#!/usr/bin/env python3
"""Empirical probe of the stack-headroom certificate producer on large
real-world corpora.

For every deployable object (creation + runtime) of each corpus contract,
this script compiles the contract through the supported raw solc spine
(`RawAst.compileArtifactFromRawSolcIr?`) and calls
`Assembly.StackHeadroom.mkCert?` (the body of
`VerifiedStackObjectArtifact.stackHeadroomCert?`) on the resulting compact
artifact, recording `some`/`none` plus a failure diagnosis for every `none`.

The corpora mirror the pinned production smokes:

* aave-pool        - Aave v3 `Pool` (linked libraries), solc 0.8.26 + 0.8.35
* poolmanager      - Uniswap v4 `PoolManager` (via-IR), solc 0.8.26
* safe             - Safe smart account `Safe` (via-IR), solc 0.8.26 + 0.8.35
* entrypoint       - ERC-4337 `EntryPoint` (via-IR, OZ remapping),
                     solc 0.8.26 + 0.8.35
* eigenlayer-bn254 - vendored `EigenLayerBN254Corpus` over the EigenLayer
                     BN254 library, solc 0.8.35

Not probed (raw-spine boundary, not certificate failures):

* Uniswap Permit2 pins `pragma solidity 0.8.17;` exactly; solc 0.8.17 emits
  no `irOptimizedAst`, so the raw path rejects it by design
  (see scripts/test_raw_solc_permit2_version_boundary.sh).
* The universal-router / Solady / OpenZeppelin bridge smokes compile small
  extracted fallback harnesses, not large deployable production objects.

Usage:
    scripts/probe_stack_headroom_corpus.sh [--corpus NAME ...] [--keep]
        [--cache-dir DIR]

Repos are shallow-cloned into the cache dir (default:
$EVM_COMPILER_CORPUS_CACHE or <outdir>/repos) and reused when present.
"""

import argparse
import copy
import importlib.util
import json
import os
import pathlib
import shutil
import subprocess
import sys
import tempfile

ROOT = pathlib.Path(__file__).resolve().parent.parent

CORPORA = {
    "aave-pool": {
        "repos": {
            "aave": (
                "https://github.com/aave/aave-v3-core.git",
                "b74526a7bc67a3a117a1963fc871b3eb8cea8435",
            ),
        },
        "source": "contracts/protocol/pool/Pool.sol",
        "source_repo": "aave",
        "contract": "Pool",
        "versions": ["0.8.26", "0.8.35"],
        "via_ir": False,
        "libraries": {
            "contracts/protocol/libraries/logic/BorrowLogic.sol:BorrowLogic":
                "0x1111111111111111111111111111111111111111",
            "contracts/protocol/libraries/logic/BridgeLogic.sol:BridgeLogic":
                "0x2222222222222222222222222222222222222222",
            "contracts/protocol/libraries/logic/EModeLogic.sol:EModeLogic":
                "0x3333333333333333333333333333333333333333",
            "contracts/protocol/libraries/logic/FlashLoanLogic.sol:FlashLoanLogic":
                "0x4444444444444444444444444444444444444444",
            "contracts/protocol/libraries/logic/LiquidationLogic.sol:LiquidationLogic":
                "0x5555555555555555555555555555555555555555",
            "contracts/protocol/libraries/logic/PoolLogic.sol:PoolLogic":
                "0x6666666666666666666666666666666666666666",
            "contracts/protocol/libraries/logic/SupplyLogic.sol:SupplyLogic":
                "0x7777777777777777777777777777777777777777",
        },
    },
    "poolmanager": {
        "repos": {
            "v4": (
                "https://github.com/Uniswap/v4-core.git",
                "46c6834698c48bc4a463a86d8420f4eb1d7f3b75",
            ),
        },
        "submodules": {"v4": ["lib/solmate"]},
        "source": "src/PoolManager.sol",
        "source_repo": "v4",
        "contract": "PoolManager",
        "versions": ["0.8.26"],
        "via_ir": True,
        "remapping_files": [("v4", "remappings.txt")],
    },
    "safe": {
        "repos": {
            "safe": (
                "https://github.com/safe-global/safe-smart-account.git",
                "bf943f80fec5ac647159d26161446ac5d716a294",
            ),
        },
        "source": "contracts/Safe.sol",
        "source_repo": "safe",
        "contract": "Safe",
        "versions": ["0.8.26", "0.8.35"],
        "via_ir": True,
    },
    "entrypoint": {
        "repos": {
            "aa": (
                "https://github.com/eth-infinitism/account-abstraction.git",
                "7af70c8993a6f42973f520ae0752386a5032abe7",
            ),
            "oz": (
                "https://github.com/OpenZeppelin/openzeppelin-contracts.git",
                "932fddf69a699a9a80fd2396fd1a2ab91cdda123",
            ),
        },
        "source": "contracts/core/EntryPoint.sol",
        "source_repo": "aa",
        "contract": "EntryPoint",
        "versions": ["0.8.26", "0.8.35"],
        "via_ir": True,
        "remapping_values": [
            ("@openzeppelin/contracts/=", "oz", "contracts/"),
        ],
    },
    "eigenlayer-bn254": {
        "repos": {
            "eigen": (
                "https://github.com/Layr-Labs/eigenlayer-contracts.git",
                "d302f65042164c8d8d0a983c1540d85a8710030b",
            ),
        },
        "source_path": "examples/EigenLayerBN254Corpus.sol",
        "contract": "EigenLayerBN254Corpus",
        "versions": ["0.8.35"],
        "via_ir": True,
        "optimizer_runs": 200,
        "remapping_values": [
            ("eigen/=", "eigen", "src/contracts/"),
        ],
    },
}

RUNNER_TEMPLATE = r"""import EvmCompiler.Solidity.RawAstPublic
import EvmCompiler.Solidity.StackHeadroomEndToEnd

/-!
Generated by scripts/probe_stack_headroom_corpus.py.  Probes
`Assembly.StackHeadroom.mkCert?` (the body of
`VerifiedStackObjectArtifact.stackHeadroomCert?`) on raw-solc-compiled
artifacts, and diagnoses failures with an instrumented mirror of the
untrusted builder loop.
-/

open EvmCompiler
open EvmCompiler.Solidity
open EvmCompiler.Assembly

structure ProbeCase where
  label : String
  rawPath : String
  source : String
  contract : String
  selector : RawAst.ObjectSelector

def probeCases : List ProbeCase :=
[
@CASES@
]

def selectionFor (case : ProbeCase) : RawAst.Selection :=
  { source? := some case.source
    contract? := some case.contract
    objectSelector := case.selector
    astOutput := "irOptimizedAst" }

def instrKind : Assembly.Instr → String
  | .label _ => "label"
  | .push _ => "push"
  | .pushLabel _ => "pushLabel"
  | .jump _ => "jump-unresolved-label"
  | .jumpi _ => "jumpi"
  | .jumpDynamic => "jumpDynamic"
  | .prim _ => "prim"

/-- Failure category of the untrusted builder. -/
inductive Diag where
  | ok (visited : Nat)
  | cap (pc : Nat) (depth : Nat) (visited : Nat)
  | stuck (pc : Nat) (kind : String) (depth : Nat) (visited : Nat)
  | fuel (visited : Nat)
  deriving Inhabited

def Diag.render : Diag → String
  | .ok visited => s!"builder-ok visited={visited}"
  | .cap pc depth visited =>
      s!"stackCap-breach pc={pc} depth={depth} visited={visited} " ++
        "(unbounded abstract stack: recursion or value-carrying growth)"
  | .stuck pc kind depth visited =>
      s!"builder-stuck pc={pc} kind={kind} depth={depth} visited={visited}"
  | .fuel visited => s!"fuel-exhausted visited={visited}"

/-- Instrumented mirror of `StackHeadroom.buildLoop`: identical traversal
order, fuel, and accept/reject behaviour (`mkStacks? = none` exactly when
this returns a non-`ok` diagnosis), but reports WHY the builder returns
`none` and how large the built table is. -/
partial def diagLoop (artifact : Compact.Artifact)
    (table : Std.HashMap Nat Compact.SourceBlock) :
    Nat → Std.HashMap Nat (List StackHeadroom.AbsStack) →
      List (Nat × StackHeadroom.AbsStack) → Nat →
      Diag × Std.HashMap Nat (List StackHeadroom.AbsStack)
  | _, acc, [], visited => (.ok visited, acc)
  | 0, acc, _, visited => (.fuel visited, acc)
  | fuel + 1, acc, (pc, astack) :: work, visited =>
      if astack.length > StackHeadroom.stackCap then
        (.cap pc astack.length visited, acc)
      else
        let known := (acc.get? pc).getD []
        if known.contains astack then
          diagLoop artifact table fuel acc work visited
        else
          let acc := acc.insert pc (astack :: known)
          match table.get? pc with
          | none => diagLoop artifact table fuel acc work (visited + 1)
          | some block =>
              match StackHeadroom.builderSuccessors artifact block astack with
              | none =>
                  (.stuck pc (instrKind block.sourceInstr) astack.length
                    visited, acc)
              | some successors =>
                  diagLoop artifact table fuel acc (successors ++ work)
                    (visited + 1)

def diagnose (artifact : Compact.Artifact) :
    Diag × Std.HashMap Nat (List StackHeadroom.AbsStack) :=
  diagLoop artifact (StackHeadroom.blockTable artifact.blocks)
    (16 * (StackHeadroom.stackCap + 1) * (artifact.blocks.length + 1) + 16)
    Std.HashMap.emptyWithCapacity [(0, [])] 0

/-- `mkCert?` validates through the bucket-indexed `checkIndexed?` (proved
equal to the flat `check?` by `checkIndexed?_eq_check?`), so full trusted
re-validation is near-linear in the table and cheap even interpreted; the
budget skip is retained only as an escape hatch.  Tune with
PROBE_CHECK_BUDGET=<Nat> (0 = never skip, the default). -/
def defaultCheckBudget : Nat := 0

def main : IO Unit := do
  let budget :=
    match (← IO.getEnv "PROBE_CHECK_BUDGET") with
    | some value => value.toNat?.getD defaultCheckBudget
    | none => defaultCheckBudget
  let stdout ← IO.getStdout
  let mut accepted := 0
  let mut rejected := 0
  let mut builderOnly := 0
  let mut compileFailed := 0
  for case in probeCases do
    let input ← IO.FS.readFile case.rawPath
    let caseStart ← IO.monoMsNow
    match RawAst.compileArtifactFromRawSolcIr? input (selectionFor case) with
    | none =>
        compileFailed := compileFailed + 1
        let caseEnd ← IO.monoMsNow
        IO.println (case.label ++ "\tCOMPILE_FAILED\tms=" ++
          toString (caseEnd - caseStart))
        stdout.flush
    | some artifact =>
        let compact := artifact.codeArtifact.compact
        let blocks := compact.blocks.length
        let (diag, built) := diagnose compact
        let entries :=
          built.toList.foldl (fun acc entry => acc + entry.2.length) 0
        let stats :=
          "\tblocks=" ++ toString blocks ++
          "\tbytes=" ++ toString artifact.image.bytes.length ++
          "\tentries=" ++ toString entries
        match diag with
        | .ok _ =>
            if budget == 0 || blocks * entries ≤ budget then
              -- The ground truth: the fail-closed certificate producer.
              match StackHeadroom.mkCert? compact with
              | some cert =>
                  accepted := accepted + 1
                  let caseEnd ← IO.monoMsNow
                  IO.println (case.label ++ "\tACCEPT" ++ stats ++
                    "\tcert_entries=" ++ toString cert.table.length ++
                    "\tms=" ++ toString (caseEnd - caseStart))
              | none =>
                  rejected := rejected + 1
                  let caseEnd ← IO.monoMsNow
                  IO.println (case.label ++ "\tREJECT" ++ stats ++
                    "\tms=" ++ toString (caseEnd - caseStart) ++
                    "\tdiag=check?-failed after " ++ diag.render)
            else
              builderOnly := builderOnly + 1
              let caseEnd ← IO.monoMsNow
              IO.println (case.label ++ "\tBUILDER_OK_CHECK_SKIPPED" ++
                stats ++ "\tms=" ++ toString (caseEnd - caseStart) ++
                "\tdiag=" ++ diag.render ++
                " (blocks*entries=" ++ toString (blocks * entries) ++
                " > budget " ++ toString budget ++
                "; interpreted check? would take hours)")
        | _ =>
            -- The diagnostic loop mirrors `buildLoop` exactly, so a
            -- non-ok diagnosis means `mkStacks?` (hence `mkCert?`)
            -- returns `none`.
            rejected := rejected + 1
            let caseEnd ← IO.monoMsNow
            IO.println (case.label ++ "\tREJECT" ++ stats ++
              "\tms=" ++ toString (caseEnd - caseStart) ++
              "\tdiag=" ++ diag.render)
        stdout.flush
  IO.println ("accepted=" ++ toString accepted ++
    " rejected=" ++ toString rejected ++
    " builder_only=" ++ toString builderOnly ++
    " compile_failed=" ++ toString compileFailed)
"""


def load_bridge():
    bridge_path = ROOT / "scripts" / "solidity_to_yul_lean.py"
    spec = importlib.util.spec_from_file_location(
        "solidity_to_yul_lean", bridge_path)
    bridge = importlib.util.module_from_spec(spec)
    assert spec.loader is not None
    sys.modules[spec.name] = bridge
    spec.loader.exec_module(bridge)
    return bridge


def checkout_repo(destination: pathlib.Path, url: str, ref: str) -> None:
    if (destination / ".git").exists():
        head = subprocess.run(
            ["git", "-C", str(destination), "rev-parse", "HEAD"],
            capture_output=True, text=True, check=True).stdout.strip()
        if head == ref:
            return
        shutil.rmtree(destination)
    destination.mkdir(parents=True, exist_ok=True)
    subprocess.run(["git", "init", "-q", str(destination)], check=True)
    subprocess.run(
        ["git", "-C", str(destination), "remote", "add", "origin", url],
        check=True)
    subprocess.run(
        ["git", "-C", str(destination), "fetch", "--depth", "1", "origin",
         ref], check=True)
    subprocess.run(
        ["git", "-C", str(destination), "-c", "advice.detachedHead=false",
         "checkout", "-q", "FETCH_HEAD"], check=True)


def solc_path(version: str) -> pathlib.Path:
    override = os.environ.get("SOLC_" + version.replace(".", ""))
    if override:
        return pathlib.Path(override)
    return (pathlib.Path.home() / ".solc-select" / "artifacts" /
            f"solc-{version}" / f"solc-{version}")


def ensure_metadata_output(request):
    outputs = request["settings"]["outputSelection"]["*"]["*"]
    if "metadata" not in outputs:
        outputs.append("metadata")


def prepare_case(name, spec, bridge, cache_dir, outdir, manifest):
    repos = {}
    for key, (url, ref) in spec.get("repos", {}).items():
        dest = cache_dir / f"{name}-{key}"
        checkout_repo(dest, url, ref)
        for sub in spec.get("submodules", {}).get(key, []):
            subprocess.run(
                ["git", "-C", str(dest), "submodule", "update", "--init",
                 "--depth", "1", sub], check=True)
        repos[key] = dest

    if "source_path" in spec:
        source_path = ROOT / spec["source_path"]
        source_name = source_path.name
    else:
        source_path = repos[spec["source_repo"]] / spec["source"]
        source_name = spec["source"]
    source_content = source_path.read_text()

    remapping_values = [
        prefix + str(repos[repo_key] / suffix) + "/"
        for prefix, repo_key, suffix in spec.get("remapping_values", [])
    ]
    remapping_files = [
        repos[repo_key] / rel
        for repo_key, rel in spec.get("remapping_files", [])
    ]
    remappings = bridge.read_import_remappings(
        remapping_values, remapping_files)
    included = bridge.collect_local_import_sources(
        source_name, source_content, source_path, {}, remappings)
    include_sources = {
        key: source.content for key, source in included.items()}

    for version in spec["versions"]:
        solc = solc_path(version)
        if not solc.exists():
            print(f"warning: skipping {name}@{version}: missing {solc}",
                  file=sys.stderr)
            continue
        request = bridge.standard_json_input(
            source_name,
            source_content,
            via_ir=spec.get("via_ir", True),
            optimized=True,
            experimental=True,
            include_sources=include_sources,
            require_bytecode=True,
            optimizer_runs=spec.get("optimizer_runs"),
            evm_version="cancun",
        )
        if "libraries" in spec:
            libraries = {}
            for qualified, address in spec["libraries"].items():
                lib_source, lib_contract = qualified.rsplit(":", 1)
                libraries.setdefault(lib_source, {})[lib_contract] = address
            request["settings"]["libraries"] = copy.deepcopy(libraries)
        ensure_metadata_output(request)
        try:
            raw_output = bridge.run_solc(str(solc), copy.deepcopy(request), ())
        except bridge.ConversionError as exc:
            # Safe-style corpora: solc's own bytecode backend rejects the
            # program (stack too deep), but irOptimizedAst is still emitted
            # when bytecode is not required; our raw spine compiles from
            # the AST.
            message = str(exc)
            if ("too deep in the stack" not in message
                    and "YulException" not in message):
                raise
            retry = bridge.standard_json_input(
                source_name,
                source_content,
                via_ir=spec.get("via_ir", True),
                optimized=True,
                experimental=True,
                include_sources=include_sources,
                require_bytecode=False,
                optimizer_runs=spec.get("optimizer_runs"),
                evm_version="cancun",
            )
            if "libraries" in request["settings"]:
                retry["settings"]["libraries"] = copy.deepcopy(
                    request["settings"]["libraries"])
            ensure_metadata_output(retry)
            raw_output = bridge.run_solc(str(solc), copy.deepcopy(retry), ())
        contract_output = (
            raw_output.get("contracts", {})
            .get(source_name, {})
            .get(spec["contract"], {}))
        ast = contract_output.get("irOptimizedAst")
        if not isinstance(ast, dict) or ast.get("nodeType") != "YulObject":
            print(f"warning: {name}@{version} emitted no YulObject "
                  "irOptimizedAst; skipping", file=sys.stderr)
            continue
        raw_path = outdir / f"{name}-{version}.standard-output.json"
        raw_path.write_text(json.dumps(raw_output, separators=(",", ":")))
        for selector in ("runtime", "creation"):
            manifest.append({
                "label": f"{name}-{version}-{selector}",
                "raw": str(raw_path),
                "source": source_name,
                "contract": spec["contract"],
                "selector": selector,
            })


def write_runner(outdir, manifest) -> pathlib.Path:
    entries = []
    for case in manifest:
        selector = ("RawAst.ObjectSelector.creation"
                    if case["selector"] == "creation"
                    else "RawAst.ObjectSelector.runtime")
        entries.append(
            "  { label := %s, rawPath := %s, source := %s, "
            "contract := %s, selector := %s }" % (
                json.dumps(case["label"]),
                json.dumps(case["raw"]),
                json.dumps(case["source"]),
                json.dumps(case["contract"]),
                selector,
            ))
    runner_path = outdir / "probe_stack_headroom.lean"
    runner_path.write_text(
        RUNNER_TEMPLATE.replace("@CASES@", ",\n".join(entries)))
    return runner_path


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--corpus", action="append",
                        choices=sorted(CORPORA.keys()),
                        help="probe only the named corpora (repeatable)")
    parser.add_argument("--outdir", type=pathlib.Path, default=None)
    parser.add_argument("--cache-dir", type=pathlib.Path, default=None)
    parser.add_argument("--lake", default=os.environ.get(
        "LAKE", str(pathlib.Path.home() / ".elan" / "bin" / "lake")))
    parser.add_argument("--keep", action="store_true",
                        help="keep the outdir on exit")
    parser.add_argument("--generate-only", action="store_true",
                        help="write raw outputs + runner, do not run lean")
    parser.add_argument("--per-case", action="store_true",
                        help="run one lean process per probe case so a "
                             "single interpreter crash cannot abort the "
                             "rest of the table")
    args = parser.parse_args()

    bridge = load_bridge()
    outdir = args.outdir or pathlib.Path(
        tempfile.mkdtemp(prefix="evm-compiler-stack-headroom-probe."))
    outdir.mkdir(parents=True, exist_ok=True)
    cache_env = os.environ.get("EVM_COMPILER_CORPUS_CACHE")
    cache_dir = (args.cache_dir or
                 (pathlib.Path(cache_env) if cache_env else outdir / "repos"))
    cache_dir.mkdir(parents=True, exist_ok=True)

    names = args.corpus or sorted(CORPORA.keys())
    manifest = []
    for name in names:
        prepare_case(name, CORPORA[name], bridge, cache_dir, outdir, manifest)

    if not manifest:
        print("error: no probe cases prepared", file=sys.stderr)
        return 1
    (outdir / "manifest.json").write_text(json.dumps(manifest, indent=1))
    runner_path = write_runner(outdir, manifest)
    print(f"outdir={outdir}")
    print(f"runner={runner_path}")
    print(f"cases={len(manifest)}")
    if args.generate_only:
        return 0

    def run_lean(path):
        # `ulimit -s`: the raw frontend's typed-CFG certificate collector
        # recurses per block; the interpreter needs a large stack for the
        # big corpora (Aave Pool).
        return subprocess.run(
            ["/bin/sh", "-c",
             'ulimit -s 65520 2>/dev/null; exec "$0" env lean --run "$1"',
             args.lake, str(path)],
            cwd=ROOT, text=True, capture_output=True)

    if args.per_case:
        exit_code = 0
        for index, case in enumerate(manifest):
            single = write_runner(outdir, [case])
            single_named = outdir / f"probe_case_{index}.lean"
            single.rename(single_named)
            result = run_lean(single_named)
            if result.returncode != 0:
                exit_code = 1
                sys.stdout.write(
                    f"{case['label']}\tLEAN_CRASHED\n")
                sys.stderr.write(result.stdout + result.stderr)
            else:
                for line in result.stdout.splitlines():
                    if not line.startswith(("accepted=",)):
                        sys.stdout.write(line + "\n")
            sys.stdout.flush()
        write_runner(outdir, manifest)
        if not args.keep and args.outdir is None and exit_code == 0:
            shutil.rmtree(outdir, ignore_errors=True)
        return exit_code

    result = run_lean(runner_path)
    sys.stdout.write(result.stdout)
    sys.stderr.write(result.stderr)
    if not args.keep and args.outdir is None and result.returncode == 0:
        shutil.rmtree(outdir, ignore_errors=True)
    return result.returncode


if __name__ == "__main__":
    raise SystemExit(main())
