#!/usr/bin/env python3
"""Profile one public-corpus execution vector with Foundry debugger steps.

This tool deliberately lives outside the frozen arena harness.  It reuses the
same compiler path, vector files, EVM revision, deployment behavior, and gas
budget, but keeps the generated Forge project and emits a debugger-step dump
that can be aggregated without changing scored inputs.
"""

from __future__ import annotations

import argparse
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
from typing import Any


REPO_ROOT = Path(__file__).resolve().parents[1]
SCRIPTS = REPO_ROOT / "scripts"
sys.path.insert(0, str(SCRIPTS))

import opt_gas_runner as gas  # noqa: E402
import opt_harness as harness  # noqa: E402


def profile_env() -> dict[str, str]:
    env = os.environ.copy()
    env.setdefault("SOLC", harness.default_solc())
    env.setdefault("FORGE", harness.default_forge())
    env.setdefault("LAKE", shutil.which("lake") or "lake")
    return env


def foundry_config() -> str:
    return "\n".join(
        [
            "[profile.default]",
            'src = "src"',
            'test = "test"',
            'out = "out"',
            'cache_path = "cache"',
            f'evm_version = "{gas.FORGE_EVM_VERSION}"',
            f"code_size_limit = {gas.CODE_SIZE_LIMIT}",
            'fs_permissions = [{ access = "read-write", path = "./" }]',
            "",
        ]
    )


def select_contract(
    compiled: dict[str, Any], contract_name: str
) -> dict[str, Any]:
    suffix = f":{contract_name}"
    matches = [
        contract
        for contract in compiled["contracts"]
        if contract["name"].endswith(suffix)
    ]
    if len(matches) != 1:
        available = ", ".join(c["name"] for c in compiled["contracts"])
        raise SystemExit(
            f"expected one contract named {contract_name!r}; "
            f"found {len(matches)} (available: {available})"
        )
    return matches[0]


def prepare_project(
    output_dir: Path,
    contract: dict[str, Any],
    vector_spec: dict[str, Any],
    vector_index: int,
) -> Path:
    vectors = vector_spec.get("vectors") or []
    if vector_index < 0 or vector_index >= len(vectors):
        raise SystemExit(
            f"vector index {vector_index} is outside 0..{len(vectors) - 1}"
        )

    project = output_dir / "forge"
    (project / "src").mkdir(parents=True, exist_ok=True)
    (project / "test").mkdir(parents=True, exist_ok=True)
    (project / "foundry.toml").write_text(foundry_config())
    rendered = gas.render_gas_harness(
        contract["runtime_hex"],
        contract["creation_hex"],
        vector_spec.get("deploy") or {},
        [vectors[vector_index]],
        "gas.out",
    )
    (project / "test" / "GasRunner.t.sol").write_text(rendered)
    return project


def run_profile(
    project: Path, output_dir: Path, env: dict[str, str]
) -> Path:
    dump_path = output_dir / "debug-steps.json"
    command = [
        env["FORGE"],
        "test",
        "--root",
        str(project),
        "--use",
        env["SOLC"],
        "--offline",
        "--match-contract",
        "GasRunner",
        "--match-test",
        "test_gas",
        "--debug",
        "--dump",
        str(dump_path),
    ]
    proc = subprocess.run(
        command,
        cwd=REPO_ROOT,
        env=env,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        check=False,
    )
    (output_dir / "forge.stdout").write_text(proc.stdout)
    (output_dir / "forge.stderr").write_text(proc.stderr)
    if proc.returncode != 0:
        details = "\n".join(
            part for part in (proc.stdout.strip(), proc.stderr.strip()) if part
        )
        raise SystemExit(f"forge profile failed:\n{details[-4000:]}")
    if not dump_path.exists():
        raise SystemExit("forge succeeded but did not write the debugger dump")
    return dump_path


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("source", help="path relative to the repository root")
    parser.add_argument("contract", help="contract name within the source")
    parser.add_argument(
        "--vector-index", type=int, default=0, help="zero-based vector index"
    )
    parser.add_argument(
        "--output-dir",
        type=Path,
        default=Path("/tmp/solidus-gas-profile"),
    )
    args = parser.parse_args()

    env = profile_env()
    compiled = harness.compile_source(args.source, env)
    if not compiled["ok"]:
        raise SystemExit(f"compile failed: {compiled['reason']}")
    contract = select_contract(compiled, args.contract)
    vector_spec = gas.load_vectors(contract["name"])

    args.output_dir.mkdir(parents=True, exist_ok=True)
    project = prepare_project(
        args.output_dir, contract, vector_spec, args.vector_index
    )
    dump_path = run_profile(project, args.output_dir, env)
    manifest = {
        "source": args.source,
        "contract": contract["name"],
        "vector_index": args.vector_index,
        "vector": vector_spec["vectors"][args.vector_index],
        "runtime_bytes": contract["runtime_bytes"],
        "creation_bytes": contract["creation_bytes"],
        "dump": str(dump_path),
    }
    (args.output_dir / "profile.json").write_text(
        json.dumps(manifest, indent=2) + "\n"
    )
    print(dump_path)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
