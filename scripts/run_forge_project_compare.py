#!/usr/bin/env python3
"""Run a Foundry project through full solc and the solc-lean wrapper.

This is the project-level harness for treating the current compiler as a
near drop-in solc replacement in real Forge test suites.  It prepares either a
local checkout or a shallow clone, runs optional setup commands, delegates the
actual two-compiler comparison to `compare_forge_solc_lean.sh`, and writes a
machine-readable report with logs and bridge-summary diagnostics.
"""

from __future__ import annotations

import argparse
import datetime as _datetime
import json
import os
import re
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path
from typing import Any, Sequence


REPORT_SCHEMA = "evm-compiler.forge-project-compare.v1"


def repo_root() -> Path:
    return Path(__file__).resolve().parent.parent


def default_lake() -> str:
    local_lake = Path.home() / ".elan" / "bin" / "lake"
    if local_lake.exists():
        return str(local_lake)
    return "lake"


def default_solc() -> str:
    local_solc = Path.home() / ".local" / "bin" / "solc"
    if local_solc.exists():
        return str(local_solc)
    return "solc"


def safe_name(value: str) -> str:
    cleaned = re.sub(r"[^A-Za-z0-9._-]+", "-", value).strip(".-")
    return cleaned or "forge-project"


def timestamp() -> str:
    return _datetime.datetime.now(_datetime.UTC).strftime("%Y%m%dT%H%M%SZ")


def default_out_dir(name: str) -> Path:
    base = Path(os.environ.get("TMPDIR", tempfile.gettempdir()))
    return base / f"evm-compiler-forge-project-{safe_name(name)}-{timestamp()}"


def run_logged(
    command: Sequence[str],
    cwd: Path,
    env: dict[str, str],
    stdout_path: Path,
    stderr_path: Path,
) -> int:
    with stdout_path.open("w", encoding="utf-8") as stdout, stderr_path.open(
        "w",
        encoding="utf-8",
    ) as stderr:
        completed = subprocess.run(
            list(command),
            cwd=cwd,
            env=env,
            text=True,
            stdout=stdout,
            stderr=stderr,
            check=False,
        )
    return completed.returncode


def run_shell_logged(
    command: str,
    cwd: Path,
    env: dict[str, str],
    stdout_path: Path,
    stderr_path: Path,
) -> int:
    with stdout_path.open("w", encoding="utf-8") as stdout, stderr_path.open(
        "w",
        encoding="utf-8",
    ) as stderr:
        completed = subprocess.run(
            command,
            cwd=cwd,
            env=env,
            text=True,
            shell=True,
            stdout=stdout,
            stderr=stderr,
            check=False,
        )
    return completed.returncode


def read_text(path: Path) -> str:
    try:
        return path.read_text(encoding="utf-8", errors="replace")
    except FileNotFoundError:
        return ""


def parse_key_values(text: str) -> dict[str, str]:
    result: dict[str, str] = {}
    for raw_line in text.splitlines():
        line = raw_line.strip()
        if not re.match(r"^[A-Za-z0-9_.-]+=", line):
            continue
        key, value = line.split("=", 1)
        result[key] = value
    return result


def git_head(path: Path) -> str | None:
    completed = subprocess.run(
        ["git", "-C", str(path), "rev-parse", "HEAD"],
        text=True,
        capture_output=True,
        check=False,
    )
    if completed.returncode != 0:
        return None
    return completed.stdout.strip() or None


def prepare_project(args: argparse.Namespace, out_dir: Path) -> tuple[Path, list[dict[str, Any]]]:
    commands: list[dict[str, Any]] = []
    if args.project_dir is not None:
        return args.project_dir.resolve(), commands
    if args.repo is None:
        raise ValueError("provide either --project-dir or --repo")

    project_dir = out_dir / "checkout"
    if args.ref:
        project_dir.mkdir(parents=True, exist_ok=True)
        init_log = out_dir / "git-init.stdout"
        init_err = out_dir / "git-init.stderr"
        status = run_logged(["git", "init", "-q", str(project_dir)], out_dir, os.environ.copy(), init_log, init_err)
        commands.append({"name": "git-init", "status": status, "stdout": str(init_log), "stderr": str(init_err)})
        if status != 0:
            return project_dir, commands
        remote_log = out_dir / "git-remote.stdout"
        remote_err = out_dir / "git-remote.stderr"
        status = run_logged(["git", "-C", str(project_dir), "remote", "add", "origin", args.repo], out_dir, os.environ.copy(), remote_log, remote_err)
        commands.append({"name": "git-remote-add", "status": status, "stdout": str(remote_log), "stderr": str(remote_err)})
        if status != 0:
            return project_dir, commands
        fetch_log = out_dir / "git-fetch.stdout"
        fetch_err = out_dir / "git-fetch.stderr"
        status = run_logged(["git", "-C", str(project_dir), "fetch", "--depth", "1", "origin", args.ref], out_dir, os.environ.copy(), fetch_log, fetch_err)
        commands.append({"name": "git-fetch", "status": status, "stdout": str(fetch_log), "stderr": str(fetch_err)})
        if status != 0:
            return project_dir, commands
        checkout_log = out_dir / "git-checkout.stdout"
        checkout_err = out_dir / "git-checkout.stderr"
        status = run_logged(["git", "-C", str(project_dir), "-c", "advice.detachedHead=false", "checkout", "-q", "FETCH_HEAD"], out_dir, os.environ.copy(), checkout_log, checkout_err)
        commands.append({"name": "git-checkout", "status": status, "stdout": str(checkout_log), "stderr": str(checkout_err)})
        return project_dir, commands

    clone_log = out_dir / "git-clone.stdout"
    clone_err = out_dir / "git-clone.stderr"
    status = run_logged(["git", "clone", "--depth", "1", args.repo, str(project_dir)], out_dir, os.environ.copy(), clone_log, clone_err)
    commands.append({"name": "git-clone", "status": status, "stdout": str(clone_log), "stderr": str(clone_err)})
    return project_dir, commands


def compare_args(args: argparse.Namespace) -> list[str]:
    result: list[str] = []
    for value in args.match_test:
        result.extend(["--match-test", value])
    for value in args.match_contract:
        result.extend(["--match-contract", value])
    for value in args.match_path:
        result.extend(["--match-path", value])
    extra = list(args.forge_args)
    if extra and extra[0] == "--":
        extra = extra[1:]
    result.extend(extra)
    return result


def write_report(path: Path, report: dict[str, Any]) -> None:
    path.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")


def build_arg_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    source = parser.add_mutually_exclusive_group(required=True)
    source.add_argument("--project-dir", type=Path)
    source.add_argument("--repo")
    parser.add_argument("--ref", help="Git ref to fetch when --repo is used")
    parser.add_argument("--name", help="Short report name")
    parser.add_argument("--out-dir", type=Path)
    parser.add_argument("--setup-command", action="append", default=[])
    parser.add_argument("--submodule", action="append", default=[])
    parser.add_argument("--match-test", action="append", default=[])
    parser.add_argument("--match-contract", action="append", default=[])
    parser.add_argument("--match-path", action="append", default=[])
    parser.add_argument("--solc", default=os.environ.get("SOLC", default_solc()))
    parser.add_argument("--lake", default=os.environ.get("LAKE", default_lake()))
    parser.add_argument("--forge", default=os.environ.get("FORGE", "forge"))
    parser.add_argument("--python", default=os.environ.get("PYTHON", sys.executable))
    parser.add_argument("--solc-version", help="Set SOLC_VERSION for both runs")
    parser.add_argument("--optimized", action="store_true")
    parser.add_argument(
        "--compare-script",
        type=Path,
        default=repo_root() / "scripts" / "compare_forge_solc_lean.sh",
    )
    parser.add_argument(
        "forge_args",
        nargs=argparse.REMAINDER,
        help="Additional forge test args after --",
    )
    return parser


def main(argv: Sequence[str] | None = None) -> int:
    parser = build_arg_parser()
    args = parser.parse_args(argv)
    name = args.name
    if name is None:
        name = Path(args.project_dir).name if args.project_dir else Path(args.repo).stem
    out_dir = (args.out_dir or default_out_dir(name)).resolve()
    out_dir.mkdir(parents=True, exist_ok=True)

    report_path = out_dir / "report.json"
    report: dict[str, Any] = {
        "schema": REPORT_SCHEMA,
        "name": name,
        "outDir": str(out_dir),
        "status": "preparing",
        "project": {
            "repo": args.repo,
            "requestedRef": args.ref,
        },
        "commands": [],
    }

    try:
        project_dir, prep_commands = prepare_project(args, out_dir)
    except ValueError as exc:
        parser.error(str(exc))
    report["commands"].extend(prep_commands)
    report["project"]["path"] = str(project_dir)
    report["project"]["actualRef"] = git_head(project_dir)
    if any(command["status"] != 0 for command in prep_commands):
        report["status"] = "prepare-failed"
        write_report(report_path, report)
        print(f"forge_project_compare=prepare-failed")
        print(f"report={report_path}")
        return 1

    env = os.environ.copy()
    env.update(
        {
            "SOLC": args.solc,
            "LAKE": args.lake,
            "FORGE": args.forge,
            "PYTHON": args.python,
        }
    )
    if args.solc_version:
        env["SOLC_VERSION"] = args.solc_version
    # --optimized no longer needs SOLC_LEAN_OPTIMIZED: the raw-path wrapper
    # always consumes irOptimizedAst, and optimizer settings come from the
    # project's own Foundry configuration.

    for index, submodule in enumerate(args.submodule, start=1):
        stdout = out_dir / f"submodule-{index}.stdout"
        stderr = out_dir / f"submodule-{index}.stderr"
        command = ["git", "submodule", "update", "--init", "--depth", "1", submodule]
        status = run_logged(command, project_dir, env, stdout, stderr)
        report["commands"].append(
            {
                "name": f"submodule-{index}",
                "command": command,
                "status": status,
                "stdout": str(stdout),
                "stderr": str(stderr),
            }
        )
        if status != 0:
            report["status"] = "setup-failed"
            write_report(report_path, report)
            print("forge_project_compare=setup-failed")
            print(f"report={report_path}")
            return 1

    for index, setup in enumerate(args.setup_command, start=1):
        stdout = out_dir / f"setup-{index}.stdout"
        stderr = out_dir / f"setup-{index}.stderr"
        status = run_shell_logged(setup, project_dir, env, stdout, stderr)
        report["commands"].append(
            {
                "name": f"setup-{index}",
                "command": setup,
                "status": status,
                "stdout": str(stdout),
                "stderr": str(stderr),
            }
        )
        if status != 0:
            report["status"] = "setup-failed"
            write_report(report_path, report)
            print("forge_project_compare=setup-failed")
            print(f"report={report_path}")
            return 1

    stdout = out_dir / "compare.stdout"
    stderr = out_dir / "compare.stderr"
    command = [str(args.compare_script.resolve()), *compare_args(args)]
    status = run_logged(command, project_dir, env, stdout, stderr)
    stdout_text = read_text(stdout)
    key_values = parse_key_values(stdout_text)
    compare_status = key_values.get("forge_compare", "unknown")
    report["commands"].append(
        {
            "name": "compare",
            "command": command,
            "status": status,
            "stdout": str(stdout),
            "stderr": str(stderr),
        }
    )
    report["compare"] = {
        "status": compare_status,
        "returncode": status,
        "keyValues": key_values,
    }
    report["status"] = "pass" if status == 0 and compare_status == "pass" else "fail"
    write_report(report_path, report)

    print(f"forge_project_compare={report['status']}")
    print(f"compare_status={compare_status}")
    print(f"compare_returncode={status}")
    print(f"project_dir={project_dir}")
    print(f"out_dir={out_dir}")
    print(f"report={report_path}")
    for key in [
        "bridge_json_backend_compatibility",
        "bridge_json_summary_unsupported_primitives",
        "bridge_json_summary_object_builtins",
        "bridge_json_summary_dialect_builtins",
        "bridge_json_summary_objects",
        "bridge_json_summary_skipped_contracts",
    ]:
        if key in key_values:
            print(f"{key}={key_values[key]}")
    return status


if __name__ == "__main__":
    raise SystemExit(main())
