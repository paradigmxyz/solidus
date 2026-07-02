#!/usr/bin/env python3
from __future__ import annotations

import argparse
import ast
import bisect
import hashlib
import json
import random
import re
from pathlib import Path
from typing import Any, Iterable


LEAN_DECL_RE = re.compile(r"^(theorem|lemma|def|abbrev)\s+([^\s:{]+)", re.M)
LEAN_BOUNDARY_RE = re.compile(
    r"^(theorem|lemma|def|abbrev|instance|structure|inductive|class|namespace|section|end)\b",
    re.M,
)


def sha256_text(text: str) -> str:
    return hashlib.sha256(text.encode("utf-8")).hexdigest()


def line_starts(text: str) -> list[int]:
    starts = [0]
    for index, char in enumerate(text):
        if char == "\n":
            starts.append(index + 1)
    return starts


def line_start(starts: list[int], line: int) -> int:
    if line <= 1:
        return 0
    if line - 1 >= len(starts):
        return len(starts)
    return starts[line - 1]


def line_end(starts: list[int], text: str, line: int) -> int:
    if line < len(starts):
        return starts[line]
    return len(text)


def line_number(starts: list[int], offset: int) -> int:
    return bisect.bisect_right(starts, offset)


def truncate_left(text: str, max_chars: int) -> str:
    if max_chars <= 0 or len(text) <= max_chars:
        return text
    return text[-max_chars:]


def body_line_count(text: str) -> int:
    stripped = text.rstrip("\n")
    if not stripped:
        return 0
    return stripped.count("\n") + 1


def leading_python_imports(text: str) -> str:
    imports: list[str] = []
    for line in text.splitlines(keepends=True):
        stripped = line.strip()
        if stripped.startswith("import ") or stripped.startswith("from "):
            imports.append(line)
    return "".join(imports)


def class_header(text: str, starts: list[int], node: ast.ClassDef) -> str:
    first_line = min([node.lineno, *[decorator.lineno for decorator in node.decorator_list]])
    start = line_start(starts, first_line)
    if node.body:
        end = line_start(starts, node.body[0].lineno)
    else:
        end = line_end(starts, text, node.end_lineno or node.lineno)
    return text[start:end]


def function_start_line(node: ast.FunctionDef | ast.AsyncFunctionDef) -> int:
    lines = [node.lineno, *[decorator.lineno for decorator in node.decorator_list]]
    return min(lines)


def is_python_stub(node: ast.FunctionDef | ast.AsyncFunctionDef) -> bool:
    meaningful = [
        stmt
        for stmt in node.body
        if not (isinstance(stmt, ast.Expr) and isinstance(stmt.value, ast.Constant) and isinstance(stmt.value.value, str))
    ]
    if not meaningful:
        return True
    if len(meaningful) == 1:
        stmt = meaningful[0]
        if isinstance(stmt, ast.Pass):
            return True
        if isinstance(stmt, ast.Expr) and isinstance(stmt.value, ast.Constant) and stmt.value.value is Ellipsis:
            return True
        if isinstance(stmt, ast.Raise) and isinstance(stmt.exc, ast.Call):
            func = stmt.exc.func
            if isinstance(func, ast.Name) and func.id == "NotImplementedError":
                return True
    return False


def iter_python_functions(tree: ast.Module) -> Iterable[tuple[ast.FunctionDef | ast.AsyncFunctionDef, tuple[ast.ClassDef, ...]]]:
    def visit_body(
        body: list[ast.stmt],
        class_stack: tuple[ast.ClassDef, ...],
    ) -> Iterable[tuple[ast.FunctionDef | ast.AsyncFunctionDef, tuple[ast.ClassDef, ...]]]:
        for stmt in body:
            if isinstance(stmt, ast.ClassDef):
                yield from visit_body(stmt.body, (*class_stack, stmt))
            elif isinstance(stmt, (ast.FunctionDef, ast.AsyncFunctionDef)):
                yield stmt, class_stack

    yield from visit_body(tree.body, ())


def collect_python_targets(
    python_root: Path,
    min_lines: int,
    max_lines: int,
    max_context_chars: int,
) -> list[dict[str, Any]]:
    package_root = python_root / "py_yul_compiler"
    targets: list[dict[str, Any]] = []
    for path in sorted(package_root.glob("*.py")):
        if path.name == "__init__.py":
            continue
        text = path.read_text()
        starts = line_starts(text)
        try:
            tree = ast.parse(text, filename=str(path))
        except SyntaxError:
            continue
        imports = leading_python_imports(text)
        source_hash = sha256_text(text)
        for node, classes in iter_python_functions(tree):
            if not node.body or is_python_stub(node):
                continue
            first_body_line = node.body[0].lineno
            body_start = line_start(starts, first_body_line)
            body_end = line_end(starts, text, node.end_lineno or first_body_line)
            target_text = text[body_start:body_end]
            lines = body_line_count(target_text)
            if lines < min_lines or lines > max_lines:
                continue

            start_line = function_start_line(node)
            decl_start = line_start(starts, start_line)
            function_header = text[decl_start:body_start]
            class_headers = "".join(class_header(text, starts, cls) for cls in classes)
            qualified_name = ".".join([*[cls.name for cls in classes], node.name])
            relative_path = str(path.relative_to(python_root))
            target_id = f"python:{relative_path}:{qualified_name}:{node.lineno}"
            header = f"{class_headers}{function_header}"
            imports_header = f"{imports}\n{header}" if imports else header
            targets.append(
                {
                    "id": target_id,
                    "language": "python",
                    "kind": "function",
                    "name": qualified_name,
                    "path": relative_path,
                    "start_line": first_body_line,
                    "end_line": node.end_lineno,
                    "body_lines": lines,
                    "target_bytes": len(target_text.encode("utf-8")),
                    "source_sha256": source_hash,
                    "target": target_text,
                    "contexts": {
                        "header": header,
                        "imports_header": imports_header,
                        "file_prefix_8k": truncate_left(text[:body_start], 8_000),
                        "file_prefix_32k": truncate_left(text[:body_start], 32_000),
                        "file_prefix": truncate_left(text[:body_start], max_context_chars),
                    },
                }
            )
    return targets


def lean_imports(text: str) -> str:
    return "".join(line for line in text.splitlines(keepends=True) if line.startswith("import "))


def collect_lean_targets(
    lean_root: Path,
    min_lines: int,
    max_lines: int,
    max_context_chars: int,
) -> list[dict[str, Any]]:
    targets: list[dict[str, Any]] = []
    files = sorted((lean_root / "EvmCompiler").rglob("*.lean"))
    for path in files:
        text = path.read_text()
        starts = line_starts(text)
        source_hash = sha256_text(text)
        imports = lean_imports(text)
        boundaries = sorted({match.start() for match in LEAN_BOUNDARY_RE.finditer(text)} | {len(text)})
        for match in LEAN_DECL_RE.finditer(text):
            decl_start = match.start()
            next_boundary = next((boundary for boundary in boundaries if boundary > decl_start), len(text))
            decl_text = text[decl_start:next_boundary]
            assign_index = decl_text.find(":=")
            if assign_index < 0:
                continue
            body_start = decl_start + assign_index + 2
            raw_target = text[body_start:next_boundary]
            target_text = raw_target.rstrip() + "\n"
            lines = body_line_count(target_text)
            if lines < min_lines or lines > max_lines:
                continue
            kind = match.group(1)
            name = match.group(2)
            relative_path = str(path.relative_to(lean_root))
            start_line = line_number(starts, body_start)
            end_line = line_number(starts, next_boundary)
            header = text[decl_start:body_start]
            target_id = f"lean:{relative_path}:{name}:{start_line}"
            targets.append(
                {
                    "id": target_id,
                    "language": "lean",
                    "kind": kind,
                    "name": name,
                    "path": relative_path,
                    "start_line": start_line,
                    "end_line": end_line,
                    "body_lines": lines,
                    "target_bytes": len(target_text.encode("utf-8")),
                    "source_sha256": source_hash,
                    "target": target_text,
                    "contexts": {
                        "header": header,
                        "imports_header": f"{imports}\n{header}" if imports else header,
                        "file_prefix_8k": truncate_left(text[:body_start], 8_000),
                        "file_prefix_32k": truncate_left(text[:body_start], 32_000),
                        "file_prefix": truncate_left(text[:body_start], max_context_chars),
                    },
                }
            )
    return targets


def sample_targets(targets: list[dict[str, Any]], count: int, seed: int) -> list[dict[str, Any]]:
    if count <= 0 or len(targets) <= count:
        return targets
    rng = random.Random(seed)
    selected = targets[:]
    rng.shuffle(selected)
    return sorted(selected[:count], key=lambda row: row["id"])


def interleave(left: list[dict[str, Any]], right: list[dict[str, Any]]) -> list[dict[str, Any]]:
    rows: list[dict[str, Any]] = []
    for index in range(max(len(left), len(right))):
        if index < len(left):
            rows.append(left[index])
        if index < len(right):
            rows.append(right[index])
    return rows


def write_jsonl(path: Path, rows: Iterable[dict[str, Any]]) -> None:
    with path.open("w") as handle:
        for row in rows:
            handle.write(json.dumps(row, ensure_ascii=False, sort_keys=True))
            handle.write("\n")


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--lean-root", type=Path, default=Path("."))
    parser.add_argument("--python-root", type=Path, default=Path("../python-yul"))
    parser.add_argument("--output", type=Path, default=Path("/tmp/yul_bpb_targets.jsonl"))
    parser.add_argument("--per-language", type=int, default=60)
    parser.add_argument("--min-lines", type=int, default=8)
    parser.add_argument("--max-lines", type=int, default=90)
    parser.add_argument("--max-context-chars", type=int, default=120_000)
    parser.add_argument("--seed", type=int, default=0)
    args = parser.parse_args()

    lean_targets = collect_lean_targets(
        args.lean_root.resolve(),
        args.min_lines,
        args.max_lines,
        args.max_context_chars,
    )
    python_targets = collect_python_targets(
        args.python_root.resolve(),
        args.min_lines,
        args.max_lines,
        args.max_context_chars,
    )
    sampled = interleave(
        sample_targets(lean_targets, args.per_language, args.seed),
        sample_targets(python_targets, args.per_language, args.seed),
    )
    args.output.parent.mkdir(parents=True, exist_ok=True)
    write_jsonl(args.output, sampled)
    print(
        f"wrote {len(sampled)} targets to {args.output} "
        f"(lean available={len(lean_targets)}, python available={len(python_targets)})"
    )


if __name__ == "__main__":
    main()
