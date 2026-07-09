#!/usr/bin/env python3
"""Repo-local OpenAI Responses API oracle helper.

The script is intentionally standard-library only.  It can submit a hand-written
context file, poll prior responses, and build a compact architecture-review
packet for this compiler repo without dumping huge Lean build logs into the
conversation.
"""

from __future__ import annotations

import argparse
import datetime as _dt
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import textwrap
from typing import Any
import urllib.error
import urllib.request


API_BASE = os.environ.get("OPENAI_API_BASE", "https://api.openai.com/v1")
DEFAULT_MODEL = os.environ.get("ORACLE_MODEL", "gpt-5.5-pro")
DEFAULT_EFFORT = os.environ.get("ORACLE_EFFORT", "xhigh")
DEFAULT_MAX_OUTPUT_TOKENS = int(os.environ.get("ORACLE_MAX_OUTPUT_TOKENS", "128000"))
TERMINAL_STATUSES = {"completed", "failed", "cancelled", "canceled", "incomplete"}

ARCHITECTURE_TITLE = "evm-compiler architecture review"
SYSTEM_PROMPT = """\
You are Oracle, a GPT Pro consultant for hard Lean theorem proving and
verified-compiler architecture. Give direct, critical, implementation-oriented
advice. Prefer compositional proof designs, small theorem statements, and
architecture corrections over heroic local tactic scripts. If you mention Lean
declaration names you are not certain exist, mark them as uncertain. Do not
pretend you have checked the repository. Separate confident conclusions from
speculation, and include a concrete next-step plan.
"""

ARCHITECTURE_REVIEW_PROMPT = """\
Please review the architecture of this Lean verified-compiler project. Focus on
whether the compiler tower has the right abstraction boundaries, whether the
current recursive Yul bridge proof is stated at the right level, and whether
there is a simpler compositional theorem structure we should use.

Important constraints:
- Do not suggest adding axioms, sorries, or proof assumptions that can be
  discharged locally.
- Treat oracle advice as design guidance only; all Lean claims must later be
  checked in the repo.
- Keep advice general to verified compiler architecture unless a concrete Lean
  interface is clearly implicated by the context below.
- Avoid asking us to paste giant build logs. If a local proof is hard, propose a
  smaller theorem boundary or invariant.
"""

DEFAULT_ARCHITECTURE_FILES = [
    "ROADMAP.md",
    "PROGRESS_LOG.md",
    "EvmCompiler/Solidity/RawAstPublic.lean",
    "EvmCompiler/Verification.lean",
    "../evm-interaction/EvmCompiler/Simulation/Outcome.lean",
    "EvmCompiler/Locals/Allocation.lean",
    "EvmCompiler/TypedCfg/Preservation.lean",
    "EvmCompiler/Yul/ObserverOracle.lean",
]

DECLARATION_PATTERNS = [
    r"\bstructure\s+OutcomeContract\b",
    r"\bstructure\s+ProgramPlan\b",
    r"\bstructure\s+ProgramCert\b",
    r"\btheorem\s+compileCertified\?_step_eventually\b",
    r"\btheorem\s+compileArtifactWithPolicy\?_valid\b",
]


def utc_now() -> str:
    return _dt.datetime.now(_dt.timezone.utc).isoformat(timespec="seconds")


def local_timestamp() -> str:
    return _dt.datetime.now().strftime("%Y%m%d-%H%M%S")


def slugify(text: str) -> str:
    chars: list[str] = []
    for ch in text.lower():
        if ch.isalnum():
            chars.append(ch)
        elif ch in {" ", "-", "_", ".", "/"}:
            chars.append("-")
    slug = "".join(chars).strip("-")
    while "--" in slug:
        slug = slug.replace("--", "-")
    return slug[:80] or "oracle"


def repo_root() -> Path:
    return Path(__file__).resolve().parents[1]


def state_dir() -> Path:
    raw = os.environ.get("ORACLE_STATE_DIR")
    if raw:
        root = Path(raw).expanduser()
    else:
        codex_home = Path(os.environ.get("CODEX_HOME", "~/.codex")).expanduser()
        root = codex_home / "state" / "oracle"
    root.mkdir(parents=True, exist_ok=True)
    (root / "raw").mkdir(exist_ok=True)
    (root / "prompts").mkdir(exist_ok=True)
    (root / "answers").mkdir(exist_ok=True)
    (root / "contexts").mkdir(exist_ok=True)
    return root


def index_path(root: Path) -> Path:
    return root / "index.json"


def load_index(root: Path) -> dict[str, Any]:
    path = index_path(root)
    if not path.exists():
        return {"version": 1, "conversations": {}}
    return json.loads(path.read_text())


def save_index(root: Path, index: dict[str, Any]) -> None:
    tmp = index_path(root).with_suffix(".json.tmp")
    tmp.write_text(json.dumps(index, indent=2, sort_keys=True) + "\n")
    tmp.replace(index_path(root))


def require_api_key() -> str:
    key = os.environ.get("OPENAI_API_KEY")
    if not key:
        raise SystemExit(
            "OPENAI_API_KEY is not set. Run `source ~/.zshrc` or export it "
            "before submitting an oracle request."
        )
    return key


def api_request(
    method: str, path: str, payload: dict[str, Any] | None = None
) -> dict[str, Any]:
    key = require_api_key()
    data = json.dumps(payload).encode("utf-8") if payload is not None else None
    request = urllib.request.Request(
        f"{API_BASE}{path}",
        data=data,
        method=method,
        headers={
            "Authorization": f"Bearer {key}",
            "Content-Type": "application/json",
        },
    )
    try:
        with urllib.request.urlopen(request, timeout=120) as response:
            body = response.read().decode("utf-8")
    except urllib.error.HTTPError as err:
        details = err.read().decode("utf-8", errors="replace")
        raise SystemExit(f"OpenAI API error {err.code}: {details}") from err
    except urllib.error.URLError as err:
        raise SystemExit(f"OpenAI API request failed: {err}") from err
    return json.loads(body)


def extract_text(response: dict[str, Any]) -> str:
    direct = response.get("output_text")
    if isinstance(direct, str) and direct.strip():
        return direct

    chunks: list[str] = []
    for item in response.get("output", []) or []:
        if item.get("type") != "message":
            continue
        for content in item.get("content", []) or []:
            if content.get("type") in {"output_text", "text"}:
                text = content.get("text")
                if isinstance(text, str):
                    chunks.append(text)
    return "\n\n".join(chunks).strip()


def response_payload(
    *,
    model: str,
    effort: str,
    max_output_tokens: int,
    prompt: str,
    background: bool,
    previous_response_id: str | None = None,
) -> dict[str, Any]:
    payload: dict[str, Any] = {
        "model": model,
        "instructions": SYSTEM_PROMPT,
        "input": prompt,
        "reasoning": {"effort": effort},
        "background": background,
        "store": True,
        "max_output_tokens": max_output_tokens,
    }
    if previous_response_id is not None:
        payload["previous_response_id"] = previous_response_id
    return payload


def save_turn_files(
    root: Path,
    response_id: str,
    *,
    prompt: str | None = None,
    request_payload: dict[str, Any] | None = None,
    raw_response: dict[str, Any] | None = None,
    answer_text: str | None = None,
) -> dict[str, str]:
    paths: dict[str, str] = {}
    if prompt is not None:
        path = root / "prompts" / f"{response_id}.md"
        path.write_text(prompt)
        paths["prompt_path"] = str(path)
    if request_payload is not None:
        path = root / "raw" / f"{response_id}.request.json"
        path.write_text(json.dumps(request_payload, indent=2, sort_keys=True) + "\n")
        paths["request_path"] = str(path)
    if raw_response is not None:
        path = root / "raw" / f"{response_id}.response.json"
        path.write_text(json.dumps(raw_response, indent=2, sort_keys=True) + "\n")
        paths["response_path"] = str(path)
    if answer_text is not None:
        path = root / "answers" / f"{response_id}.md"
        path.write_text(answer_text.rstrip() + "\n")
        paths["answer_path"] = str(path)
    return paths


def turn_record(
    response: dict[str, Any],
    *,
    title: str,
    context: Path,
    parent: str | None,
    prompt_paths: dict[str, str],
) -> dict[str, Any]:
    return {
        "response_id": response["id"],
        "title": title,
        "context": str(context),
        "parent": parent,
        "created_at": utc_now(),
        "updated_at": utc_now(),
        "status": response.get("status", "unknown"),
        **prompt_paths,
    }


def find_conversation(index: dict[str, Any], conversation_id: str) -> dict[str, Any]:
    conv = index["conversations"].get(conversation_id)
    if not conv:
        raise SystemExit(f"Unknown conversation: {conversation_id}")
    return conv


def find_turn(index: dict[str, Any], response_id: str) -> tuple[str, dict[str, Any]] | None:
    for conv_id, conv in index["conversations"].items():
        for turn in conv.get("turns", []):
            if turn.get("response_id") == response_id:
                return conv_id, turn
    return None


def run_git(args: list[str], *, max_chars: int = 12000) -> str:
    try:
        result = subprocess.run(
            ["git", *args],
            cwd=repo_root(),
            check=False,
            text=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
        )
    except OSError as err:
        return f"(git command failed: {err})"
    text = result.stdout.strip()
    if len(text) > max_chars:
        return text[:max_chars] + "\n... (truncated)"
    return text or "(no output)"


def read_text(path: Path) -> str:
    try:
        return path.read_text(errors="replace")
    except OSError as err:
        return f"(could not read {path}: {err})"


def truncate_middle(text: str, max_chars: int) -> str:
    if len(text) <= max_chars:
        return text
    keep = max_chars // 2
    tail = max_chars - keep
    return (
        text[:keep].rstrip()
        + "\n\n... (middle truncated by scripts/oracle.py) ...\n\n"
        + text[-tail:].lstrip()
    )


def latest_progress_entries(path: Path, max_entries: int, max_chars: int) -> str:
    text = read_text(path)
    if text.startswith("(could not read"):
        return text
    entries: list[str] = []
    current: list[str] = []
    for line in text.splitlines():
        if line.startswith("- "):
            if current:
                entries.append("\n".join(current))
            current = [line]
        elif current:
            current.append(line)
    if current:
        entries.append("\n".join(current))
    selected = entries[:max_entries] if entries else text.splitlines()[:80]
    return truncate_middle("\n\n".join(selected), max_chars)


def roadmap_front(path: Path, max_chars: int) -> str:
    text = read_text(path)
    if text.startswith("(could not read"):
        return text
    return text[:max_chars].rstrip() + (
        "\n... (truncated at roadmap front)" if len(text) > max_chars else ""
    )


def lean_module_inventory(max_files: int = 180) -> str:
    files = sorted(repo_root().joinpath("EvmCompiler").rglob("*.lean"))
    rels = [str(path.relative_to(repo_root())) for path in files[:max_files]]
    suffix = "" if len(files) <= max_files else f"\n... ({len(files) - max_files} more)"
    return "\n".join(rels) + suffix


def extract_decl_windows(path: Path, patterns: list[str], window: int, max_chars: int) -> str:
    text = read_text(path)
    if text.startswith("(could not read"):
        return text
    lines = text.splitlines()
    blocks: list[str] = []
    compiled = [re.compile(pattern) for pattern in patterns]
    seen_ranges: set[tuple[int, int]] = set()
    for idx, line in enumerate(lines):
        if not any(pattern.search(line) for pattern in compiled):
            continue
        start = max(0, idx - window)
        end = min(len(lines), idx + window + 1)
        key = (start, end)
        if key in seen_ranges:
            continue
        seen_ranges.add(key)
        numbered = [
            f"{line_no + 1}: {lines[line_no]}" for line_no in range(start, end)
        ]
        blocks.append("\n".join(numbered))
    if not blocks:
        return "(no declaration windows matched the configured patterns)"
    return truncate_middle("\n\n---\n\n".join(blocks), max_chars)


def file_excerpt(path: Path, max_chars: int) -> str:
    text = read_text(path)
    if text.startswith("(could not read"):
        return text
    return truncate_middle(text, max_chars)


def resolve_project_path(raw: str) -> Path:
    path = Path(raw).expanduser()
    if not path.is_absolute():
        path = repo_root() / path
    return path.resolve()


def build_architecture_context(args: argparse.Namespace) -> Path:
    root = repo_root()
    output = (
        Path(args.output).expanduser().resolve()
        if args.output
        else state_dir() / "contexts" / f"architecture-review-{local_timestamp()}.md"
    )
    files = list(DEFAULT_ARCHITECTURE_FILES)
    files.extend(args.extra_file or [])

    sections: list[str] = []
    sections.append(
        textwrap.dedent(
            f"""\
            # {args.title}

            Generated at: {utc_now()}
            Repository: {root}

            ## Requested Review

            {ARCHITECTURE_REVIEW_PROMPT.strip()}
            """
        ).rstrip()
    )
    sections.append(
        "## Git Status\n\n```text\n"
        + run_git(["status", "--short"], max_chars=16000)
        + "\n```"
    )
    sections.append(
        "## Git HEAD\n\n```text\n"
        + run_git(["rev-parse", "--short", "HEAD"], max_chars=2000)
        + "\n```"
    )
    sections.append(
        "## Lean Module Inventory\n\n```text\n" + lean_module_inventory() + "\n```"
    )

    roadmap = root / "ROADMAP.md"
    progress = root / "PROGRESS_LOG.md"
    sections.append(
        f"## ROADMAP.md Front\n\n```markdown\n{roadmap_front(roadmap, args.roadmap_chars)}\n```"
    )
    sections.append(
        "## Latest PROGRESS_LOG.md Entries\n\n```markdown\n"
        + latest_progress_entries(progress, args.progress_entries, args.progress_chars)
        + "\n```"
    )

    recursive_bridge = root / "EvmCompiler/Yul/RecursiveBridgeSupport.lean"
    sections.append(
        "## Selected Recursive Bridge Declaration Windows\n\n```lean\n"
        + extract_decl_windows(
            recursive_bridge,
            DECLARATION_PATTERNS,
            window=args.decl_window,
            max_chars=args.decl_chars,
        )
        + "\n```"
    )

    for raw in files:
        path = resolve_project_path(raw)
        if not path.exists() or path == roadmap or path == progress or path == recursive_bridge:
            continue
        try:
            label = str(path.relative_to(root))
        except ValueError:
            label = str(path)
        sections.append(
            f"## File Excerpt: {label}\n\n```lean\n{file_excerpt(path, args.file_chars)}\n```"
        )

    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_text("\n\n".join(sections).rstrip() + "\n")
    return output


def make_prompt(title: str, context_path: Path, context: str, followup: bool) -> str:
    kind = "follow-up" if followup else "new request"
    return textwrap.dedent(
        f"""\
        Oracle {kind}: {title}

        Context file: {context_path}

        Please review the following context and respond with:
        1. the architectural/proof-theoretic diagnosis;
        2. the most likely route to finish;
        3. concrete Lean theorem/interface changes to try next;
        4. risks, false assumptions, or places where the plan may blow up.

        --- BEGIN CONTEXT ---
        {context}
        --- END CONTEXT ---
        """
    )


def submit_request(
    *,
    title: str,
    context_path: Path,
    model: str,
    effort: str,
    max_output_tokens: int,
    foreground: bool,
    dry_run: bool,
    parent: str | None = None,
    conversation_id: str | None = None,
) -> None:
    root = state_dir()
    index = load_index(root)
    conversation = (
        find_conversation(index, conversation_id) if conversation_id is not None else None
    )
    context = context_path.read_text()
    prompt = make_prompt(title, context_path, context, followup=parent is not None)
    payload = response_payload(
        model=model,
        effort=effort,
        max_output_tokens=max_output_tokens,
        prompt=prompt,
        background=not foreground,
        previous_response_id=parent,
    )
    if dry_run:
        print(json.dumps(payload, indent=2, sort_keys=True))
        return

    response = api_request("POST", "/responses", payload)
    response_id = response["id"]
    paths = save_turn_files(
        root, response_id, prompt=prompt, request_payload=payload, raw_response=response
    )
    if conversation is None:
        conv_id = response_id
        index["conversations"][conv_id] = {
            "id": conv_id,
            "title": title,
            "slug": slugify(title),
            "created_at": utc_now(),
            "updated_at": utc_now(),
            "model": model,
            "effort": effort,
            "max_output_tokens": max_output_tokens,
            "turns": [
                turn_record(
                    response,
                    title=title,
                    context=context_path,
                    parent=None,
                    prompt_paths=paths,
                )
            ],
        }
    else:
        conversation["turns"].append(
            turn_record(
                response,
                title=title,
                context=context_path,
                parent=parent,
                prompt_paths=paths,
            )
        )
        conversation["updated_at"] = utc_now()
    save_index(root, index)
    print(f"submitted {response_id}")
    print(f"status: {response.get('status', 'unknown')}")
    print(f"conversation: {conversation['id'] if conversation else response_id}")
    print(f"state: {root}")


def command_build_architecture_context(args: argparse.Namespace) -> None:
    path = build_architecture_context(args)
    print(path)


def command_ask_architecture(args: argparse.Namespace) -> None:
    context_path = build_architecture_context(args)
    print(f"context: {context_path}", file=sys.stderr)
    submit_request(
        title=args.title,
        context_path=context_path,
        model=args.model,
        effort=args.effort,
        max_output_tokens=args.max_output_tokens,
        foreground=args.foreground,
        dry_run=args.dry_run,
    )


def command_ask(args: argparse.Namespace) -> None:
    submit_request(
        title=args.title,
        context_path=Path(args.context).expanduser().resolve(),
        model=args.model,
        effort=args.effort,
        max_output_tokens=args.max_output_tokens,
        foreground=args.foreground,
        dry_run=args.dry_run,
    )


def update_polled_turn(root: Path, index: dict[str, Any], response_id: str) -> None:
    found = find_turn(index, response_id)
    if not found:
        print(f"{response_id}: not tracked locally")
        return
    conv_id, turn = found
    response = api_request("GET", f"/responses/{response_id}")
    status = response.get("status", "unknown")
    paths = save_turn_files(root, response_id, raw_response=response)
    turn.update(paths)
    turn["status"] = status
    turn["updated_at"] = utc_now()
    index["conversations"][conv_id]["updated_at"] = utc_now()
    text = extract_text(response)
    if text:
        turn.update(save_turn_files(root, response_id, answer_text=text))
    error = response.get("error")
    if error:
        turn["error"] = error
    print(f"{response_id}: {status}")
    if text:
        print(f"answer: {turn['answer_path']}")
    if error:
        print(f"error: {json.dumps(error, sort_keys=True)}")


def command_poll(args: argparse.Namespace) -> None:
    root = state_dir()
    index = load_index(root)
    if args.all:
        ids = [
            turn["response_id"]
            for conv in index["conversations"].values()
            for turn in conv.get("turns", [])
            if turn.get("status") not in TERMINAL_STATUSES
        ]
    elif args.response_id:
        ids = [args.response_id]
    else:
        raise SystemExit("poll needs a response_id or --all")
    if not ids:
        print("no pending responses")
        return
    for response_id in ids:
        update_polled_turn(root, index, response_id)
    save_index(root, index)


def command_list(args: argparse.Namespace) -> None:
    root = state_dir()
    index = load_index(root)
    rows = []
    for conv_id, conv in index["conversations"].items():
        turns = conv.get("turns", [])
        status = turns[-1].get("status", "unknown") if turns else "unknown"
        if args.pending and status in TERMINAL_STATUSES:
            continue
        rows.append((conv.get("updated_at", ""), conv_id, status, conv.get("title", "")))
    for _updated, conv_id, status, title in sorted(rows, reverse=True):
        print(f"{conv_id}  {status:12}  {title}")


def command_show(args: argparse.Namespace) -> None:
    root = state_dir()
    index = load_index(root)
    conv = find_conversation(index, args.conversation)
    turns = conv.get("turns", [])
    if not turns:
        print(json.dumps(conv, indent=2, sort_keys=True))
        return
    turn = turns[-1] if args.latest else next(
        (item for item in turns if item["response_id"] == args.turn),
        None,
    )
    if not turn:
        raise SystemExit(f"turn not found: {args.turn}")
    answer = turn.get("answer_path")
    if answer and Path(answer).exists():
        print(Path(answer).read_text())
    else:
        print(json.dumps(turn, indent=2, sort_keys=True))


def resolve_parent(conv: dict[str, Any], parent: str) -> str:
    if parent == "latest":
        turns = conv.get("turns", [])
        if not turns:
            raise SystemExit("conversation has no prior turns")
        return turns[-1]["response_id"]
    for turn in conv.get("turns", []):
        if turn["response_id"] == parent:
            return parent
    raise SystemExit(f"parent response not found in conversation: {parent}")


def command_reply(args: argparse.Namespace) -> None:
    root = state_dir()
    index = load_index(root)
    conv = find_conversation(index, args.conversation)
    parent = resolve_parent(conv, args.parent)
    title = args.title or f"Follow-up to {conv['title']}"
    submit_request(
        title=title,
        context_path=Path(args.context).expanduser().resolve(),
        model=args.model or conv.get("model", DEFAULT_MODEL),
        effort=args.effort or conv.get("effort", DEFAULT_EFFORT),
        max_output_tokens=args.max_output_tokens
        or conv.get("max_output_tokens", DEFAULT_MAX_OUTPUT_TOKENS),
        foreground=args.foreground,
        dry_run=args.dry_run,
        parent=parent,
        conversation_id=args.conversation,
    )


def add_common_model_args(parser: argparse.ArgumentParser) -> None:
    parser.add_argument("--model", default=DEFAULT_MODEL)
    parser.add_argument("--effort", default=DEFAULT_EFFORT)
    parser.add_argument("--max-output-tokens", type=int, default=DEFAULT_MAX_OUTPUT_TOKENS)
    parser.add_argument("--foreground", action="store_true", help="disable background mode")
    parser.add_argument("--dry-run", action="store_true", help="print request JSON only")


def add_architecture_context_args(parser: argparse.ArgumentParser) -> None:
    parser.add_argument("--title", default=ARCHITECTURE_TITLE)
    parser.add_argument("--output", help="write generated context here")
    parser.add_argument(
        "--extra-file",
        action="append",
        help="additional project file to excerpt into the architecture packet",
    )
    parser.add_argument("--roadmap-chars", type=int, default=40000)
    parser.add_argument("--progress-entries", type=int, default=24)
    parser.add_argument("--progress-chars", type=int, default=36000)
    parser.add_argument("--file-chars", type=int, default=18000)
    parser.add_argument("--decl-window", type=int, default=16)
    parser.add_argument("--decl-chars", type=int, default=36000)


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(
        description="Ask/poll GPT Pro oracle jobs for the evm-compiler repo."
    )
    sub = parser.add_subparsers(dest="command", required=True)

    build_ctx = sub.add_parser(
        "build-architecture-context",
        help="write a compact architecture-review context markdown file",
    )
    add_architecture_context_args(build_ctx)
    build_ctx.set_defaults(func=command_build_architecture_context)

    ask_arch = sub.add_parser(
        "ask-architecture",
        help="build an architecture context packet and submit it to the oracle",
    )
    add_architecture_context_args(ask_arch)
    add_common_model_args(ask_arch)
    ask_arch.set_defaults(func=command_ask_architecture)

    ask = sub.add_parser("ask", help="submit a hand-written context file")
    ask.add_argument("--title", required=True)
    ask.add_argument("--context", required=True)
    add_common_model_args(ask)
    ask.set_defaults(func=command_ask)

    poll = sub.add_parser("poll", help="poll one response or all pending responses")
    poll.add_argument("response_id", nargs="?")
    poll.add_argument("--all", action="store_true")
    poll.set_defaults(func=command_poll)

    list_cmd = sub.add_parser("list", help="list local oracle conversations")
    list_cmd.add_argument("--pending", action="store_true")
    list_cmd.set_defaults(func=command_list)

    show = sub.add_parser("show", help="show a local oracle answer")
    show.add_argument("conversation")
    show.add_argument("--latest", action="store_true", default=False)
    show.add_argument("--turn", help="specific response id to show")
    show.set_defaults(func=command_show)

    reply = sub.add_parser("reply", help="reply to a previous oracle response")
    reply.add_argument("--conversation", required=True)
    reply.add_argument("--parent", default="latest")
    reply.add_argument("--context", required=True)
    reply.add_argument("--title")
    reply.add_argument("--model")
    reply.add_argument("--effort")
    reply.add_argument("--max-output-tokens", type=int)
    reply.add_argument("--foreground", action="store_true", help="disable background mode")
    reply.add_argument("--dry-run", action="store_true", help="print request JSON only")
    reply.set_defaults(func=command_reply)
    return parser


def main(argv: list[str] | None = None) -> int:
    args = build_parser().parse_args(argv)
    args.func(args)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
