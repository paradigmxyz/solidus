#!/usr/bin/env python3
from __future__ import annotations

import argparse
import json
import math
import os
import time
import urllib.error
import urllib.request
from pathlib import Path
from typing import Any


DEFAULT_BASE_URL = "https://api.together.xyz/v1"


def read_jsonl(path: Path) -> list[dict[str, Any]]:
    rows: list[dict[str, Any]] = []
    with path.open() as handle:
        for line in handle:
            line = line.strip()
            if line:
                rows.append(json.loads(line))
    return rows


def append_jsonl(path: Path, row: dict[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("a") as handle:
        handle.write(json.dumps(row, ensure_ascii=False, sort_keys=True))
        handle.write("\n")


def completed_keys(path: Path) -> set[tuple[str, str, str]]:
    if not path.exists():
        return set()
    keys: set[tuple[str, str, str]] = set()
    for row in read_jsonl(path):
        keys.add((row["id"], row["context"], row["model"]))
    return keys


def post_json(url: str, api_key: str, payload: dict[str, Any]) -> dict[str, Any]:
    request = urllib.request.Request(
        url,
        data=json.dumps(payload).encode("utf-8"),
        headers={
            "Authorization": f"Bearer {api_key}",
            "Content-Type": "application/json",
        },
        method="POST",
    )
    try:
        with urllib.request.urlopen(request, timeout=180) as response:
            return json.loads(response.read().decode("utf-8"))
    except urllib.error.HTTPError as exc:
        body = exc.read().decode("utf-8", errors="replace")
        raise RuntimeError(f"Together API error {exc.code}: {body}") from exc


def extract_logprobs(response: dict[str, Any]) -> tuple[list[str], list[float | None], list[int]]:
    # Together's completions-compatible response usually puts echo logprobs on
    # choices[0].logprobs. Some deployments expose prompt logprobs separately.
    if response.get("prompt"):
        prompt = response["prompt"][0]
        logprobs = prompt["logprobs"]
    else:
        choices = response.get("choices") or []
        if not choices or "logprobs" not in choices[0]:
            raise RuntimeError(f"response has no logprobs: {response}")
        logprobs = choices[0]["logprobs"]

    tokens = logprobs.get("tokens")
    token_logprobs = logprobs.get("token_logprobs")
    offsets = logprobs.get("text_offset")
    if tokens is None or token_logprobs is None or offsets is None:
        raise RuntimeError(f"logprobs missing tokens/token_logprobs/text_offset: {logprobs}")
    return tokens, token_logprobs, offsets


def score_prompt(
    *,
    api_key: str,
    base_url: str,
    model: str,
    context: str,
    target: str,
) -> dict[str, Any]:
    combined = context + target
    payload = {
        "model": model,
        "prompt": combined,
        "max_tokens": 1,
        "temperature": 0,
        "echo": True,
        "logprobs": 1,
    }
    response = post_json(f"{base_url.rstrip('/')}/completions", api_key, payload)
    tokens, token_logprobs, offsets = extract_logprobs(response)
    boundary = len(context)
    end = len(combined)

    selected: list[tuple[str, float, int]] = []
    for token, logprob, offset in zip(tokens, token_logprobs, offsets, strict=True):
        if boundary <= offset < end:
            if logprob is None:
                raise RuntimeError("target token had null logprob")
            selected.append((token, float(logprob), int(offset)))
    if not selected:
        raise RuntimeError("no scored target tokens found; response offsets may be incompatible")

    total_logprob = sum(logprob for _, logprob, _ in selected)
    target_bytes = len(target.encode("utf-8"))
    target_tokens = len(selected)
    return {
        "target_bytes": target_bytes,
        "target_tokens": target_tokens,
        "logprob_sum": total_logprob,
        "neg_logprob": -total_logprob,
        "bpb": -total_logprob / math.log(2) / target_bytes,
        "token_perplexity": math.exp(-total_logprob / target_tokens),
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--targets", type=Path, default=Path("/tmp/yul_bpb_targets.jsonl"))
    parser.add_argument("--output", type=Path, default=Path("/tmp/yul_bpb_scores.jsonl"))
    parser.add_argument("--model", default="zai-org/GLM-5.2")
    parser.add_argument("--base-url", default=DEFAULT_BASE_URL)
    parser.add_argument("--contexts", default="header,imports_header,file_prefix_8k,file_prefix_32k")
    parser.add_argument("--limit", type=int, default=0)
    parser.add_argument("--sleep", type=float, default=0.0)
    parser.add_argument("--resume", action="store_true")
    parser.add_argument("--dry-run", action="store_true")
    args = parser.parse_args()

    targets = read_jsonl(args.targets)
    if args.limit:
        targets = targets[: args.limit]
    contexts = [context.strip() for context in args.contexts.split(",") if context.strip()]

    if args.dry_run:
        for target in targets[:10]:
            for context_name in contexts:
                context = target["contexts"][context_name]
                request_chars = len(context) + len(target["target"])
                print(
                    f"{target['id']}\t{context_name}\tchars={request_chars}\t"
                    f"target_bytes={target['target_bytes']}"
                )
        print(f"dry run: {len(targets)} targets x {len(contexts)} contexts")
        return

    api_key = os.environ.get("TOGETHER_API_KEY")
    if not api_key:
        raise SystemExit("TOGETHER_API_KEY is not set")

    done = completed_keys(args.output) if args.resume else set()
    for target in targets:
        for context_name in contexts:
            key = (target["id"], context_name, args.model)
            if key in done:
                continue
            metrics = score_prompt(
                api_key=api_key,
                base_url=args.base_url,
                model=args.model,
                context=target["contexts"][context_name],
                target=target["target"],
            )
            row = {
                "id": target["id"],
                "language": target["language"],
                "kind": target["kind"],
                "name": target["name"],
                "path": target["path"],
                "context": context_name,
                "model": args.model,
                "body_lines": target["body_lines"],
                **metrics,
            }
            append_jsonl(args.output, row)
            print(
                f"{row['language']}\t{row['context']}\t{row['id']}\t"
                f"bpb={row['bpb']:.4f}\ttokens={row['target_tokens']}"
            )
            if args.sleep:
                time.sleep(args.sleep)


if __name__ == "__main__":
    main()
