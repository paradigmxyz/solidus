#!/usr/bin/env python3
from __future__ import annotations

import argparse
import json
import statistics
from collections import defaultdict
from pathlib import Path
from typing import Any


def read_jsonl(path: Path) -> list[dict[str, Any]]:
    rows: list[dict[str, Any]] = []
    with path.open() as handle:
        for line in handle:
            line = line.strip()
            if line:
                rows.append(json.loads(line))
    return rows


def fmt(value: float) -> str:
    return f"{value:.4f}"


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("scores", type=Path)
    args = parser.parse_args()

    rows = read_jsonl(args.scores)
    groups: dict[tuple[str, str], list[dict[str, Any]]] = defaultdict(list)
    for row in rows:
        groups[(row["language"], row["context"])].append(row)

    print("language\tcontext\tn\tmean_bpb\tmedian_bpb\tstdev_bpb\tmean_bytes")
    for (language, context), group in sorted(groups.items()):
        bpbs = [float(row["bpb"]) for row in group]
        byte_counts = [int(row["target_bytes"]) for row in group]
        stdev = statistics.stdev(bpbs) if len(bpbs) > 1 else 0.0
        print(
            "\t".join(
                [
                    language,
                    context,
                    str(len(group)),
                    fmt(statistics.mean(bpbs)),
                    fmt(statistics.median(bpbs)),
                    fmt(stdev),
                    fmt(statistics.mean(byte_counts)),
                ]
            )
        )


if __name__ == "__main__":
    main()
