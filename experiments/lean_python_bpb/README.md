# Lean/Python BPB Pilot

Local-only harness for a first bits-per-byte comparison between this Lean
compiler and the Python Yul compiler in `../python-yul`.

The checked-in scripts do not call any model unless you run the scorer with a
`TOGETHER_API_KEY`.

## Build Targets

```sh
python3 experiments/lean_python_bpb/build_targets.py \
  --lean-root . \
  --python-root ../python-yul \
  --per-language 60 \
  --output /tmp/yul_bpb_targets.jsonl
```

Each target hides a declaration/function body and records these context views:

- `header`: declaration/function header only.
- `imports_header`: imports plus the header.
- `file_prefix_8k`: last 8,000 characters before the hidden body.
- `file_prefix_32k`: last 32,000 characters before the hidden body.
- `file_prefix`: exact file prefix up to the hidden body, capped by
  `--max-context-chars`.

## Score With GLM-5.2

After setting `TOGETHER_API_KEY`:

```sh
python3 experiments/lean_python_bpb/score_together.py \
  --targets /tmp/yul_bpb_targets.jsonl \
  --output /tmp/yul_bpb_scores.jsonl \
  --contexts header,imports_header,file_prefix_8k,file_prefix_32k \
  --model zai-org/GLM-5.2
```

The scorer uses Together's completions API with `echo` and `logprobs`, then
sums logprobs only over the original hidden body span. The primary metric is:

```text
BPB = -sum(logprobs) / ln(2) / target_body_bytes
```

Use `--dry-run` first to inspect request sizes without making API calls.

## Analyze

```sh
python3 experiments/lean_python_bpb/analyze_scores.py \
  /tmp/yul_bpb_scores.jsonl
```
