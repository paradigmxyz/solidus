#!/usr/bin/env bash

set -euo pipefail

repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$repo_root"

failed=0

report_matches() {
  local title="$1"
  shift
  local matches
  matches="$(rg -n "$@" 2>/dev/null || true)"
  if [[ -n "$matches" ]]; then
    printf '%s\n%s\n\n' "$title" "$matches" >&2
    failed=1
  fi
}

report_matches \
  'Syntax modules must not import aggregate layer modules:' \
  '^import EvmCompiler\.(Assembly|TypedCfg|Structured|Expressions|Locals|Functions|Objects|Yul|Solidity)$' \
  EvmCompiler -g '*Syntax.lean'

report_matches \
  'Syntax modules must not import compiler or proof modules:' \
  '^import EvmCompiler\..*(Compiler|Preservation|SourceLowering|Semantics)' \
  EvmCompiler -g '*Syntax.lean'

report_matches \
  'Semantic modules must not import compiler or proof modules:' \
  '^import EvmCompiler\..*(Compiler|Preservation|SourceLowering)' \
  EvmCompiler -g '*Semantics.lean'

report_matches \
  'Semantic modules must not import aggregate layer modules:' \
  '^import EvmCompiler\.(Assembly|TypedCfg|Structured|Expressions|Locals|Functions|Objects|Yul|Solidity)$' \
  EvmCompiler -g '*Semantics.lean'

report_matches \
  'The stable root must import only stable API modules:' \
  '^import EvmCompiler\.(Assembly|Structured|Expressions|Locals|Functions|Objects|Yul|Solidity|LayerAudit)$' \
  EvmCompiler.lean

report_matches \
  'Stable public modules must not import legacy theorem corridors:' \
  '^import EvmCompiler\.(LayerAudit|Yul\.(NoCallRuntime|OpenLowering|OpenGasAware|OpenRuntime|ObserverOracle))' \
  EvmCompiler.lean EvmCompiler/Public.lean

report_matches \
  'The Objects public compiler must not call legacy backend target emitters:' \
  'Functions\.(CallAwareSpill|ScratchFrameSpill)\..*compile(Target|Executable)' \
  EvmCompiler/Objects/Compiler.lean

if ! rg -q 'Structured\.TypedCfgCompiler\.compile\?' \
    EvmCompiler/Objects/Compiler.lean ||
    ! rg -q 'AllocatedTypedCfg\.Program\.compileCertified\?' \
      EvmCompiler/Objects/Compiler.lean; then
  printf '%s\n\n' \
    'The Objects public compiler must lower through the certified allocated TypedCfg pass.' \
    >&2
  failed=1
fi
report_matches \
  'The Objects public compiler must not bypass the allocated TypedCfg pass through the Expressions convenience compiler:' \
  'Expressions\.Program\.compileTypedArtifact\?' \
  EvmCompiler/Objects/Compiler.lean

report_matches \
  'The Objects public compiler must not call the legacy two-pass scratch-frame emitter:' \
  'ScratchFrameSpill\.compileExpressionsProgram\?' \
  EvmCompiler/Objects/Compiler.lean

planned_program="$(
  sed -n '/^structure PlannedProgram where$/,/^namespace PlannedProgram$/p' \
    EvmCompiler/Objects/Compiler.lean
)"
if rg -q 'expressions[[:space:]]*:[[:space:]]*Expressions\.Program' \
    <<<"$planned_program"; then
  printf '%s\n\n' \
    'The public allocation planner must not carry an already emitted Expressions program.' \
    >&2
  failed=1
fi
if ! rg -q 'source[[:space:]]*:[[:space:]]*Functions\.Program' \
    <<<"$planned_program" ||
    ! rg -q 'allocation[[:space:]]*:[[:space:]]*Locals\.Allocation\.ProgramPlan' \
      <<<"$planned_program"; then
  printf '%s\n\n' \
    'The public planned artifact must carry the Functions source and scoped canonical allocation.' \
    >&2
  failed=1
fi
if ! rg -q 'def lowerExpressions\?' EvmCompiler/Objects/Compiler.lean ||
    ! rg -q 'def allocationLowerer' EvmCompiler/Objects/Compiler.lean ||
    ! rg -q 'def LoweredFrom' EvmCompiler/Objects/Compiler.lean; then
  printf '%s\n\n' \
    'The Objects compiler must expose one allocation-consuming lowerer and its executable certificate relation.' \
    >&2
  failed=1
fi
if ! rg -q 'ScratchFrameSpill\.allocationPlanner' \
      EvmCompiler/Objects/Compiler.lean ||
    ! rg -q 'ScratchFrameSpill\.allocationLowerer' \
      EvmCompiler/Objects/Compiler.lean; then
  printf '%s\n\n' \
    'The public scratch-frame route must use code-free scoped planning and allocation-driven single-pass lowering.' \
    >&2
  failed=1
fi
report_matches \
  'Objects inline planning must not restore the hard-coded empty allocation:' \
  'stackOnlyProgramAllocation|stackOnlyAllocation' \
  EvmCompiler/Objects/Compiler.lean
report_matches \
  'The stable Objects compiler must not restore parallel CallAware emitters or planner discovery:' \
  'CallAwareSpill|callAwareSpill|callAwareSwitchSpill|compileCallAwareCandidates' \
  EvmCompiler/Objects/Compiler.lean
report_matches \
  'User-facing bridge diagnostics must not restore retired parallel backends:' \
  'Functions\.(LiveLayout|CallAwareSpill|ScratchFrameSpill)|live_layout_|call_aware_|adaptive_spill|scratch_frame_spill' \
  scripts/solidity_to_yul_lean.py
report_matches \
  'Successful public compiler metadata must not make allocation or TypedCfg certificates optional:' \
  '(allocation|typedCfg)\?[[:space:]]*:[[:space:]]*Option' \
  EvmCompiler/Objects/Compiler.lean

report_matches \
  'Stable layer aggregates must not import preservation or legacy runtime corridors:' \
  '^import EvmCompiler\..*(Preservation|StackResource|SourceLowering|SourceDirect|RecursiveBridgeSupport|ObjectRuntime|OpenExternal|OpenAssembly|OpenLowering|ObserverOracle|NoCallCreate|NoCallRuntime)' \
  EvmCompiler/Assembly.lean \
  EvmCompiler/Structured.lean \
  EvmCompiler/Expressions.lean \
  EvmCompiler/Locals.lean \
  EvmCompiler/Functions.lean \
  EvmCompiler/Objects.lean \
  EvmCompiler/Yul.lean

report_matches \
  'Migrated architecture modules must not contain proof holes:' \
  '\b(sorry|admit|sorryAx)\b' \
  EvmCompiler/Core \
  EvmCompiler/Compiler \
  EvmCompiler/Public.lean \
  EvmCompiler/Simulation \
  EvmCompiler/Locals/Allocation.lean \
  EvmCompiler/Locals/EffectSemantics.lean \
  EvmCompiler/TypedCfg \
  EvmCompiler/Structured/TypedCfgCompiler.lean

oversized="$(
  find EvmCompiler -type f -name '*.lean' -print0 |
    xargs -0 wc -l |
    awk '$1 > 5000 && $2 != "total" { print $1 " " $2 }' |
    sort -nr
)"
if [[ -n "$oversized" ]]; then
  printf 'Architecture debt: modules above the 5K-line soft limit:\n%s\n\n' \
    "$oversized"
fi

if ((failed != 0)); then
  printf 'architecture dependency check failed\n' >&2
  exit 1
fi

printf 'architecture dependency check passed\n'
