<!--
  Solidus Arena PR template.

  * Contest submissions target the `arena` branch and MUST fill in the
    Based-on line below (CI checks it by git ancestry).
  * Non-contest contributions (compiler improvements outside the arena) target
    `main` — you can delete the arena-specific sections.

  See CONTRIBUTING.md and CHALLENGE.md.
-->

## Based-on

<!-- REQUIRED for arena submissions. Which record did you branch from?
     Must match a `record-N` tag (or `arena`, the current record). -->

Based-on: record-N

## Summary

<!-- What did you change? Which pass / IR / proof did you rewrite? -->

## Sizes / gas summary

<!-- Paste the relevant totals from your local run (benchmarks/opt_last_run.json
     after `scripts/opt_harness.sh bench` or `full`). -->

- total_gas:
- total_deploy_gas:
- total_exec_gas:
- vs baseline:

## Checklist

- [ ] `scripts/opt_harness.sh full` is **green locally** (proof gate + bench).
- [ ] `#print axioms` footprint is exactly `[propext, Classical.choice, Quot.sound]`.
- [ ] I did **not** edit any hash-frozen file (see `benchmarks/frozen_manifest.txt`).
- [ ] Compiler output is **deterministic** (byte-identical on a repeat compile).
- [ ] Every corpus contract still compiles (fail-closed: no output, no score).
- [ ] `Based-on:` above names the record I branched from.
