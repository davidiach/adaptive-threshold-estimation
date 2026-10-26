# Threshold hill-climbing starter kit

A harness for letting coding agents improve the adaptive-threshold research
overnight, using only machine-checkable scores. Give Astra this folder plus
both research packages, v4 and next-phase. The agent instructions are in
`BRIEF.md`.

## Layout

| Path | What it is |
|---|---|
| `BRIEF.md` | Agent instructions: Phase 0, four tracks, rules, report format |
| `lean/ThresholdHC/Statements.lean` | 33 frozen Lean statements of v4 lemmas (60 points) |
| `lean/ThresholdHC/Proofs/*.lean` | `sorry` stubs, one file per group; agents fill these |
| `lean/setup.sh` | Installs Lean if needed, pins Mathlib, builds |
| `tools/score.py` | Lean scorer and cheat checks: frozen hashes, forbidden constructs, build, per-target type and axiom audit |
| `tools/freeze.py` | Records hashes of frozen files after Phase 0 |
| `tools/check_targets_numeric.py` | High-precision check that every frozen statement is true |
| `tools/targets.json` | Target list, points and files |
| `constants/` | Exact evaluator and scorer for the variance–work constant |
| `FREEZE_LOG.md`, `RUNLOG.md` | Logs the agent must keep |

## Status when handed over (26 October 2026)

- All 33 Lean statements pass the numerical truth check.
- **They have not been compiled.** This environment could not reach Mathlib's
  cache. Phase 0 is a compile gate: syntax-only fixes are allowed and must be
  logged in `FREEZE_LOG.md`.
- The scorer was tested against simulated Lean output. It catches:
  - non-standard axioms, including `native_decide`'s;
  - forbidden tokens;
  - type mismatches with the frozen statements;
  - edits to frozen files;
  - regressions.
- The constants scorer was tested end to end. The v4 baseline proxy is 6.78;
  `k2 = 0.7` gives 5.95; out-of-bounds settings are rejected.

## What to check in the morning

1. `FREEZE_LOG.md`: read every entry. Any change that alters a statement's
   meaning invalidates the related points.
2. `results/lean_best.json`: points, proven targets, and the axioms list.
3. `RUNLOG.md`: the attempt history.
4. `REPORT.md`: the agent's summary, with status labels.

For a final check of any Lean proof, rerun `python tools/score.py` on a clean
checkout. For extra assurance, replay the build with an external kernel
checker such as `lean4checker`.
