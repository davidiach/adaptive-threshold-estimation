# Freeze log

Record every change made to a frozen file BEFORE `tools/freeze.py --init`
(Phase 0 compile fixes only). After freezing, changes need David's approval
and go here too, with the approval noted.

Format, one entry per change:

## <file> — <short title>
- Before: `...`
- After: `...`
- Why: elaboration error message, and why the meaning is unchanged.

---

## Tier 2 integration and 713 hardening — 27 October 2026

- Approved by: David, in this chat on 27 October 2026.
- Approval quote: "Go ahead and fix the two validation issues, harden the 713 guard, and integrate Tier 2. I approve re-freezing once all checks pass."
- Scope: all 13 proposed Tier 2 targets (61 points), scorer v2 with both reviewed validation fixes, and the 713 definition lock.
- Proposal: Opus patch `bd5d3f367602d792e6873e066290649653bec621`, applied to the completed-713 baseline `852690a`.
- Mathematical statements: original Tier 1 and all 713 Lean sources are byte-identical to `852690a`; all proposed Tier 2 statement text is unchanged (checkout line endings differ from the review copy). No syntax/elaboration fixes were required; `lake build ThresholdHC.Statements2`, all Tier 2 proof modules, and the full library build passed.
- Before: 12 frozen files; score 60/60; scorer did not enforce audit exit/completeness; mixed `sorryAx`/unexpected-axiom reports were classified as `sorry`.
- After: 21 frozen files; 46 targets worth 121 points; scorer enforces exit/completeness and rejects unexpected axioms before handling `sorryAx`.
- Numeric validation: remove the I6 passing fallback, require positive coverage, and add a deterministic qualifying I6 case. Regression tests suppress all I6 evaluations and require failure.
- 713 hardening: preserve existing Lean bytes and lock the specification's complete local import closure. Whole-file locks include proofs in those dependency modules; no definition refactor or theorem weakening.
- Previously frozen files changed: `lean/ThresholdHC.lean`, `tools/targets.json`, `tools/score.py`, `tools/freeze.py`, `tools/check_targets_numeric.py`.
- Newly frozen files: `lean/ThresholdHC/Statements2.lean`, `tools/check_targets2_numeric.py`, `lean/ThresholdHC/Uniform713/Specification.lean`, `lean/ThresholdHC/Uniform713/Common.lean`, `lean/ThresholdHC/Uniform713/Concentration.lean`, `lean/ThresholdHC/Uniform713/Classifier.lean`, `lean/ThresholdHC/Uniform713/Estimator.lean`, `tools/uniform713_targets.json`, `tools/verify_uniform713.py`.
- Pre-freeze validation: all ten validation regression tests passed; numerical suites passed 33/33 and 13/13 (I6 has 25 evaluated cases); input hashes, experiment locks, power-bracket, bias, uniform arithmetic, and existing constants configuration checks passed. Evidence: `results/tier2_numeric_gates.json` and `.log`.
- Pre-freeze Lean audit: exit 0, 33 proven / 13 `sorry`, no errors or violations (`results/tier2_prefreeze_audit.json` and `.log`). The complete 713 guard passed 130/130 roots with both specification and dependency locks; the scalar audit passed 7/7.
- Integration portability fix: all 11 sequential module builds passed, but the scorer's full-build output reader failed under Windows cp1252 on Lean's UTF-8 diagnostics. The scorer and both checkpoint/713 audit readers now decode UTF-8 explicitly; scorer log writes also specify UTF-8. The new regression emulates cp1252 even on Linux. Tests were rerun with `PYTHONUTF8=0`; no mathematical statement changed. The freeze is regenerated after validating this additional repair under the same approval.
- Re-freeze: performed only after the above gates passed; all 21 hashes verify. All 11 target modules passed sequential builds; after the Windows decoding fix, `tools/verify_lean_checkpoint.py` passed the full build, the frozen scorer, and its independent 46-report audit with no Tier 1 regression.
- Baseline saved: `results/lean_best.json` and `results/lean_tier2_baseline.json`, valid 60/121 (Tier 1 60/60, Tier 2 0/61); all 13 Tier 2 proofs remain `sorry`. Evidence: `results/lean_checkpoint.json`, `results/lean_audit.log`, and `results/lean_independent_audit.log`.
- Verification environment: local Windows with the pinned Lean/Mathlib and Python dependencies. CI includes the new regression suite; this entry does not claim a remote CI run for the integration.
