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

## Separate Tier 3 specification lock — 27 October 2026

- Authorization: David requested Tier 3 randomized policies, unbounded stopping,
  and the arbitrary-law optimizer, using multiple agents and verified commits,
  with another eight-hour-or-landmark goal.
- The original `FROZEN.sha256`, all 21 protected files, and the 121-point target
  set are unchanged. This is a separate extension, not a re-scoring of Tier 2.
- `TIER3_FROZEN.sha256` locks the four definition-only model files, the complete
  landmark specification, their local statement dependencies, the target
  manifest, and the Tier 3 verifier (nine files including two existing sources).
  Every model and the combined specification compiled before the lock was made.
- The fixed targets cover arbitrary measurable common seeds, marginal KL and
  seed-dependent tests; finite expected plus-work implying halting under both
  hypotheses; unbounded terminal testing; the arbitrary-law optimizer with
  cutoff existence/uniqueness and both parameter regimes; and an explicit
  geometric-seed experiment with unbounded work support and finite expectation.
- The locked verifier checks exact final target types, standard axioms, every
  public Tier 3 declaration, source stability during the audit, and both sets
  of frozen hashes. Missing target proofs remain pending. `--require-complete`
  rejects any partial checkpoint. Eight failure-path regression tests pass.
- First accepted component audit: four of eleven registered targets, 81/81
  declaration reports, exit zero, standard axioms only. The full optimizer is
  included; unbounded stopping/testing and the example remain pending.
- Final landmark in `23988c7`: all eleven exact targets and 152/152 declarations
  pass with only the three standard axioms. All nine Tier 3 locks and the
  original 21-file freeze are unchanged. The original score remains 121/121;
  the separate full 713 audit remains 130/130. Independent Linux run
  [40468287646](https://github.com/davidiach/adaptive-threshold-estimation/actions/runs/40468287646)
  passed both jobs with complete Tier 3 verification required.

## Distribution-blind and critical upper specifications — 28 October 2026

- These are separate extension specifications. No previously frozen file,
  lock manifest or score changed.
- `lean/ThresholdHC/BlindUpper/Specification.lean`, SHA-256
  `9531acd63300aa44359d293b84cc544d40977c6be79c0a87a1d24bcfe410ab15`, compiled
  and was frozen at 2026-10-27T18:12:30Z, before the upper construction. The
  record is `tools/blind_upper_specification_freeze.json`, committed in
  `a4ab54a`. `tools/verify_blind_upper_components.py` pins the hash and requires
  `distribution_blind_upper` to inhabit `DistributionBlindUpperStatement`
  exactly; that proof was accepted at `236eb2d`
  (`results/blind_upper_components_002.json`).
- `lean/ThresholdHC/CriticalUpper/Specification.lean`, SHA-256
  `2e6482ac338da26b5ceaf4bfac38cf63bff401aa934e43ea19f21368625a21ae`, compiled
  and was frozen at 2026-10-28T07:36:44Z, before any critical-upper proof. The
  record is `tools/critical_upper_specification_freeze.json`, committed in
  `2162210`. The statement is not yet proved.
- Authorization: neither freeze record names an approval, and none is claimed
  here.
- Dependency lock, added on 28 October 2026 for review finding 2 on
  [PR 3](https://github.com/davidiach/adaptive-threshold-estimation/pull/3):
  the critical-upper record now also lists the hashes of the specification's
  137 transitive project imports (`dependency_sha256`), and
  `tools/verify_critical_upper_components.py` rejects any change to them. The
  statement bytes are unchanged. The hashes record the dependency state on that
  date, after the unused `CriticalRarePrior` definition was removed, not the
  state at the original freeze time.
