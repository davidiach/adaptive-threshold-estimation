# Overnight brief: hill-climbing the adaptive threshold research

You are improving a research project on adaptive threshold estimation: the
v4 paper plus the next-phase rare-event note. Work unattended. Improve
**only** what a machine can check. Never improve a score by weakening what is
being checked.

Inputs you already have:
- v4 package: `Adaptive_Threshold_v4/` (paper source `source/paper.tex`, code);
- next-phase package: `Adaptive_Threshold_Next_Phase/` (rare-event note,
  benchmark harness).

This kit adds frozen targets, scorers and cheat checks.

## Ground rules (apply to every track)

1. **Frozen means frozen.** Files listed in `FROZEN.sha256` (after Phase 0)
   may not change: target statements, target list, scorers, grids, lake files.
   If you believe a frozen item is wrong, write the case in
   `proposals/<name>.md` and move on. David decides.
2. **Hill-climb protocol.** Work in git.
   - Commit the baseline.
   - For each attempt: make a change, run the track's scorer with
     `--accept <previous best>`.
   - Commit only on ACCEPT. On REJECT, revert (`git checkout -- .` for
     tracked files).
   - Append one line per attempt to [RUNLOG.md](docs/process/RUNLOG.md), accepted or not.
3. **No unverifiable claims.** Every statement in your report must be one of:
   - proved and machine-checked (Lean score);
   - proved on paper (give the proof);
   - numerical evidence (give the script and seed);
   - conjecture.

   Label which. Never upgrade a label.
4. **Held-out discipline.** Tune on dev or tuning data only. Held-out sets are
   for acceptance and the final report. Do not inspect held-out errors to
   choose the next change.
5. **Stop rules.** If a target or idea gets no ACCEPT after about 90 minutes of
   effort, park it with notes in `proposals/stuck.md` and move on. Commit after
   every ACCEPT so nothing is lost if the run ends.

## Phase 0: environment and freeze (do first, about 1 hour max)

The Lean track needs network access to GitHub and Mathlib's build cache. It
also needs roughly 5 GB of disk and 8 GB or more of RAM. If your environment
cannot install Lean or download the Mathlib cache, skip Track A, say so at the
top of the report, and run Tracks B to D.

1. `bash lean/setup.sh`
2. The target statements in `lean/ThresholdHC/Statements.lean` were written
   without a compiler. The author's environment could not reach Mathlib's
   cache. Every statement has been checked numerically and is believed true;
   see `tools/check_targets_numeric.py`.
   - If any statement fails to **elaborate**, fix only the syntax or names
     needed, without changing its mathematical meaning.
   - Log every such edit in `FREEZE_LOG.md` (before, after, why).
   - Never change a statement because it is hard to prove.
3. `python tools/check_targets_numeric.py` must report all 33 targets
   consistent.
4. `python tools/freeze.py --init`, then `python tools/score.py`. Expect
   `valid=True points=0/60`.
5. `git init && git add -A && git commit -m "Phase 0 baseline"`. Copy
   `results/lean_score.json` to `results/lean_best.json`.

## Track A (main): machine-check the v4 lemmas in Lean 4 + Mathlib

There are 33 frozen targets worth 60 points, in groups A–H, listed in
`tools/targets.json`. Each target is a `def ... : Prop` in
`ThresholdHC.Targets`. Prove it as
`theorem ThresholdHC.Proofs.<name> : ThresholdHC.Targets.<name>` in
`lean/ThresholdHC/Proofs/<Group>.lean`. Each target's docstring names the v4
lemma it comes from; the paper proofs are in `source/paper.tex`.

**Scoring:** `python tools/score.py --accept results/lean_best.json`.

A target counts only if all of the following hold:
- the build passes;
- the scorer's freshly generated audit theorem typechecks against the frozen
  statement;
- `#print axioms` shows only `propext`, `Classical.choice` and `Quot.sound`.

`sorryAx` means unproved. Any other axiom zeroes the score.

These are forbidden anywhere in proof files: `axiom`, `native_decide`,
`implemented_by`, `extern`, `unsafe`, `opaque`, `debug.*`/`skipKernelTC`,
custom `elab`/`macro`/`syntax`, `run_cmd`, `#exit`. Helper lemmas and new
helper modules under `Proofs/` are fine. Keep every unproved target as
`sorry` so the build always passes.

On ACCEPT, copy `results/lean_score.json` to `results/lean_best.json` and
commit.

Suggested order is easy points first, then the high-value targets:
- **D1–D3, A1–A5, F1–F2, G3, H1, H2:** algebra. Try `field_simp`, `ring`,
  `nlinarith`, `positivity`, `min` case splits.
- **E1–E3:** geometric series in Mathlib: `tsum_geometric_of_lt_one`, and
  `HasSum` for `∑ (n+1) r^n` and its relatives.
- **G1, G2, G4:** bounds on `√2` and `log 2`. Mathlib has
  `Real.log_two_lt_d9` and `Real.log_two_gt_d9`.
- **C1–C4:**
  - C1: substitute `r = √(x/y)`, show `g(r) = log r - 2(r-1)/(r+1)` is monotone, and use `g(1) = 0`.
  - C2: use `log t ≤ t - 1` termwise.
  - C3: sum C1.
  - C4: Cauchy–Schwarz over `Fin n`.
- **B1** (Taylor bound for Bernoulli KL) unlocks **B2, B3, B5**. B2 follows
  B1 + A4 + A5 exactly as in the Lemma 3 proof. B4 is a limit computation.
- **F3–F5, H3, H4:** integrals and series. These are the hardest; H3/H4
  follow the dyadic-interval comparison in v4 Lemma 6.

Possible extension, for proposals only and not scored: draft Lean statements
for the stopped-transcript KL bound (Proposition 5) and for the rare-event
lemmas of the next-phase note. Put them in `proposals/` for David to approve
as new frozen targets.

## Track B (cheap, in parallel): tighten the variance–work constant

The objective is an exact-recursion proxy for `sup V·W / I_μ²` of the
unbiased estimator:
- v4 proves 12665;
- the exact value at v4's settings is about 6.78 on the frozen grid;
- the universal lower bound is 1/16.

**Score:** `python constants/score_constants.py constants/candidate.json --accept results/constants_best.json`

The scorer accepts only strict improvements on both dev and held-out grids,
with the v4 bias bound still holding.

**Allowed:** edit `constants/candidate.json` (`k1`, `k2` within the bounds in
`grid.json`). A first probe already found `k2 = 0.7` gives 5.95.

**Radical designs** (other stopping schedules, level laws, randomized ties)
cannot be scored by the frozen evaluator. Implement them in
`proposals/constants/` with their own exact evaluator, and compare them
honestly to the frozen baseline. Any winner eventually needs an analytic
constant (a lemma or a Lean target), and the report should say how far that
is.

## Track C (practical): a real-valued method on the Giles–Haji-Ali model

The next-phase benchmark (`Adaptive_Threshold_Next_Phase/code/benchmark.py`)
showed tuned GHA winning: RMS error 0.0201 at about 65k observations, against
0.0492 for tuned v4. But v4 had to discard information through a Bernoulli
conversion.

**Goal:** a v4-style method that uses the real-valued observations directly
and beats tuned GHA on held-out runs at both 16,384 and 65,536 budgets. The
v4-style method keeps the multilevel randomization and the two-success
calibration, and uses a sequential sign test on real-valued means, such as an
empirical-Bernstein or variance-adaptive stopping rule.

Rules:
- Reuse that harness's train, tune and test stages and its seeds.
- Tune on tuning replications only.
- Run the held-out test once per final candidate.
- Report offline training costs separately, as the harness already does.
- Do not compare against constant estimators without noting that constant
  zero scores 0.025 here.

If GHA still wins, report that.

## Track D (research, only after A has stalled or with a spare agent)

From the next-phase note. These are not hill-climbable; deliver proofs with
status labels.

1. **Verify the imported input verbatim.** Check Lee–Valiant Corollary 19
   (arXiv:1904.09228v3) against the note's Lemma "Published single-coin
   input": conditions, Hellinger normalization, and the expected-work form.
   Fix the note if anything differs.
2. **Matching upper bound for Ψ.** Start with power margins α ≥ 2, where Ψ
   predicts roughly `(h/a)√ρ` (with a `√log` factor at α = 2). Upper
   constructions may know (α, a, ρ). Test conjectured rates against small
   exact or numerical instances before attempting a proof.
3. **ρ-adaptive or distribution-blind rare-event algorithm.** Begin by asking
   whether the two-success calibration plus a data-driven start level can
   replace knowledge of ρ.

## Morning report: [REPORT.md](docs/process/REPORT.md)

1. **Environment:** whether Track A ran; any `FREEZE_LOG.md` entries, quoted
   in full.
2. **Track A:** score before → after, targets proved, targets parked with the
   reason, and the final `#print axioms` summary.
3. **Track B:** best configuration, dev and held-out products, and how far it
   is from a provable constant.
4. **Track C:** the held-out table with mean work and descriptive intervals,
   offline costs, and the honest verdict.
5. **Track D:** each claim with its status label.
6. **Proposals and stuck items** for David to decide.

Keep the report short. Evidence lives in the repo.
