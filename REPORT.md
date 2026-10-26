# Research hill-climb report

## Environment and evidence

The Lean track ran: Lean 4.36.0-rc1 with Mathlib pinned to
`9bdd0bc71aaae0fd83889f9aacd70c32fccd1bcd`. All 33 supplied statements
compiled unchanged and passed their numerical sanity checks. Twelve files
were frozen in commit `8128f9a`. **There are no FREEZE_LOG change entries**:
no target syntax or mathematical meaning was changed. All 50 original input
files match the supplied manifest.

Python 3.12, NumPy 2.4.4, SciPy 1.17.1, mpmath 1.3.0, and Numba 0.68.0 were
used. Dependencies are pinned. Public checkpoint history is at
[davidiach/threshold-hillclimb](https://github.com/davidiach/threshold-hillclimb).

Final proof checkpoint `a485ad6` also passed the independent
[Linux CI run](https://github.com/davidiach/threshold-hillclimb/actions/runs/40410461304):
all 33 frozen targets, the seven additional scalar lemmas, numerical checks,
original input hashes, and locked experiment provenance. The proof score is
therefore reproduced on Windows and Linux.

## A — Lean proofs

**Tier 2 integrated and verified locally, 27 October 2026.** The target set now contains
the original 33 proved targets plus 13 unproved targets worth 61 points. The
validated integration baseline is 60/121 (Tier 1 60/60, Tier 2 0/61). The proposed
Tier 2 mathematical statements are unchanged. Scorer v2 requires a successful,
complete audit and rejects unexpected axioms even when accompanied by `sorryAx`.
The Tier 2 numeric checker requires positive coverage and includes a deterministic
I6 test. See `TIER2.md` and the approval/validation record in `FREEZE_LOG.md`.

**Proved and machine-checked: 0 → 34 → 60/60, all 33 targets.** Checkpoint 002
passed the full build, frozen hashes, exact target types, and independent
audit with exit zero and all 33 reports. The axiom union is exactly
`propext`, `Classical.choice`, and `Quot.sound`. No `sorry` remains in the
Tier 1 proof modules. No Tier 1 targets are parked or unproved. This verifies the
specified targets, not every theorem of the research papers. Evidence is in
`results/lean_score_002.json`, `results/lean_checkpoint_002.json`, and
`results/lean_independent_audit_002.log`.

The original scorer omitted its audit subprocess exit status from validity.
The approved v2 scorer now checks exit status and all 46 target reports directly.
`tools/verify_lean_checkpoint.py` retains the independent audit, consistency
check, and no-regression requirement. Linux CI replays it.

**Full 713 extension: proved and machine-checked.** The separate development in
`lean/ThresholdHC/Uniform713/` proves `full_bound_713` against the exact
`FullBound713Statement` recorded before the final proof. The theorem derives
concentration from independent bounded observations, analyzes the actual capped
classifier and shared-prefix cost, constructs the independent geometric level,
and establishes square integrability, finite expected work, unbiasedness, and
the strict product bound for arbitrary magnitude/sign laws. The model assumes
only measurable independent [0,1] observations with mean 1/2 ± d, 0<d≤1/2, and
integrable 1/d. Bernoulli observations are included. No desired error or moment
bound is assumed. A concrete Bernoulli(1) example verifies that the assumptions
are satisfiable. The separate guard audits 130 public proof roots, checks the
recorded specification hash and all local specification dependency hashes, and
requires the complete theorem in CI. Its guard, manifest, specification, and
definition-bearing dependency files are included in the approved 21-file freeze.

Full proof checkpoint `852690a` passed the independent
[Linux CI run](https://github.com/davidiach/threshold-hillclimb/actions/runs/40414013439):
all 130 proof roots, the exact full theorem type, the original 33 targets,
scalar checks, numerical checks, and provenance locks. This verification is
for that committed checkpoint; later proposals are separate work.

## B — Constants

**Numerical evidence.** Both candidates were chosen from 169 development-only
trials and published in `f4f8e84` before their held-out evaluations.

| Configuration (k1,k2) | Dev proxy | Held-out proxy | Decision |
|---|---:|---:|---|
| Original (1,1) | 6.778762 | 6.771882 | Baseline |
| (0.25,1) | 5.550646 | 5.550060 | ACCEPT |
| (0.25,0.5) | 4.281742 | 4.282069 | ACCEPT on finite grid |

**Proved in Lean; also independently reviewed on paper.** For (0.25,1),
conditional second moment is below 23/d and expected work below 31/d. Thus
the untruncated estimator has
`Var(Y) E[W] < 713 (E[1/D])^2` when `E[1/D]` is finite, improving the supplied
analytic upper constant 12665. See the full
[713 proof](proposals/constants/UNIFORM_PRODUCT_BOUND.md) and
[independent review](proposals/RESEARCH_REVIEW.md). The complete proof is
`lean/ThresholdHC/Uniform713/FullBound.lean`; its audit is
`results/uniform713_status.json`. The earlier seven scalar lemmas remain
separately reproducible. Optimality is not claimed; the lower bound 1/16 and
finite-grid proxy remain different objects.

**Proved counterexample.** The finite-grid winner (0.25,0.5) fails the original
uniform bias bound: at d=0.1 and cap 2^97, a specific all-tails event exceeds
that bound by a factor greater than 2907. Its grid score therefore cannot be
used as a universal guarantee. See [bias audit](proposals/constants/BIAS_AUDIT.md).

## C — Direct-real benchmark

**Numerical evidence — REJECT.** The final candidate was locked in `6eec012`,
then tested once with 500 repetitions per cell. No post-test tuning occurred.

| Budget | Method | RMSE, descriptive 95% interval | Mean work, descriptive 95% interval |
|---:|---|---:|---:|
| 16,384 | GHA | .02990 [.02778,.03204] | 15,893 [15,619,16,167] |
| 16,384 | Direct-real | .03910 [.03260,.04563] | 15,329 [14,467,16,205] |
| 65,536 | GHA | .02012 [.01862,.02159] | 66,847 [65,667,68,031] |
| 65,536 | Direct-real | .02185 [.01838,.02581] | 64,658 [62,853,66,586] |

GHA has the lower point estimate at both budgets; the larger-budget comparison
does not resolve a separation statistically. Constant zero has RMSE .025,
beating both smaller-budget point estimates. Outputs are clipped to [0,1],
and the real-valued variance boundary is heuristic for this unbounded model.

The selected method uses randomized level sums and independent two-success
calibration; it exercises two levels. New training plus tuning cost was
**1,541,656,608 draws**, compared with reused GHA training of 166,827,744 and
GHA-only tuning of 34,093,824. These are amortized comparisons, not equal-total-
cost experiments. Implementation checks covered 71,049 finite tapes, 1,000
telescopes, and 10 repeated-calibration identities. See [Track C](TRACK_C.md)
for raw-error results, seeds, offline-cost breakdown, and calibration proof.

## D — Source audit and remaining theory

**Source comparison.** Lee–Valiant Corollary 19's small-parameter conditions,
Hellinger normalization, and original-prior expected-work denominator match
the supplied note. Its large-gap extension is explicitly a separate argument.
No mathematical correction to the imported input was needed.

**Proved on paper.** Exact power-margin classifier-envelope integrals were
derived for alpha at and above two. A separate argument rules out an exact,
fully uniform unknown-rarity guarantee with no additive error floor, already
for a known fixed gap. Both arguments and their qualifications are in
[Track D](TRACK_D.md). The adaptation argument was independently reviewed.

**Numerical evidence.** Twenty-five deterministic quadrature checks passed;
27 cases evaluate the existing upper bracket. These do not establish a
matching upper theorem for alpha>=2 or arbitrary laws.

## Open work and proposals

- Tier 1 is complete. Prove the 13 new Tier 2 targets, prioritizing the
  stopped-transcript information/testing bounds and atomic rare-event optimizer.
- The full 713 probability theorem is already proved and separately audited;
  adding it to the scored target list remains a separate scope decision.
- The arbitrary-law matching upper bound and matching alpha>=2 constructions
  remain open here. No general distribution-blind theorem is supplied.
- Unknown-rarity algorithms need a qualified guarantee, such as an additive
  floor or restricted parameter range; two-success work calibration alone
  cannot avoid the stated obstruction.
- Scorer v2 incorporates audit exit status directly; the independent audit
  remains a second check under the approved Tier 2 freeze.

No novelty, priority, external-referee endorsement, or universal superiority
claim is made.

The user's ETH preprint was assessed as an indirect algorithmic research lead;
no result here depends on its claimed theorem. See
[relevance assessment](proposals/ETH_PAPER_RELEVANCE.md).
