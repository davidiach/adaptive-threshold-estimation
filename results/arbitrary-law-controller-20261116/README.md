# Full arbitrary-law all-budget controller

[`arbitrary_law_controller`](../../lean/ThresholdHC/ArbitraryLawController/Full.lean)
constructs one observable procedure from known `0 < rho, delta <= 1/4`.
For every probability law of positive gaps there is a deterministic finite
onset, common to every measurable sign law with total positive fraction at
most `rho`. On one event of probability at least `1-delta`, its intervals
cover at every integer budget and have half-width at most
`2^32 C_* K_mu,rho(B/Lambda)` at every budget beyond that onset.
Here `C_* = 6 * plannedCoefficient 28000` and
`Lambda = log(1/delta) + 2 log(2 + log(1+B)/log 2)`.

The controller has unconditional physical caps, consistent finite observed
prefixes, pauses and nested intervals. It selects the largest fitting depth
using the exact pilot reservation and `m_J = 8 ceil(log_2(4J/delta_s)) + 1`,
where `delta_s = delta/((s+1)(s+2))`. If none fits it buys no observations
and returns `[0,rho]`. The continuation uses exactly `m_J` capped copies on
fresh coin labels with the remaining cap, rather than the least admissible
odd count. The checked failure allowance is `delta_s/2`; (A17), the base
budget `4^J/16`, (A18) and the final constant are preserved.

A joint failure lemma charges a bad pilot once and retains its upper
certificate on the same event as coverage. The selected depth tends to
infinity, so the learned law's `2^24` oracle comparison applies after a
deterministic onset. The onset is a theorem quantity, never an input to the
procedure. The same event protects arbitrary observation-dependent stopping
budgets. No candidate family, moment/tail condition, true-law integration
oracle, or assumed stage-risk/coverage guarantee is used.

## Verification identity

- Proof checkpoint: `3f07e30a9a74a3b2b28c24ff5d017d3d60e093b1`.
- Base checkpoint (merge of #113): `f51f962370537ac08e0edc0ba4e2ab253dc40026`.
- Pinned Lean: `v4.36.0-rc1`; Mathlib: `9bdd0bc71aaae0fd83889f9aacd70c32fccd1bcd`.
- [Exact input](controller.lean) and [log](controller.log): 99 independently
  restated exact statements and 99 transitive axiom reports, covering 73
  theorems, 25 definitions/abbreviations and one probability instance.
- [Project closure input](project_closure.lean) and [log](project_closure.log):
  730 project modules, 9,360 constants, 7,615 theorems, 82 instances,
  four of the six registered orphan instances and 1,665 definitions.
- Only `propext`, `Classical.choice`, and `Quot.sound`; no declared axioms or
  offenders. The additive lock update registers 39 definitions, including
  compiler-generated recursive helpers. All 2,334 old entries are unchanged;
  the whole-project lock now has 2,373 entries.
- [Independent kernel replay](kernel_replay.json) passes for all twelve new
  modules. This is not a replay of the whole dependency closure.
- 54 verifier regression tests pass. The source guard checks 1,214 files;
  all 246 frozen hashes in ten manifests pass.

Run `python tools/verify_arbitrary_law_controller.py` to rebuild and repeat
the exact audit. CI additionally replays all twelve modules through the
independent kernel checker and runs the separate whole-project audit.
The [status record](status.json) hashes every proof/audit input, all 730
project sources in the import closure, and the preserved output files.
All 718 reused project sources are byte-identical to the base checkpoint.

## Boundaries

This record is local proof-checkpoint evidence. It does not certify CI on
a later PR head; that status must be checked for the actual commit.
The Lean construction chooses its reference estimator classically and
uses exact reference functionals. Finite-law numerical enclosures, Python
and PRNG execution, practical constants and external specialist review
remain separate. A newly identified manuscript/PDF build and final
publication reconciliation remain tracked in #84. Earlier published
records and PDFs are unchanged.
