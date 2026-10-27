# Tier 6: an algorithm-level minimax lower bound

The eight-hour-or-landmark goal began on 2026-10-27 at 08:59:52 UTC.
The target is the explicit arbitrary-law bound

$$
R_\mu(B)\ge \frac1{64}\,\omega_\mu(B^{-1/2}),\qquad
\omega_\mu(h)=\int\min\{1,h/d\}\,\mu(dd),\qquad B\ge1.
$$

The coefficient is the fixed target, not an optimality claim. This is
the lower-bound side of the paper's minimax law; the matching statistical upper
bound is a separate formalization task.

## Exact algorithm model

The magnitude law is any probability measure on `Gap = {d : Real // 0 < d and
d <= 1/2}`. It may have atoms or a singular component and need not have a finite
inverse moment. `SignLaw` ranges over every measurable function from `Gap` to
`[0,1]`.

An `AdaptiveEstimator` has an arbitrary measurable random-seed space and a
probability law for that seed. Its policy chooses any natural-number coin label
or stops, based on the seed and previous Boolean observations. It may create,
revisit, and interleave coins without a fixed cap. Its output is any measurable
real function of the seed and the full padded observation tape. Both the policy
and output are fixed across sign laws.

The hidden magnitudes form an independent countable product with law `mu`,
independent of algorithm randomness. Policy and output cannot inspect that
hidden environment. We retain it in the augmented transcript only when applying
the stronger Tier 5 information bound.

`UniformBudget` bounds expected total observations under every sign law.
Squared error is a nonnegative extended-real integral, and RMS error is its
square root. Infinite risk is retained. `minimaxRisk` takes the infimum over all
measurable seed spaces and all admissible estimators of the supremum of RMS
error over sign laws.

## Canonical process and proof route

The process is explicitly constructed using Ionescu--Tulcea. Coordinate zero
stores the common seed; subsequent coordinates store observations or a stop
symbol. The transition probability is the child-cylinder mass divided by its
parent-cylinder mass. At a zero-mass history it defaults to stopping; the
proved cylinder consistency ensures that this choice changes no positive-mass
event. Kernel normalization and measurability are proved.

The crucial process target derives all bounded finite-prefix integral
identities for this construction. The algorithm-level theorem does not assume
`RealizesCreationPrefixes`, an entropy limit, absolute continuity, or a testing
bound.

For `h = 1/(4 sqrt B)`, the hard pair uses
`eta(d) = min(1,h/d)/8` and sign probabilities `1/2 +/- eta(d)`.
Its parameter separation is `omega_mu(h)/4`, at least
`omega_mu(1/sqrt B)/16`. Tier 5 bounds full KL by `8/225`, below `1/8`.
A separate actual-measure two-point theorem gives RMS risk at least one quarter
of the separation, yielding the coefficient `1/64`.

An immediate-stopping estimator witnesses that the budget class is nonempty.
Its worst-case RMS risk is at most one. This checks that the minimax definition
is not an infimum over an empty class.

## Targets and validation

The eleven targets are general canonical-process realization, population
realization, hard-pair validity and separation, modulus scaling, budget-scale
separation, a two-point risk inequality, budget-class nonemptiness, the bound
for each admissible algorithm, the minimax bound, and their combined theorem.

The specification import closure, target manifest, verifier, and all prior lock
manifests are frozen before accepting a proof checkpoint. The separate Tier 6
guard checks exact statement types, source hashes, and declaration axioms.
Only `propext`, `Classical.choice`, and `Quot.sound` are allowed. Nine regression
tests exercise the guard's failure cases, including structure registration.

Run `python tools/verify_tier6.py --sequential --require-complete` for the full
landmark. A partial checkpoint must list pending targets and cannot claim
completion. Earlier specifications and verification guards remain unchanged.

The 38-file `TIER6_FROZEN.sha256` lock covers the exact specification import
closure, target manifest, verifier, and all four prior lock manifests. All three
proof agents reviewed the model and target interfaces before the lock.

The first selected-foundations audit passes **5/11 exact targets and 100/100
declaration checks**, with every audited source unchanged. The five targets are
hard-pair validity and separation, modulus scaling, budget-scale separation, and
the two-point risk theorem. Evidence is in
`results/tier6_foundations_status.json` and
`results/tier6_foundations_audit.log`.

The general process-realization bridge and the final algorithm/minimax theorems
remain pending. No completed Tier 6 landmark is claimed in this checkpoint.
