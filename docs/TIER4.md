# Tier 4: full infinite-transcript relative entropy

The eight-hour-or-landmark goal began on 2026-10-27 at 07:48:45 UTC.
The intended landmark is a complete kernel-checked bound for the actual joint
law of the random seed and the infinite observation tape, with independent
Linux verification. This document records Tier 4 separately from concurrent
repository documentation work.

## Locked target

The six targets in `tools/tier4_targets.json` require:

1. Equality between the measure-theoretic KL of the joint seed/prefix law and
   the previously proved conditional finite-sum KL.
2. Equality between full infinite-transcript KL and the supremum of all finite
   joint-prefix KL values.
3. The full bound `KL(P_transcript, Q_transcript) ≤ (128/225) h² E_P[work]`.
4. Finiteness, absolute continuity, and integrability of the log-likelihood ratio.
5. The same bound for every measurable statistic of the seed and full tape.
6. A combined theorem containing all five statements.

The KL is Mathlib's extended-real `InformationTheory.klDiv`, not a definition
by finite-prefix supremum. Expected work need only be finite under the plus
hypothesis. Seeds have arbitrary measurable probability laws. The coin family
is fixed and finite, as in Tier 3. The realization condition specifies the
actual joint finite-prefix laws and assumes no entropy identity or bound.

All three proof agents reviewed the statements before the ten-file
`TIER4_FROZEN.sha256` lock was created. The lock includes the prior lock manifests
and the new checker. Earlier mathematical statements remain unchanged.

## Proof route

The generic entropy lemmas use the nonnegative KL integrand on increasing
measurable restrictions. Finite expected work gives almost-sure halting under
both hypotheses. On each stopped event, the prefix and seed reconstruct the
entire tape by padding with `none`. Restriction and data processing inequalities
then identify infinite KL with the finite-prefix supremum. A separate density
calculation identifies finite joint KL with the existing conditional information
integral, after which the prior work bound applies.

## Verification

Specification modules and the generic entropy/bound-reduction modules compile.
The eight audit regression tests pass. No completed Tier 4 target is claimed at
this initial foundations checkpoint; the specialized bridges remain in progress.

Run `python tools/verify_tier4.py --sequential --require-complete` for the complete
audit. A partial checkpoint must omit `--require-complete` and explicitly report
pending targets. Only `propext`, `Classical.choice`, and `Quot.sound` are accepted.
