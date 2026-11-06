# Arbitrary-law adaptation: formalization scope

The [arbitrary-law adaptation theorem](ARBITRARY_LAW_ADAPTATION.md) has a
paper proof. The new `ThresholdHC.ArbitraryLawAdaptation` namespace formalizes
components of that proof; it does not yet contain its full statistical theorem.
Python execution is outside the Lean verification claim.

## Finite entropy transport

For a nonnegative finite cost vector, write
`G(a) = A + sum negMulLog(a_i) - negMulLog(A)`, where `A = sum a_i`.
[EntropyTransport.lean](../lean/ThresholdHC/ArbitraryLawAdaptation/EntropyTransport.lean)
proves a cross-entropy bound allowing zero reference weights off the cost
support, the normalized reference identity, a rowwise transport inequality,
and entropy decrease under arbitrary finite merging. In particular, if
`sum_k f_(i,k) <= a_i`, `b_(i,k) <= r_k f_(i,k)`, `r_k <= 1`, and a positive
reference subprobability satisfies `r_k (-log p_k) <= L`, then
`G(b) <= G(a) + L A` for nonnegative `a`, `f`, and `b` and `L >= 0`.

[BandPenalty.lean](../lean/ThresholdHC/ArbitraryLawAdaptation/BandPenalty.lean)
specializes to `r_k = min(1, 4 (1/4)^k)` and `p_k = (1/2)^(k+1)`.
It proves `r_k (k+1) <= 2`, the finite geometric normalization, the coding
penalty bound, and `G(b) <= 3 G(a)`. The sizes of both finite index sets are
arbitrary. The pushforward theorem allows merging cells into their actual
destination bands.

Run `python tools/verify_arbitrary_law_entropy.py` to compile these modules
and audit 15 independently restated exact statements and their transitive
axioms. The audit permits only `propext`, `Classical.choice`, and `Quot.sound`.
The proof-source guard is `python tools/verify_lean_sources.py`.

The [native audit record](../results/arbitrary-law-entropy-20261106/README.md)
identifies the exact proof checkpoint, sources, compiler and reused objects.

## Finite CDF envelope

[CDFEnvelope.lean](../lean/ThresholdHC/ArbitraryLawAdaptation/CDFEnvelope.lean)
constructs a measure on the real line from cumulative upper bounds. Taking
prefix minima preserves the finite grid bounds and makes the weights
nonnegative. The finite measure has total mass one when the first bound is
one, and its zero atom has exactly the remaining tail mass. Lean proves its
closed-CDF formula, including the preceding-bound value at each positive grid
atom, and CDF domination of every nonnegative probability law satisfying the
finitely many supplied grid bounds. No condition is imposed at unprobed cutoffs.

Run `python tools/verify_arbitrary_law_envelope.py` for 25 exact statements
and 24 transitive axiom reports. The hypotheses are deterministic finite grid
bounds; the pilot's probability guarantee for those bounds remains to be proved.

The [native envelope record](../results/arbitrary-law-envelope-20261106/README.md)
preserves its proof checkpoint, exact audit input, axiom reports and empty
compilation log.

## Observable learning stage

[LearnedStage.lean](../lean/ThresholdHC/ArbitraryLawAdaptation/LearnedStage.lean)
constructs an observable stage from a fixed paid pilot, a rule turning its
observed word into the finite envelope above, and a continuation selected by
that envelope. The pilot and continuation use disjoint persistent coin labels.
Lean proves that the continuation receives untouched tapes and that the output
computed from the chronological observed history equals the table construction.
The learned law is a probability measure on every observed word; CDF domination
follows on the finite grid event. Both endpoints share one policy and obey the
unconditional physical cap
`pilotCost + continuationCost`. Their joint output law is identified in the
original hidden-gap experiment, with arbitrary measurable gap-dependent signs.

Run `python tools/verify_arbitrary_law_stage.py` for 17 exact statements and
16 transitive axiom reports. This is a reusable execution construction. It
does not instantiate the statistical pilot or robust continuation, or assume
their desired risk bounds in place of proving them. It is a single stage,
not yet the final all-budget confidence controller.

The [native stage audit](../results/arbitrary-law-stage-20261106/README.md)
identifies the 644-source project closure, exact statements and compiled
dependency hashes. Across all three component audits, 57 exact statements
and 55 transitive axiom reports pass.

## Work still needed for the full theorem

The finite matrix inequality is not yet the arbitrary-measure transport
theorem. Remaining work includes countable entropy limits, construction of
transported selections and their domination, the light random contraction,
and the entropy functional's treatment of unresolved mass at zero. The finite
CDF envelope is checked, but still needs its statistical pilot event and
law-dependent onset. The observable stage is checked as an execution component;
the concrete pilot and robust continuation must be instantiated and their
statistical bounds proved. Finally the stages need to be joined into the
all-budget controller, with fresh stages, nested intervals, simultaneous
coverage and eventual oracle width. These conclusions must be proved, not
supplied as assumptions to a controller interface.
