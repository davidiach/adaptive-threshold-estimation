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

## Work still needed for the full theorem

The finite matrix inequality is not yet the arbitrary-measure transport
theorem. Remaining work includes countable entropy limits, construction of
transported selections and their domination, the light random contraction,
and explicit treatment of unresolved mass at zero. The learned CDF envelope
also needs its statistical pilot event and law-dependent onset. Finally the
robust continuation must be joined to the observable controller, with its
original experiment law, physical cap, fresh stages, and simultaneous
all-budget coverage and oracle width. These conclusions must be proved,
not supplied as assumptions to a controller interface.
