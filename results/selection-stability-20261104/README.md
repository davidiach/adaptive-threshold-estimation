# Stability and finite approximation of the selection functional

For a probability law on positive gaps, moving probability mass of total
variation at most η changes the selection value by at most η. Mathlib's
variation distance is twice this convention. Rounding gaps upward within
their original bands by a factor of at most r gives a value between K/r and K.
The rounding map may send several gaps to the same point.

The [advance specification](https://github.com/davidiach/adaptive-threshold-estimation/blob/0d2bb966c3e6ba6ea9e7f238687e4ba0e4205c98/lean/ThresholdHC/SelectionStability/Specification.lean)
fixes both statements for the original minimax selection functional. The proof
compares the two laws on their common part and bounds the cost of the residual.
For rounding, a hard selection of rounded gaps pulls back to a hard selection of
original gaps. Within each band, inverse-square costs change by at most r².

For any η > 0 and r > 1, first move the small-gap tail to a positive cutoff,
then round onto a finite grid. If the resulting finite-law value is in [L,U],
the original value is in [max(0,L−η), min(ρ,rU+η)]. One may take L = 5Q/8
and U = Q from the finite-law quantile value. See the
[construction](https://github.com/davidiach/adaptive-threshold-estimation/blob/d48094b796e5d06e7e9f26e139db3656d2c67447/lean/ThresholdHC/SelectionStability/FiniteApproximation.lean)
and the [enclosures](https://github.com/davidiach/adaptive-threshold-estimation/blob/d48094b796e5d06e7e9f26e139db3656d2c67447/lean/ThresholdHC/SelectionStability/Approximation.lean).

The [native record](status.json) identifies all eight compiler invocations.
The isolated build rebuilt seven modules. It reused 79 project modules whose
sources and compiled inputs matched the cited earlier records. The [final
input](ExactAudit.lean) checks five exact statements and the [kernel reports](08.log)
cover 18 declarations with only propext, Classical.choice and Quot.sound.

Run the full check from the repository root with
`python tools/verify_selection_stability.py`.
