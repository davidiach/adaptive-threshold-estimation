# A 31/20 upper bound for quantile selection

For every positive-gap probability law, rarity $0<\rho\le1/4$ and budget
$B>0$, the [Lean theorem](../../lean/ThresholdHC/QuantilePrice/Full.lean)
shows $K\le Q\le (31/20)K$ on the original statistical selection functional.
Its [reference weights](../../lean/ThresholdHC/QuantilePrice/Weights.lean)
give the separated-cost coefficient $16/9$. The [scalar inequality](../../lean/ThresholdHC/QuantilePrice/Scalar.lean)
combines the entropy bounds with the ordinary observation cost.

The [native build record](status.json) identifies the pinned compiler and 69
project dependencies. It checks the hashes of 63 reused artifacts and rebuilds
six project modules. The [exact audit](ExactAudit.lean) checks six statements,
including the earlier $8/5$ comparison after its proof was generalized. All
31 [axiom reports](07.log) use only propext, Classical.choice and Quot.sound.

Run `python tools/verify_quantile_price_upper.py` from the repository root.
The [sharp root characterization](../../docs/OPTIMAL_QUANTILE_FACTOR.md) has a
separate paper proof and a rational numerical certificate.
