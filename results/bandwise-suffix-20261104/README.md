# Finite-law bandwise-suffix theorem

For every probability law with finite support on $(0,1/2]$, $0<\rho\le1/4$
and $B>0$, a hard restriction to a subset of the support attains the minimum
over all submeasures. Within each canonical dyadic band the selected atoms
form an upper-gap suffix. Clipping this optimizer's objective at $\rho$
gives the original selection value $K$.

The [statement](https://github.com/davidiach/adaptive-threshold-estimation/blob/a2ee4e83f985d942297639d12712c278e89a7421/lean/ThresholdHC/BandwiseSuffix/Specification.lean)
was committed before the proof. On a finite support, the existing hard-selection
identity gives an attained hard optimum. Moving an equal quantity of inverse-square
cost from a selected atom to a skipped larger atom in its band leaves every band
cost unchanged. The saved tail cost per unit increases strictly with the gap.
The [theorem](https://github.com/davidiach/adaptive-threshold-estimation/blob/c15a9fa46a5f0a743fb20416b87498225a13661e/lean/ThresholdHC/BandwiseSuffix/Full.lean)
therefore rules out every such inversion at an uncapped hard optimum.

The [search corollary](https://github.com/davidiach/adaptive-threshold-estimation/blob/c15a9fa46a5f0a743fb20416b87498225a13661e/lean/ThresholdHC/BandwiseSuffix/Search.lean)
shows that at most $\prod_j(n_j+1)$ candidates suffice when occupied band $j$
contains $n_j$ atoms. For example, 60 atoms in one band give at most 61
candidates. With one atom per occupied band the bound is exponential.

The [native record](status.json) contains all 9 successful compiler
commands, their input hashes and the output artifact hashes. The isolated run
rebuilt 8 project modules, including the two original
hard-selection proof dependencies `Superadditive` and `HardSelection`. The
other 39 project sources and compiled inputs matched the
[previous record](../entropy-tail-explicit-20261104/status.json). It used the
pinned external dependency cache. The [final input](ExactAudit.lean) checks five
exact statements. The [kernel reports](09.log) cover 23 declarations and
use only `propext`, `Classical.choice` and `Quot.sound`.

From the repository root run

```sh
python tools/verify_bandwise_suffix.py
```
