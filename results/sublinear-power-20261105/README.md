# Rare power margins below exponent one

For $0<\alpha<1$, write $z(h)=\min\{\rho,(h/a)^\alpha\}$. At every
$B\ge1$ and $0<\rho,\delta\le1/4$ the exact power law has the following
two-sided bounds in the original uniform expected-flip-budget experiment.

| Criterion | Resolution $h$ | Lower coefficient on $z(h)$ | Upper coefficient |
|---|---|---:|---:|
| Root mean squared error | $1/\sqrt B$ | $1/32$ | $512/(1-\alpha)$ |
| Confidence radius | $\sqrt{\log(1/\delta)/B}$ | $1/960$ | $8192/(1-\alpha)$ |

The [upper families](../../lean/ThresholdHC/SubcriticalPower/Upper.lean) are
chosen before the actual law. A bound on its small-gap mass suffices, and
the sign law only has to meet the global rarity constraint. The
[lower proof](../../lean/ThresholdHC/SubcriticalPower/Lower.lean) uses the
actual fractional quantile tail, whose CDF is the reference CDF clipped at
its total mass. The [combined result](../../lean/ThresholdHC/SubcriticalPower/Full.lean)
covers the saturated and unsaturated budgets. [Manuscript Appendix T](../../paper/v6/appendix-sublinear-power.tex)

The [native record](status.json) at the [proof checkpoint](https://github.com/davidiach/adaptive-threshold-estimation/commit/b0c197402f9623cf845f732582fe21f7e9159d9f)
covers 592 modules, including five new modules compiled without warnings.
Of 587 inherited objects, 571 matched earlier published hashes and 16
have their first recorded hashes here. The [five exact statements](sublinear_power.lean)
and [ten transitive axiom reports](sublinear_power.log) passed with only the
standard allowed axioms. Run `python tools/verify_sublinear_power.py` from
the repository root. The logarithmic row at one and the row strictly between
one and two require a different upper construction.
