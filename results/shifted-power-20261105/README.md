# Logarithmic and intermediate rare power margins

For $1\le\alpha<2$, let $f_1(x)=\min\{\rho,x[1+\log_+(\rho/x)]\}$
and $f_\alpha(x)=\min\{\rho,\rho^{1-1/\alpha}x\}$ above one.
Both sides now hold in the original observable experiment at every
positive budget. The RMS resolution is $x=1/(a\sqrt B)$.
The confidence resolution is $x=\sqrt{\log(1/\delta)/B}/a$.

| Criterion | Lower coefficient on $f_\alpha$ | Upper coefficient |
|---|---:|---:|
| Root mean squared error | $1/32$ | $C_\alpha$ |
| Confidence, expected budget | $1/960$ | $27C_\alpha$ |
| Confidence, hard observation cap | $1/960$ | $27C_\alpha$ |

Here $0<a\le1$ and $0<\rho,\delta\le1/4$, with lower bounds for the
exact power law. The original paper range $a\le1/4$ is included. Every
upper family is selected before the actual law and works across the
power margin class. The interval radius uses the global rarity bound,
without a pointwise sign-prior bound.
[Complete theorem](../../lean/ThresholdHC/ShiftedPower/Full.lean) ·
[Manuscript Appendix U](../../paper/v6/appendix-shifted-power.tex)

Write $W_\alpha=68(\alpha+2)/(2-\alpha)^2$.
The explicit upper coefficient is
$C_1=1+20\sqrt{204}\le287$ at one and
$C_\alpha=1+8\sqrt{W_\alpha}/(1-2^{(1-\alpha)/2})$ above one.
Thus $287$ and $7749$ suffice for the two upper criteria at one.
[Constants](../../lean/ThresholdHC/ShiftedPower/Constants.lean)

The [Poisson-allocation controller](../../lean/ThresholdHC/ShiftedPower/Allocated.lean)
runs a finite shifted telescope with independent coins and a mean count
fixed from the envelope. Its work is the number of flips purchased.
The shared-prefix difference moments, law-independent allocation,
truncation choice and deterministic cap for confidence are included.

The [native record](status.json) at the [proof checkpoint](https://github.com/davidiach/adaptive-threshold-estimation/commit/ba2bc76940ad473068f7b05fcf4cf2a5ac861a58)
covers 664 modules. All 18 new modules compiled without warnings.
Of 646 inherited objects, 645 match earlier published hashes and one
has its first recorded hash here. [Ten exact statements](shifted_power.lean)
and [35 transitive axiom reports](shifted_power.log) passed using only
the standard allowed axioms. Run `python tools/verify_shifted_power.py`.
