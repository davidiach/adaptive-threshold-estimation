# A uniform variance-work upper constant of 713

**Status: proved on paper below, not Lean-checked.** The arithmetic checks in
`uniform_constant_checks.py` verify the rational comparisons, not the full
probability argument. This concerns the theory-compatible candidate
`k1=1/4, k2=1`, not the finite-grid winner `k2=1/2`.

For the original geometric single-term construction with `r=1/sqrt(2)` and
`p_l=(1-r)r^l`, the modified classifier satisfies, for either sign and every
`0<d<=1/2`,

`E[Y_L^2 | d,S] < 23 min(sqrt(2^L),1/d)`,

`E[W_L | d,S] < 31 min(sqrt(2^L),1/d)`.

Here J is sampled independently of the coin and its observations,
`Y_L=1[J<=L] Delta_J/p_J`, and `W_L` is zero when J>L and otherwise
the number of shared-prefix observations needed for that increment.

Consequently, whenever `I=E[1/D]<infinity`, the untruncated estimator is
unbiased and has `Var(Y) E[W] < 713 I^2`. The bound is uniform in the
magnitude law and sign function; it does not identify the optimum constant.
It improves the supplied analytic upper bound 12665. It does not equate
the finite-grid value 5.5501 with a universal bound.

## 1. A uniform error envelope

The proof in `BIAS_AUDIT.md` gives, with `x=Nd^2`,

`e_N <= exp(-2x)+(2/3)exp(-1/2)x^(-2)`.

For `x>=1`, `x^2 exp(-2x)<=exp(-2)`. Write
`B=exp(-2)+(2/3)exp(-1/2)`.
The positive Taylor series gives `exp(2)>7` and `exp(1/2)>8/5`, hence

`B < 1/7+5/12 = 47/84 < 3/5`.

For every x>0, `x^2 exp(-2x)<=exp(-2)` because that function has its global
maximum at x=1. The original displayed error sum therefore yields
`e_N <= B x^(-2)` for **all x>0**, including x<1. Consequently the union
bound on fine and coarse errors gives
`E[Delta_l^2] <= min(1,5B x^(-2)) <= min(1,3x^(-2))`
for all levels l>=1, with `x=2^l d^2`.
At level zero, `Delta_0=Z_1`, and `d^2<=1/4` makes the same envelope equal
to one, so it covers that level as well.

## 2. Second moment

The geometric series comparison from the v4 proof, with the threshold scale
replaced by `d'=d/3^(1/4)`, gives

`E[Y_L^2] <= C0 min(sqrt(2^L),3^(1/4)/d)`,

where

`C0 = (1-r)^(-1) [(1-r)^(-1)+(1-r^3)^(-1)] < 17`.

For completeness, `E[Y_L^2]=sum_{l<=L} E[Delta_l^2]/p_l`. Before
`2^l(d')^2=1`, bound the sum of `sqrt(2^l)` by
`(1-r)^(-1)min(sqrt(2^L),1/d')`. After that scale, the summands are bounded
by a geometric sequence with first term at most `1/d'` and ratio `r^3`.
This proves the displayed comparison, including when the cutoff precedes
the split. Since `3^(1/4)<4/3`, the constant is less than `68/3<23` after
replacing `min(sqrt(2^L),3^(1/4)/d)` by
`3^(1/4)min(sqrt(2^L),1/d)`.

The rational bound `r<442/625` follows by squaring. Substituting that upper
bound into the increasing rational expression for C0 proves C0<17 by
integer arithmetic.

## 3. Expected classifier work

Let `c=13/7` and `t=sqrt((1/4+log(N/n))/n)`.
If the classifier survives a dyadic prefix n<N and `d>c t`, its empirical
mean deviates in the direction opposite the true sign by more than
`(1-1/c)d`. One-sided Hoeffding therefore yields

`P(tau_N>n) <= 1[d<=c t] + exp(-2(1-1/c)^2 n d^2)`.

Suppose `x=Nd^2>=1` and put `u=nd^2`. The indicator's condition implies
`u<=c^2[1/4+log(x/u)]`.
If `u<1`, trivially `u<=1+c^2 log x`. If `u>=1`, use `log u>=0` and
`c^2/4=169/196<1` to obtain the same conclusion.
The dyadic sum of n with this property is at most
`2d^(-2)[1+c^2 log x]`.

For every b>0 and a dyadic sequence, comparison on disjoint intervals
`[n/2,n]` gives `sum n exp(-b n d^2)<=2/(b d^2)`.
Apply this with `b=2(1-1/c)^2`. The survival identity
`E tau_N=1+sum_{n<N} n P(tau_N>n)` and `1<=d^(-2)/4` now give

`E tau_N <= d^(-2)[125/18+(338/49)log x]`

`             <= 7 d^(-2)(1+log x)`.

The deterministic bound tau_N<=N handles x<1 and gives
`E tau_N <= 7 m_N(d)`, with the same m_N as in v4.

## 4. Coupled work and the final product

On a shared stream, the cap-N threshold is at least the cap-(N/2)
threshold at every prefix before N/2. If the fine classifier stops there,
the coarse classifier has also stopped by then. If it stops at or after
N/2, the coarse classifier has already reached its cap. Thus, pathwise,

`tau_(N/2)<=tau_N`, and `W_l=max(tau_N,tau_(N/2))=tau_N`.

This removes the factor two from the sum-of-stopping-times bound in v4.
It also covers level zero, whose work is one. Consequently

`E W_L <= 7(1-r) sum_{l<=L} 2^(-l/2) m_(2^l)(d)`.

Split at `2^l d^2=1` as in v4. The prefix has constant 1. In the tail,
the first x lies in (1,2], so its summands are bounded by
`d^(-1)r^k(1+log2+k log2)`. Summing yields

`E W_L <= 7[2+log2/(1-r)] min(sqrt(2^L),1/d)`.

Using `r<71/100` and `log2<7/10` gives
`7[2+log2/(1-r)] < 7(2+70/29)=896/29<31`.

Finally, integrate the conditional bounds and let L increase. The sums of
nonnegative second moments and expected costs converge; finite second
moment supplies integrability. More explicitly, for the untruncated Y,
`E[(Y-Y_L)^2]=sum_{l>L} E[Delta_l^2]/p_l -> 0`, so the convergence is
in L2 and hence in L1. The telescoping expectations converge to
the true sign since e_N tends to zero, giving unbiasedness after averaging
over the magnitude and sign. Variance is no greater than second moment,
so `Var(Y) E[W] < (23 I)(31 I)=713 I^2`.
