# Sharper bounds on the quantile-to-selection factor

For the functional and quantile value in the [certified-selection note](../research/2026-10-30-certified-selection/NOTE.md),
every probability law on $(0,1/2]$, $0<\rho\le1/4$, and $B>0$ satisfies
$$
 K\le Q\le \frac{31}{20}K .
$$
A five-atom law has $Q/K>1.46255$. Thus the optimal universal factor lies
strictly above $1.46255$ and at most $1.55$. A [subsequent characterization](OPTIMAL_QUANTILE_FACTOR.md)
identifies its exact value as a scalar root. The argument below proves the
$31/20$ upper bound. Its [Lean proof and audit](../results/quantile-price-20261104/README.md)
cover arbitrary positive-gap laws.
The [arithmetic verifier](../tools/verify_quantile_price_bounds.py) checks the
rational inequalities and evaluates the lower example with rational log and
square-root enclosures.

## A separated cost coefficient of 16/9

Write $C=16/9$. For a measure $\xi$ supported at gaps at least $t>0$, index
the bands from the one containing $t$ outwards to larger gaps. The possible
ratios $d/t$ in band $j$ are bounded below by
$m_0=m_1=1$, $m_j=2^{j-1}$ for $j\ge2$. Use reference weights
$\pi_j=\exp(1-Cm_j)$. For $E(x)=\sum_{k=0}^8 x^k/k!$, the positive exponential
series gives $E(x)\le e^x$ for $x\ge0$. Since $2^{j+2}\ge4+4j$,
$$
 \sum_j\pi_j
 \le\frac{2}{E(C-1)}+\frac{1}{E(2C-1)}
     +\frac{1/E(4C-1)}{1-1/E(4C)}<1.
$$
The last inequality is rational. If $a_j$ is the inverse-square cost in
band $j$, the entropy inequality for subprobability weights gives
$$
 \Gamma_\xi\le\sum_j a_j(1-\log\pi_j)
   =C\sum_j m_j a_j\le (C/t)\int d^{-1}\,\xi(dd).
$$
This follows on every finite prefix, including the zero-cost case, and hence
for the prefix supremum.

## The scalar price

For $T,v,c\ge0$, put $z=\sqrt{Tc}$, $k=31/20$, $a=37/40$ and $b=77/80$.
We claim
$$
 T+\sqrt{(v+az)^2+(bz)^2}\le k\big(\sqrt{T^2+v^2}+c\big). \tag{1}
$$
Represent the norm on the left by the maximum of $x(v+az)+ybz$ over
$x,y\ge0$ with $x^2+y^2=1$. For each such pair,
$(ax+by)\sqrt{Tc}\le (ax+by)^2 T/(4k)+kc$. Cauchy–Schwarz proves (1)
once
$$
 \left(1+\frac{(ax+by)^2}{4k}\right)^2+x^2\le k^2.
$$

Here is a rational certificate for this last inequality. Homogenizing and
clearing denominators reduces it to $P(x,y)\ge0$, where
$$
 P(x,y)=16k^4(x^2+y^2)^2-[4k(x^2+y^2)+(ax+by)^2]^2-16k^2x^2(x^2+y^2).
$$
Set $w=y-x/3$ and expand $P(1,w+1/3)=Aw^4+Dw^3+Fw^2+Gw+H$.
In descending order the five coefficients are
$$
 \frac{340512227}{8192000},\quad\frac{922920889}{30720000},\quad
 \frac{551277971}{12288000},\quad\frac{255898057}{276480000},\quad
 \frac{177573199}{3317760000}.
$$
Exact multiplication gives $A>0$, $24A>D^2$, $F>6$ and
$4(F-6)H>G^2$. Consequently
$$
 P(x,y)=w^2(Aw^2+Dwx+6x^2)+x^2((F-6)w^2+Gwx+Hx^2)\ge0.
$$
This argument also covers $x=0$ and every zero-price boundary.

## Comparison with an arbitrary selection

Let $h=B^{-1/2}$ and split the law at its lower $\rho$ quantile $t$ into
tail $\nu$ of mass $\rho$ and core $\kappa$, including the fractional split
of a boundary atom. Write $T=\int\min(1,h/d)\,d\nu$. For $h\ge t$ the
[existing saturation theorem](../lean/ThresholdHC/QuantileSelection/Full.lean)
gives $K=Q=\rho$. Suppose $h<t$ and fix a finite-objective submeasure
$f\mu$, $0\le f\le1$. Define
$$
 X=h\sqrt{\rho\Gamma_{f\mu}},\qquad u=h\sqrt{\rho\Gamma_{f\nu}},\qquad
 v=h\sqrt{\rho\Gamma_{f\kappa}}.
$$
Let $e,c$ be the unselected ordinary costs in the tail and core, respectively.
Superadditivity gives $u^2+v^2\le X^2$. Cauchy–Schwarz on the selected tail
gives $T\le e+u$, so $\sqrt{T^2+v^2}\le e+X$ by the triangle inequality.

For $\xi=(1-f)\kappa$, the core gaps exceed $h$, so
$c=h\int d^{-1}\,d\xi$. Since $h\rho/t\le T$, the separated bound gives
$Z^2=h^2\rho\Gamma_\xi\le C Tc$. For the finite-band core, the entropy
interaction bound is $G(p+q)\le G(p)+G(q)+2\log2\sqrt{G(p)G(q)}$.
This follows from Lemma 1 of the note using total cost $\le G$ in both
factors. Thus
$$
 h^2\rho\Gamma_\kappa\le v^2+Z^2+2\log2\,v Z
                  \le (v+a\sqrt{Tc})^2+b^2Tc .
$$
Indeed $E(111/160)>2$ implies $\sqrt C\log2\le(4/3)(111/160)=a$,
and $C\le a^2+b^2$. Now (1) bounds the raw quantile price by
$k(X+e+c)$ for every selection. Taking the infimum and clipping at $\rho$
proves the upper bound because $k\ge1$. The quantile core is feasible,
giving the lower bound $K\le Q$.

## Five-atom lower example

Set $t=2^{-20}$, $s=1+2^{-20}$, $\rho=1/8$ and $B=(16/t)^2$.
The first atom is at $t$ with mass $(19/12)\rho$. Three more have
gaps $t s,2ts,4ts$. At these atoms the masses are $\rho a(d/t)^2$,
with $a=1/10,1/192,1/65536$ in that order. Put the remaining mass at $1/2$.
The quantile core keeps $7/19$ of the first atom and all of the others.
As a feasible selection for the upper bound on $K$, keep just the first
and last atoms. The ordinary cost of the three skipped atoms is small, while
the quantile core pays the entropy cost of each of their separate bands.

The verifier calculates a lower endpoint for $Q$ and an upper endpoint
for the clipped cost of this feasible selection. Their rational comparison
is strict at $146255/100000$. This proves the obstruction without assuming
that the witness is optimal. Run it from the repository root with
`python tools/verify_quantile_price_bounds.py`.
