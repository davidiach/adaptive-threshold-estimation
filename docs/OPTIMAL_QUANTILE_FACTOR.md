# The optimal universal quantile-to-selection factor

Let $c_*=\sup Q_\mu(\rho,B)/K_\mu(\rho,B)$ over positive-gap probability
laws, $0<\rho\le1/4$ and $B>0$, with the canonical dyadic bands and fractional
quantile split of the [selection theorem](../research/2026-10-30-certified-selection/NOTE.md).
All logarithms below are natural. For $k\ge\sqrt2$ and $u\ge1$ set
$$
 \lambda=2k^2(u+1/u)-4k,\qquad
 F(k,u)=\exp(1-\lambda/(2u))+\sum_{j=0}^{\infty}\exp(1-\lambda\,2^j).
$$

**Theorem.** The sharp constant is the unique $k\in[\sqrt2,31/20]$ satisfying
$$
 \max_{1\le u\le31/20} F(k,u)=1.
$$
In particular,
$$
 1.462554551279 < c_* < 1.462554551280 .
$$
Finite laws approach the same supremum as general laws. The characterization
is a paper proof. Lean now checks the unique scalar root and its exact equivalence to all finite-vector bounds, including a counterexample below the root. Finite-law realization and sharpness over gap laws remain to be formalized. [Native record](../results/optimal-quantile-root-20261105/README.md)

The [exact arithmetic verifier](../tools/verify_optimal_quantile_factor.py)
certifies the displayed numerical bracket. It uses a concrete six-atom
law on the lower side and a covering of the entire interval in $u$ on the upper side.

## 1. Normalizing an arbitrary law and selection

For a finite vector $x\ge0$ put $A=\sum_i x_i$ and
$G(x)=A+\sum_i x_i\log(A/x_i)$, with zero coordinates contributing zero.
We use homogeneity, concavity, coordinatewise monotonicity and superadditivity
of $G$. These follow from the homogeneous Shannon entropy formula. Splitting
a coordinate into several bins of the same total increases entropy. For
$A,B\ge0$ write
$$
 I(A,B)=(A+B)\log(A+B)-A\log A-B\log B .
$$
In particular $G(x\sqcup y)=G(x)+G(y)+I(A,B)$ for disjoint coordinates,
and $G(x+y)\le G(x\sqcup y)$ when coordinates overlap. $I$ is increasing
in each argument and $I(A,B)\le2\log2\sqrt{AB}$.
[Entropy interaction proof](../lean/ThresholdHC/QuantileSelection/Interaction.lean)

Let $h=B^{-1/2}$, $t$ be the lower $\rho$ quantile and $\mu=\nu+\kappa$ the
tail/core split. Set $T=\int c_h\,d\nu$ with $c_h(d)=\min(1,h/d)$.
The tail has mass $\rho$ and $T>0$. For $h\ge t$, $K=Q=\rho$.
Assume $h<t$ and consider a submeasure $f\mu$ of finite objective. Index the
core bands from the band of $t$ outwards to larger gaps, starting at zero.
Their minimum possible ratios $d/t$ are bounded below by
$m_0=1$ and $m_j=2^{j-1}$ for $j\ge1$.
[Quantile split and saturation](../lean/ThresholdHC/QuantileSelection/Full.lean)

Scale all inverse-square band costs by $h^2\rho/T^2$. Write $v,b$ for the
scaled costs of $f\kappa,(1-f)\kappa$, and $l$ for those of $f\nu$.
The raw quantile price divided by $T$ is $1+\sqrt{G(v+b)}$. All core
vectors are finite since $t>0$. The normalized ordinary price of skipped
core mass is at least $\sum_j m_j b_j$. Indeed $c_h(d)=h/d$ on the core,
$d\ge t m_j$ there and $T\ge h\rho/t$. Write $e=\int c_h(1-f)\,d\nu/T$,
so $0\le e\le1$. Cauchy–Schwarz on the selected tail gives
$$
 (1-e)^2\le \frac{h^2\rho}{T^2}\int f(d)d^{-2}\,\nu(dd)=\sum_j l_j.
$$

Only band zero can contain both tail and core. Merging all selected
tail costs into this one band decreases entropy. Taking first a finite
prefix and then its limit proves the same statement if there are infinitely
many tail bands. Finite objective bounds the total cost, and the merged
finite vector has continuous entropy. The normalized rare price of the
selection is consequently at least $\sqrt{G(v+(1-e)^2 e_0)}$, where $e_0$
is the unit vector in band zero.

We claim that $\Phi(y)=\sqrt{G(v+y^2e_0)}$ is 1-Lipschitz on $y\ge0$.
For $y>0$, let $M$ be the total cost and $p=(v_0+y^2)/M$. Then
$$
 0\le\Phi'(y)=\frac{y(1-\log p)}{\sqrt{G(v+y^2e_0)}}
 \le\sqrt{\frac{p(1-\log p)^2}{1+H_2(p)}}\le1.
$$
Here $H_2(p)=-p\log p-(1-p)\log(1-p)$ bounds the full entropy from below.
For the last inequality, subtract the numerator from the denominator.
Using $-\log(1-p)\ge p$, the difference is at least
$1-p^2-p(x+x^2)$ with $x=-\log p$. This is nonnegative since
$e^x-e^{-x}\ge2x+x^3/3\ge x+x^2$ for $x\ge0$.
The case $p=1$ is equality. Continuity at $y=0$ completes the Lipschitz
claim. Thus the normalized raw selection price is at least
$$
 \sqrt{G(v+e_0)}+\sum_j m_j b_j .
$$

## 2. Removing the selected core's band locations

Fix $w=v+b$. The last display is a concave function of $v$ in the box
$0\le v_j\le w_j$. A minimum occurs at a vertex, by taking the cheaper
endpoint in each coordinate. The numerator $1+\sqrt{G(w)}$ stays fixed.
Hence for an upper bound on the ratio we may take $v,b$ disjoint.

Let $E=G(v)$, $A=\sum v_j$, $B_0=\sum b_j$ and $c=\sum m_j b_j$.
Here $E\ge A$ and $c\ge B_0$.

* If $b_0=0$, then $G(v+e_0)\ge1+E$, while
  $G(v+b)\le E+G(b)+I(A,B_0)\le E+G(b)+I(E,B_0)$.
  The last quantity is $G(E,b_1,b_2,\ldots)$. Replacing the entire
  selected core by the single cost $E$ in band zero therefore bounds the
  ratio from above.
* If $b_0>0$, then $v_0=0$ and $G(v+e_0)=1+D$, where $D=E+I(A,1)$.
  The scale-weight bound gives $G(b)\le2c$, including the two bands
  of weight one. If $c\le1$, set $N=G(v+b)$ and note $N\le D+2c$.
  Hence $1+\sqrt N\le\sqrt{2}\sqrt{1+N}
  \le\sqrt2(\sqrt{1+D}+c)$. If $c\ge1$, the derivative
  $\partial_s I(A,s)=\log(1+A/s)$ for $s\ge1$ is at most
  $\sqrt A$, since $\log(1+x^2)\le x$ for $x\ge0$. Thus
  $N\le D+2c+(c-1)\sqrt D$. Again $1+N\le(\sqrt{1+D}+c)^2$,
  since $2\sqrt{1+D}\ge1+\sqrt D$ and $c^2\ge c$.
  The ratio in this case is at most $\sqrt2$.
  [Scale weights](../lean/ThresholdHC/QuantileSelection/ScaleWeights.lean)

It follows that a universal factor is the supremum, over $a\ge0$ and finite
nonnegative lists $b=(b_0,\ldots,b_{s-1})$, of
$$
 R(a,b)=\frac{1+\sqrt{G(a,b_0,\ldots,b_{s-1})}}
                  {\sqrt{1+a}+\sum_{j=0}^{s-1}2^j b_j}. \tag{1}
$$
The list in (1) starts in the first band *above* the boundary band. Its
weights are $1,2,4,\ldots$. Taking $a=1$ and no other cost gives $\sqrt2$,
covering the second case. The preceding inequalities compare raw objectives
for every selection. Taking their infimum and then clipping at $\rho$
preserves the factor since it is at least one.

Conversely fix any such $a,b$. Choose a small fixed $\rho>0$ at most $1/4$.
At the dyadic gap $t=2^{-n}$ place mass $\rho(1+a)$. At gaps
$t2^j(1+\eta)$, $0<\eta<1$, place masses
$\rho b_j[2^j(1+\eta)]^2$. Choose $\rho$ small enough that this leaves
positive mass, which is placed at $1/2$. For all sufficiently large $n$
the indicated gaps occupy distinct bands, including the last, easy atom.
The quantile tail is mass $\rho$ at $t$. A feasible hard selection takes
the entire atom at $t$ and the easy atom. Put $h=\alpha t$ with
$\alpha>0$ sufficiently small that both prices remain below $\rho$ and
$h<t$. In units of $T=\alpha\rho$ the easy atom has inverse-square cost
at most $4t^2/\rho$, which vanishes as $n\to\infty$. The quantile core
has limiting costs $(a,b)$ and the hard selection has limiting cost
$1+a$ in the boundary band. Its normalized ordinary price is
$(1+\eta)\sum_j2^j b_j$. Taking $n\to\infty$ and then $\eta\downarrow0$
makes the ratio of the quantile price to this feasible price converge to
(1). Since $K$ is at most the feasible price, (1) gives exactly $c_*$.

## 3. An exact scalar equation

A constant $k\ge\sqrt2$ bounds (1) exactly when it works for every tangent
in the identity $\sqrt{1+a}=\inf_{u\ge1}(u+(1+a)/u)/2$. At a fixed $u$,
rescale all costs $x=(a,b)$ by a common scalar $t\ge0$. The maximum of
$\sqrt{tG(x)}-tkC(x)$ is $G(x)/(4kC(x))$ for $x\ne0$, where
$C(x)=a/(2u)+\sum_j2^j b_j$. The zero vector already satisfies the
inequality. Thus the condition becomes
$$
 G(x)\le\lambda C(x)\quad\text{for every finite vector }x\ge0 .
$$
For a unit-total vector $p$, this is precisely
$1+H(p)\le\lambda\sum_i p_i w_i$, with cost weights
$w=(1/(2u),1,2,4,\ldots)$. On any fixed finite index set, the maximum of
$1+H(p)-\lambda\sum p_i w_i$ is $\log\sum_i e^{1-\lambda w_i}$.
This follows by normalizing the exponential weights and subtracting the
KL divergence from that normalized vector. Finite partial sums increase
to $F(k,u)$. The condition for all finite vectors is therefore $F(k,u)\le1$.

For $u\ge1$, $\lambda$ increases with $u$. The first summand can also
be written $\exp(2-k^2-(k/u-1)^2)$, so it decreases for $u\ge k$.
Thus the maximum may be taken on $[1,k]$. Throughout
$k\in[\sqrt2,31/20]$ the same maximum is obtained on the fixed interval
$[1,31/20]$. The series converges uniformly there. At each fixed $u$,
$\lambda$ strictly increases with $k$, so $F$ strictly decreases.
Taking a maximizer on the compact interval shows its maximum also strictly
decreases with $k$. It varies continuously. The lower example and upper
certificate below straddle one. This proves the unique-root characterization.

## 4. Certifying the numerical value

For the lower bound use (1)'s finite-law construction with $t=\eta=2^{-40}$,
$\rho=1/8$, $h=t/16$, $a=0.5853452$ and
$b=(0.09980536,0.005307215,0.00001500696,0.00000000012033)$.
All terminating decimals here are exact. The verifier encloses the actual
six-atom quantile and feasible objectives, with a strict rational
comparison at $1.462554551279$.

For the upper endpoint $k=1.462554551280$, we certify every $u$ in
$[1,31/20]$. On this interval $F_{uu}\ge-25$. Indeed the first summand
is at most one, and the second derivative of its exponent is
$-6k^2/u^4+4k/u^3\ge-15$. The square of the first derivative in the
exponential chain rule is nonnegative. The other summands contribute
at worst $-\lambda''\sum_{m=1,2,4,\ldots}m e^{1-m\lambda}$.
Here $\lambda''=4k^2/u^3<10$, $\lambda\ge2$, and the sum is bounded by
$e^{-1}/(1-e^{-2})^2<1$. Exponential decay also justifies differentiating
the series twice uniformly on this interval.

On each subinterval $[l,r]$, convexity of $F(k,u)+25u^2/2$ bounds
$F(k,u)$ by the larger endpoint value plus $25(r-l)^2/8$. The verifier
bisects until this upper bound is strictly below one. It covers the full
interval with 85 terminal cells, at most 21 subdivisions deep. At each
endpoint it sums weights through $m=16$ and bounds the omitted terms by
$4/(3\cdot2^{63})$. Each exponential is enclosed with an alternating
series after halving the argument, followed by upward-rounded squaring.
All comparisons use integers and rational arithmetic. A reproduction is
`python tools/verify_optimal_quantile_factor.py`. The unique scalar
root, independent of the displayed rounding, specifies the exact factor.

## Native finite-core reduction

Lean checks the 1-Lipschitz bound for the square root of entropy after adding $y^2$ in the boundary coordinate. It also checks skipped-tail absorption, the concave reduction to disjoint core vectors and both boundary-coordinate cases, giving the exact scalar-root factor for arbitrary nonnegative finite core splits. The all-law comparison below includes the measure normalization. [Native record](../results/quantile-core-reduction-20261105/README.md)

## Native all-law upper comparison

The normalization of arbitrary gap laws is now Lean-checked. For every positive-gap probability law, $0<\rho\le1/4$ and $B>0$, the original selection functional satisfies $\mathcal K\le Q\le c_{\rm vec}\mathcal K$, where $c_{\rm vec}$ is the exact unique scalar root. The proof includes fractional quantile atoms, countable tail merging, saturation and infinite selected entropy. The mathematical selection-value comparison also holds for $\rho\le1$. Finite-law realization and sharpness over gap laws remain to be formalized. [Native record](../results/sharp-quantile-upper-20261105/README.md)
