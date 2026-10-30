---
title: "Certified computation of the entropy–tail rate"
subtitle: "A sharper quantile comparison, bandwise selection, and controlled law approximation"
author: "Research contribution prepared for David Iach"
date: "30 October 2026"
---

# Scope and main contribution

This is an additive contribution to `davidiach/adaptive-threshold-estimation`, pinned to commit `6ad675e04570cc1ef6bece8e26beb81e1a176471`. It does not rewrite the baseline, change a frozen specification, or replace a published manuscript. Its mathematical objects are the selection functional $K$ and the closed quantile functional $Q$ in version 6, Sections 13–14 [R1–R3].

The contribution is deterministic. The proofs below do **not** assume that the paper-only statistical characterization $R_{\mu,\rho}(B)\asymp K_{\mu,\rho}(B)$ has been formalized or independently validated. They concern the functionals themselves. Interpreting their numerical values as minimax statistical rates still relies on the separate statistical theorem and its constants.

The main improvements are:

| Result | This contribution | Status |
|:---|:---|:---|
| Quantile comparison | $K\le Q\le \tfrac85K$, improving $1+2\sqrt2$ | Full paper proof below; not Lean-checked |
| Exact finite selection | An optimizer is an upper-gap suffix **within each dyadic band** | Full paper proof below; not Lean-checked |
| Fast feasible selection | A scan of $n+1$ global cuts gives $K\le V\le Q$ | Full paper proof below; not generally exact |
| Stability in the law | $|K_\mu-K_{\widetilde\mu}|\le d_{\rm TV}(\mu,\widetilde\mu)$ | Full paper proof below |
| Band-preserving rounding | $K_{T_\#\mu}\le K_\mu\le rK_{T_\#\mu}$ | Full paper proof below |
| Numerical evaluation | Rational lower/upper bounds, instance-bound replay, explicit search caps | Implemented and regression-tested; Python is not formally verified |
| Limit on further tightening | A rational six-atom example has $Q/K>1.42132>\sqrt2$ | Exact finite interval certificate |

These are contributions relative to the pinned repository. No claim of priority over the wider literature is made. Standard entropy inequalities, exchange arguments, and fractional-knapsack reasoning are ingredients, not claimed inventions. The limited related-work check near the end of this note is not a completed novelty survey.

# Definitions

Let $\mu$ be a probability law on $(0,1/2]$, let $0<\rho\le1/4$, let $B>0$, and set $h=B^{-1/2}$. Use exactly the repository's canonical bands

$$
I_j=(2^{-(j+2)},2^{-(j+1)}],\qquad j=0,1,2,\ldots.
$$

For a finite submeasure $\sigma\le\mu$, write

$$
a_j(\sigma)=\int_{I_j}d^{-2}\,\sigma(dd),\qquad
G(a)=A+\sum_j a_j\log(A/a_j),\qquad A=\sum_j a_j.
$$

Zero coordinates contribute zero, and $G(0)=0$. For infinitely many occupied bands, define $\Gamma_\sigma$ by the supremum of finite-prefix values of $G$, as in the repository. Write

$$
c_h(d)=\min\{1,h/d\},\qquad
K_\mu=\min\left\{\rho,\inf_{0\le\sigma\le\mu}
  \left[h\sqrt{\rho\Gamma_\sigma}+\int c_h(d)(\mu-\sigma)(dd)\right]\right\}.
$$

All logarithms are natural. The parameters $\rho,B$ are suppressed only when fixed.

For the quantile split, remove exactly the smallest-gap mass $\rho$: let $\nu$ be that lower-tail submeasure and let $\kappa=\mu-\nu$. At a boundary atom, split its mass fractionally. There is a positive quantile location $t$ such that $\nu$ is supported on $(0,t]$ and $\kappa$ on $[t,1/2]$. Then

$$
T_h=\int c_h\,d\nu,\qquad
Q_\mu=\min\{\rho,T_h+h\sqrt{\rho\Gamma_\kappa}\}.
$$

The core $\kappa$ meets finitely many bands and has finite inverse-square cost. No finiteness assumption on the full-law inverse moment or entropy is needed.

# A sharper quantile comparison

## Entropy interaction

**Lemma 1.** For finite nonnegative vectors $a,b$, with totals $A,B$,

$$
G(a+b)\le G(a)+G(b)+2\log 2\sqrt{AB}
          \le G(a)+G(b)+\sqrt{2G(a)G(b)}.
$$

**Proof.** Expanding the entropy gives

$$
G(a+b)-G(a)-G(b)
\le (A+B)H_2\left(\frac{A}{A+B}\right),
$$

because the omitted coordinatewise terms
$(a_j+b_j)\log(a_j+b_j)-a_j\log a_j-b_j\log b_j$
are nonnegative. Here $H_2(p)=-p\log p-(1-p)\log(1-p)$.

For completeness,

$$
H_2(p)\le2\log2\sqrt{p(1-p)}.
$$

To see this without appealing to a numerical plot, differentiate
$H_2(p)/\sqrt{p(1-p)}$ on $(0,1/2)$. Its derivative has the sign of

$$
g(p)=(1-p)\log(1-p)-p\log p.
$$

The function $g$ is concave on $[0,1/2]$, since
$g''(p)=-(1-2p)/(p(1-p))\le0$, and vanishes at both endpoints. Thus the ratio increases to its value $2\log2$ at $1/2$; symmetry handles the other half. Finally, $A\le G(a)$, $B\le G(b)$, and $2\log2<\sqrt2$. The latter can be verified, for example, using $\log2<7/10<1/\sqrt2$. Boundary cases follow by continuity. $\square$

The existing superadditivity property is also important:

$$
G(a+b)\ge G(a)+G(b).
$$

It follows from concavity and degree-one homogeneity. It remains true for the prefix-supremum extension $\Gamma$ by taking limits. The upper interaction bound above will only be used on the finite-band core.

## A factor-two scale-separated cost bound

**Lemma 2.** For any finite measure $\xi$ supported on $[t,1/2]$,

$$
\Gamma_\xi\le\frac{2}{t}H_\xi,
\qquad H_\xi=\int d^{-1}\,\xi(dd).
$$

**Proof.** Let $j_0$ be the band containing $t$. Index bands above it by $r\ge0$, so the band index is $j_0-r$. Put

$$
m_0=m_1=1,\qquad m_r=2^{r-1}\quad(r\ge2).
$$

Every supported gap in the band at offset $r$ satisfies $d/t\ge m_r$. If $a_r$ is its inverse-square cost, then

$$
\sum_r m_ra_r\le H_\xi/t.
$$

Use the subprobability weights $\pi_r=\exp(1-2m_r)$. They satisfy

$$
\sum_r\pi_r
=2e^{-1}+e^{-3}+e^{-7}+e^{-15}+\cdots<1.
$$

One elementary bound is $2/e<3/4$ and
$e^{-3}+e^{-7}+\cdots\le e^{-3}/(1-e^{-4})<2/15$.
For $p_r=a_r/A$, the entropy inequality for a subprobability vector gives
$H(p)\le\sum_rp_r\log(1/\pi_r)$. Therefore

$$
G(a)\le\sum_r a_r[1+\log(1/\pi_r)]
      =2\sum_r m_ra_r\le2H_\xi/t.
$$

Only finitely many of these bands can be occupied; the unused weights cause no difficulty. $\square$

This improves the factor four used in the pinned comparison proof. The factor two is not asserted to be optimal.

## A scalar inequality with an exact algebraic certificate

**Lemma 3.** For $T,v,c\ge0$,

$$
T+\sqrt{v^2+2Tc+2v\sqrt{Tc}}
\le\frac85\left(\sqrt{T^2+v^2}+c\right).
$$

**Proof.** If $r=\sqrt{T^2+v^2}=0$, both $T$ and $v$ vanish and the result is immediate. Otherwise divide by $r$, put $s=T/r\in[0,1]$, and write $z=\sqrt{c/r}$. It suffices to show

$$
s+\sqrt{1-s^2+2sz^2+2z\sqrt{s(1-s^2)}}
\le\frac85(1+z^2).
$$

The right side minus $s$ is positive. On squaring, the difference between its square and the radicand is

$$
P=\frac{64}{25}z^4+
 \left(\frac{128}{25}-\frac{26}{5}s\right)z^2
 -2z\sqrt{s(1-s^2)}+2s^2-\frac{16}{5}s+\frac{39}{25}.
$$

Young's inequality gives

$$
2z\sqrt{s(1-s^2)}\le\frac32z^2+\frac23s(1-s^2).
$$

Consequently,

$$
P\ge\frac{64}{25}
 \left(z^2+\frac{181-260s}{256}\right)^2+\frac{p(s)}{3072},
$$

where

$$
p(s)=2048s^3-1968s^2-584s+861.
$$

This is an exact polynomial identity, not a fitted numerical inequality. With $w=s-3/4\ge-3/4$,

$$
\begin{aligned}
p(s)&=2048w^3+2640w^2-80w+180\\
&\ge1104w^2-80w+180\\
&=1104\left(w-\frac{5}{138}\right)^2+\frac{12320}{69}>0.
\end{aligned}
$$

The required squared inequality follows, and then so does the unsquared inequality. $\square$

## Main theorem

**Theorem 4.** For every law and parameters in Section 2,

$$
\boxed{K_\mu\le Q_\mu\le\frac85K_\mu.}
$$

Also $T_h\le K_\mu$. If $h\ge t$, then $K_\mu=Q_\mu=\rho$.

**Proof.** The inequality $K\le Q$ follows by choosing $\sigma=\kappa$.
Fix any finite-objective selection $\sigma=f\mu$, where $0\le f\le1$. Define

$$
\begin{aligned}
u&=h\sqrt{\rho\Gamma_{f\nu}},&
v&=h\sqrt{\rho\Gamma_{f\kappa}},\\
a&=\int c_h(d)(1-f)\,\nu(dd),&
c&=\int c_h(d)(1-f)\,\kappa(dd).
\end{aligned}
$$

In this display, the scalar $u$ is distinct from the measure $\nu$. Write
$x=h\sqrt{\rho\Gamma_\sigma}$ and $S=x+a+c$ for the selection objective.
Because $\sigma=f\nu+f\kappa$, superadditivity implies

$$
u^2+v^2\le x^2.
$$

Cauchy–Schwarz and $\nu((0,1/2])=\rho$ give

$$
T_h\le a+h\int d^{-1}f\,d\nu
\le a+h\sqrt{\rho\int d^{-2}f\,d\nu}
\le a+u.
$$

In particular $T_h\le S$ for every selection, and $T_h\le\rho$, proving $T_h\le K$. If $h\ge t$, then $T_h=\rho$ and the saturation claim follows.

Assume now $h<t$. Put $\xi=(1-f)\kappa$ and $z_0=h\sqrt{\rho\Gamma_\xi}$. Since the core gaps exceed $h$, we have $c=hH_\xi$. Also every tail gap is at most $t$, giving $h\rho/t\le T_h$. Lemma 2 therefore yields

$$
z_0^2\le2(h\rho/t)(hH_\xi)\le2T_hc.
$$

Apply Lemma 1 to $\kappa=f\kappa+\xi$:

$$
h\sqrt{\rho\Gamma_\kappa}
\le\sqrt{v^2+z_0^2+\sqrt2\,vz_0}
\le\sqrt{v^2+2T_hc+2v\sqrt{T_hc}}.
$$

Finally, the Euclidean triangle inequality gives

$$
\sqrt{T_h^2+v^2}
\le\sqrt{(u+a)^2+v^2}
\le\sqrt{u^2+v^2}+a\le x+a.
$$

Lemma 3 now shows

$$
T_h+h\sqrt{\rho\Gamma_\kappa}
\le\frac85\left(\sqrt{T_h^2+v^2}+c\right)
\le\frac85S.
$$

Take the infimum over $\sigma$ and retain the outer cap at $\rho$. This proves the theorem. All infinite-law steps concern either monotone extended entropies or the finite-band core; no exchange of an infimum with an infinite limit is needed here. $\square$

**Why the proof is stronger.** The earlier comparison uses the total selected entropy both to control the selected tail and to control the selected core. Here the two costs remain separate until the inequality $u^2+v^2\le x^2$ combines them. That avoids charging the same selected cost twice.

# Exact selection within bands

**Theorem 5 (bandwise suffix reduction).** Let $\mu$ be a finite law on $n$ distinct positive gaps. If band $j$ contains $n_j$ atoms, a globally minimizing hard selection exists that, within every occupied band, selects a suffix of the atoms in increasing gap order. Thus an exact search need examine only

$$
\prod_j(n_j+1)
$$

assignments, rather than all $2^n$ hard subsets.

**Proof.** Allow fractional selections $x_i\in[0,1]$. The finite-dimensional objective is continuous on a compact cube, so it attains a minimum. Fix the selections outside one band. In that band put

$$
\alpha_i=w_i/d_i^2,\qquad \beta_i=w_ic_h(d_i).
$$

Its contribution to the entropy depends on the selected atoms only through $z=\sum_i\alpha_ix_i$. At fixed $z$, minimizing the objective is equivalent to maximizing the saved ordinary cost $\sum_i\beta_ix_i$. The benefit-to-cost ratio is

$$
\frac{\beta_i}{\alpha_i}=d_i^2c_h(d_i)
=\begin{cases}d_i^2,&d_i\le h,\\hd_i,&d_i\ge h.\end{cases}
$$

This is strictly increasing in the gap. The fractional-knapsack exchange argument therefore selects the largest gaps first, with at most one fractional boundary atom. Explicitly, moving a small amount of selected inverse-square cost from a smaller gap to a larger, not-yet-full gap preserves $z$ and increases the saved ordinary cost.

Between consecutive cumulative suffix costs, the maximized saving is affine in $z$. The entropy contribution, with the other bands fixed, is concave in $z$: in the positive interior its second derivative is $1/(A_0+z)-1/z\le0$. Its square root is also concave, since square root is increasing and concave. Thus on each such interval the complete objective is concave, and its minimum occurs at an endpoint. The fractional boundary atom may be removed or included in full without increasing the minimum.

Perform this replacement band by band. Each replacement preserves global optimality, leaves the already processed bands as suffixes, and makes the new band a hard suffix. This proves the claim. The outer cap by $\rho$ does not affect the argument. $\square$

This theorem does **not** give a polynomial-time algorithm in the unrestricted number of bands. When there is one atom per band, the candidate count is still $2^n$. It can nevertheless make a large difference when many atoms occupy the same few bands. For 60 atoms in one band, the sufficient family contains 61 candidates instead of $2^{60}$; this is a reduction against naive subset enumeration, not a claim that every previous implementation required that enumeration.

## A cheaper global-cut approximation

Let $V$ be the minimum of the capped objective over the $n+1$ selections that keep all atoms above a single global gap threshold.

**Corollary 6.** $K\le V\le Q\le\tfrac85K$.

**Proof.** The quantile core is a global cut with at most one fractional boundary atom. Its objective is concave in that atom's selected fraction, with every other atom fixed. At least one of the two endpoints is no worse than the fractional value. Both endpoints are among the global cuts. $\square$

The implementation precomputes ordinary-cost prefixes and updates the band-cost vector as the cut moves. It evaluates $n+1$ candidates, each involving at most the number of occupied bands. This is a certified feasible upper bound, **not** an exact optimizer in general.

For example, with masses $9999/10000$ at $1/4$ and $1/10000$ at $1/2$, rarity $1/4$, and budget $10^8$, the optimum selects the smaller-gap atom and rejects the larger-gap atom. Its value is approximately $0.0002000099997499875$, while the best global upper-gap cut is approximately $0.0002000214902134999$. The distinction is small in this example but exact. The certificate is `evidence/not_one_global_threshold.json`.

# Stability and controlled approximation of a law

## Total variation

Use the probability-measure convention

$$
d_{\rm TV}(\mu,\widetilde\mu)
=\sup_A|\mu(A)-\widetilde\mu(A)|
=\tfrac12\|\mu-\widetilde\mu\|_1.
$$

**Theorem 7.** At fixed $\rho,B$,

$$
\boxed{|K_\mu-K_{\widetilde\mu}|\le d_{\rm TV}(\mu,\widetilde\mu).}
$$

**Proof.** Let $\lambda=\mu\wedge\widetilde\mu$ be the common submeasure and let $\eta=1-\lambda((0,1/2])$. For any $\sigma\le\mu$, set $\sigma_0=\sigma\wedge\lambda$. Then $\sigma_0\le\widetilde\mu$ and $\Gamma_{\sigma_0}\le\Gamma_\sigma$. Moreover,

$$
\widetilde\mu-\sigma_0
=(\widetilde\mu-\lambda)+(\lambda-\sigma_0),
\qquad \lambda-\sigma_0\le\mu-\sigma.
$$

Since $0\le c_h\le1$, the remainder cost increases by at most $\eta$. Taking infima and clipping at $\rho$ gives $K_{\widetilde\mu}\le K_\mu+\eta$. Interchange the laws. $\square$

The unit constant cannot be improved uniformly. Fix $0<\eta<\rho$; start with a point mass at a fixed easy gap and move mass $\eta$ to a gap $d_h=o(h)$ as $h\downarrow0$. The original score tends to zero, while the perturbed score is at least $\eta$ by the tail lower bound and at most $\eta+O(h)$ by assigning the hard mass to the remainder.

This is stability of the **optimal rate functional**, not an assertion that a fixed estimator designed for one law continues to meet its budget or risk guarantee under another law. In particular, no guarantee about estimating $\mu$ from pilot data is being made. An empirical atomic measure and a continuous law have total variation distance one; replacing a continuous law by its empirical distribution does not automatically make this theorem useful.

## Band-preserving upward rounding

**Theorem 8.** Let $T:(0,1/2]\to(0,1/2]$ be measurable, preserve every canonical band, and satisfy $d\le T(d)\le rd$ for some $r\ge1$. For $\widetilde\mu=T_\#\mu$,

$$
\boxed{K_{\widetilde\mu}\le K_\mu\le rK_{\widetilde\mu}.}
$$

**Proof.** Push any $\sigma\le\mu$ forward. Since each gap stays in its band,

$$
r^{-2}a_j(\sigma)\le a_j(T_\#\sigma)\le a_j(\sigma).
$$

Coordinatewise monotonicity and homogeneity give the corresponding entropy inequalities, while $c_h(T(d))\le c_h(d)$. This proves $K_{\widetilde\mu}\le K_\mu$.

Conversely, write any $\widetilde\sigma\le\widetilde\mu$ as $f\widetilde\mu$ and lift it to $\sigma=(f\circ T)\mu$. Its pushforward is $\widetilde\sigma$ even when $T$ merges atoms. Then $\Gamma_\sigma\le r^2\Gamma_{\widetilde\sigma}$ and $c_h(d)\le r c_h(T(d))$. The lifted objective is at most $r$ times the rounded objective. Take infima and clip. $\square$

**The band condition is necessary for this argument.** Consider equal masses at $249/1000$ and $251/1000$, with rarity $1/100$ and budget $10^8$. Rounding the first gap upward to the second changes it by a factor of only $251/249\approx1.00803$, but merges two dyadic bands. Certified scores are approximately

$$
K_{\rm before}=5.204915296814786\cdot10^{-5},\qquad
K_{\rm after}=3.984063745019918\cdot10^{-5}.
$$

Their ratio is about $1.3064$, not at most $1.00803$. This is a feature of the dyadic entropy functional; it is not a demonstrated discontinuity of the underlying statistical minimax risk. The implementation's rounding helper checks band preservation exactly.

## A finite approximation theorem for arbitrary laws

**Corollary 9.** Suppose $d_{\rm TV}(\mu,\mu_0)\le\eta$, and a band-preserving upward map with distortion at most $r$ sends $\mu_0$ to a finite law $\widehat\mu$. If a numerical certificate encloses $K_{\widehat\mu}$ in $[L,U]$, then

$$
\boxed{\max\{0,L-\eta\}\le K_\mu
\le\min\{\rho,rU+\eta\}.}
$$

In particular, evaluating the finite quantile functional gives

$$
\max\{0,\tfrac58Q_{\widehat\mu}-\eta\}
\le K_\mu\le\min\{\rho,rQ_{\widehat\mu}+\eta\}.
$$

**Proof.** Compose Theorems 7 and 8, then apply Theorem 4 when using $Q$. $\square$

Every law on $(0,1/2]$ admits such finite approximations with $\eta\downarrow0$ and $r\downarrow1$. Choose $t>0$ so that $\mu((0,t))\le\eta$, move that small tail mass to $t$, and round the remaining support upward on a finite grid inside each of its finitely many bands. With $m$ equally spaced subintervals per band, the relative distortion is at most $1+1/m$.

This is an approximation theorem, not a universal time bound: finding $t$ and the exact cell masses requires suitable access to the law, and the required number of bands can be large. Certified enclosures for input masses would require an additional layer beyond the exact-rational law API implemented here.

# A certified obstruction to a square-root-two comparison

The factor $8/5$ is not claimed sharp. However, it cannot simply be replaced by $\sqrt2$.

Use $\rho=2113/10000$ and $h=152287/10^{11}$, with $B=h^{-2}$. The following decimal gaps and masses are exact terminating rationals:

| Gap | Mass | Selected in the feasible witness |
|---:|---:|:---:|
| 0.000215282 | 0.413943 | Yes |
| 0.000316030 | 0.014171 | No |
| 0.001250871 | 0.094956 | Yes |
| 0.022545179 | 0.021878 | Yes |
| 0.024956686 | 0.450979 | Yes |
| 0.328605066 | 0.004073 | Yes |

Let $U$ be a rigorous upper bound on this witness's objective, and $L_Q$ a rigorous lower bound on the quantile score. The saved rational intervals prove

$$
L_Q>\frac{142132}{100000}U,
\qquad \left(\frac{142132}{100000}\right)^2>2.
$$

Since $K\le U$, this proves

$$
Q/K>1.42132>\sqrt2.
$$

The display values are $Q\approx0.003141812697776756$ and $K\approx0.0022104890724864465$. The strict counterexample does not require knowing the exact optimizer or trusting the bandwise-suffix theorem: a feasible upper bound on $K$ is sufficient. See `evidence/sqrt2_counterexample.json` and its supporting instance file.

# The numerical implementation and its trust boundary

The new module is `toolkit/threshold_toolkit/rare_event_functional.py`. It uses only the Python standard library. It never uses binary floating-point arithmetic to form a bound. Decimal displays in the experiment summaries are explicitly separate from the rational endpoints in the certificates.

## Rational arithmetic primitives

For $x=n/d\ge0$ and precision $p$, let

$$
k=\left\lfloor\sqrt{\left\lfloor n2^{2p}/d\right\rfloor}\right\rfloor.
$$

Then $k/2^p\le\sqrt{x}<(k+1)/2^p$, unless the lower endpoint is exact, in which case the interval collapses. The integer square root supplies these bounds without an approximate transcendental function.

For a positive rational $x$, reduce it to $x=2^ky$ with $1\le y<2$. With $z=(y-1)/(y+1)\in[0,1/3)$,

$$
\log y=2\sum_{j=0}^{N-1}\frac{z^{2j+1}}{2j+1}+R_N,
\quad
0\le R_N\le\frac{2z^{2N+1}}{(2N+1)(1-z^2)}.
$$

The same formula at $z=1/3$ bounds $\log2$. This gives rational enclosures for the entropy. Monotonicity then gives rational bounds for each complete objective. Taking the minimum of all candidate lower endpoints and the minimum of all candidate upper endpoints encloses the global minimum whenever the sufficient candidate family has been completely enumerated.

A best feasible witness is not automatically declared the unique optimizer when its interval overlaps another candidate's interval. A search exceeding the explicit state cap raises an exception; it never emits an incomplete search as an exact certificate.

## Public entry points

`quantile_certificate` computes an inexpensive lower/upper enclosure using $T\le K$, $5Q/8\le K\le Q$, and the ordinary-only and full-entropy feasible selections.

`threshold_certificate` scans all global upper-gap cuts for a potentially tighter feasible upper bound. Its output explicitly records that it is not globally exact.

`exhaustive_certificate` uses the bandwise-suffix theorem and encloses the exact finite-law functional. It precomputes each band's suffix cost and complementary ordinary cost, so a candidate evaluation visits bands rather than all atoms.

`round_up_within_bands` constructs a valid finite-law rounding map and returns its exact maximum relative distortion. `transfer_enclosure` applies Corollary 9; it does not infer or validate a total-variation premise from samples.

`verify_certificate` takes the expected law, rarity, and budget separately. It checks the schema and scope, binds the instance by canonical rational values and a SHA-256 digest, reconstructs the required calculation, and compares the complete canonical output. It rejects extra, missing, or corrupted fields. This is deterministic recomputation, **not** an independent implementation or a formal proof of the Python code.

## Example use

```python
from fractions import Fraction
from threshold_toolkit.rare_event_functional import (
    FiniteGapLaw, exhaustive_certificate, verify_certificate,
)

law = FiniteGapLaw([
    ("1/10000000000", "1/100000000"),
    ("1/4", "99999999/100000000"),
])
cert = exhaustive_certificate(law, rho="1/1000000", budget=10**12)
assert verify_certificate(cert, law, rho="1/1000000", budget=10**12)
lo = Fraction(cert["K_interval"]["lower"])
hi = Fraction(cert["K_interval"]["upper"])
print(float(lo), float(hi))  # Display only; lo and hi remain exact.
```

Here $K\approx1.4\cdot10^{-8}$. The best of the ordinary-only and full-entropy scores, both capped at $\rho$, is $10^{-6}$: more than 71.4 times larger. The quantile score is only about 1.000283 times the optimum. This illustrates why selection matters; it is **not** a 71-fold measured improvement in an estimator's statistical performance.

# Validation actually performed

The final unit suite contains **29 tests**, all passing. A separate standard-library checker verifies all four polynomial identities in Lemma 3 coefficient by coefficient over the rationals; its record is `evidence/algebra.json`. It covers exact dyadic boundaries, positive gaps as small as $2^{-600}$, invalid inputs, exact single-atom formulas, quantile atom splitting, saturation, monotonicity, same-band search reduction, independent full-subset comparisons, total-variation and rounding examples, the exact scalar polynomial identity, certificate round trips, and deliberate corruption of scope, instance, endpoints, completion status, and other metadata.

A separate deterministic run examined **128 rational laws**, comparing **9,604 full hard subsets** against **5,211 band-suffix candidates**. The interval results were consistent in every case. The quantile bounds also enclosed the independently enumerated optima. These are finite regression checks, not proofs of the universal theorems.

An additional floating-point exploration examined **20,000 laws** and **1,439,604 subsets**. Its largest observed ratio was approximately 1.4213200455. A nearby rationalized example was then certified separately, yielding the strict $1.42132$ lower bound in Section 6. The floating-point exploration itself has no certificate status and was not used to justify the $8/5$ theorem.

All these runs use newly generated cases. No repository held-out benchmark data, sealed research inputs, or existing result files were changed. The complete upstream Lean suite and the complete pre-existing toolkit suite were **not** rerun. No claim is made about a new GitHub CI run. The container had no Lean executable, and a full network clone failed; the relevant upstream sources were read through the GitHub connector.

# Integration, remaining work, and related work

## Integration boundary

The package is additive: one module, one test file, this research note, and its reproducibility files. It does not alter the frozen entropy-tail specification, published papers, or existing audit records. The mathematical proofs here are not Lean proofs. The natural formalization targets are, in dependency order: the entropy interaction bound; the scale-separated bound; the scalar inequality; the $8/5$ comparison; the finite-band suffix reduction; and the two approximation inequalities.

The scalar inequality is particularly suitable for a small isolated algebraic proof. The bandwise result requires a finite-dimensional exchange argument, not the statistical experiment model. None of these targets should be recorded as verified merely because the Python tests pass.

## What this does not resolve

The full general-law entropy-tail statistical lower and upper bounds remain outside this contribution's formalization scope. This package does not produce a practical coin-flipping implementation of the paper's general rare-event estimator, establish a sharp high-confidence rare-event law, prove unknown-law adaptation, convert expected budgets into deterministic budgets, or eliminate the large constants in the statistical theorem. Its narrower improvement is a much tighter and auditable computational interface to the existing rate functional.

The absence of external specialist review remains a limitation, not an added completion gate. The repository's documented project preference is preserved.

## Related-work and novelty boundary

The repository already contains the entropy-tail selection law, the closed quantile law, and the hard-selection lemma [R1–R3]. These are not reintroduced here as new discoveries. Lee and Valiant study fully adaptive estimation of mixtures of unknown positive and negative coins, including the rare-event dependence on error, gap, and confidence [R4]. The September 2026 papers by Aronow, Kallus, and Lopatto [R5], and by Yao, Zhao, and Zhou [R6], concern Gaussian best-arm identification and complexity-weighted gap entropy. They are relevant antecedents, but they are different statistical tasks.

In particular, the appearance of an additive confidence/entropy term in best-arm identification does not by itself prove the analogous formula for the present rare-event model. No such transfer is claimed. This contribution makes no assertion that its deterministic inequalities or finite optimization structure are unprecedented outside the repository; a complete priority survey has not been performed.

# References and pinned source map

**[R1]** David Iach, *Adaptive Threshold Estimation*, repository overview, agent guide, and current work plan at commit `6ad675e04570cc1ef6bece8e26beb81e1a176471` (30 October 2026). Source paths: `README.md`, `AGENTS.md`, `docs/WORKPLAN.md`.

**[R2]** Same repository, consolidated version 6, `paper/v6/entropy-tail-statement.tex`. Definitions of $G$, $\Gamma$, $K$, the hard-assignment lemma, and the entropy-tail theorem statement. At the pinned checkpoint the full statistical characterization remains paper-only.

**[R3]** Same repository, `paper/v6/finite-comparison.tex`. The previous bound is $K\le Q\le(1+2\sqrt2)K$, using the scale-separated bound $\Gamma_\xi\le4H_\xi/t$.

**[R4]** Jasper C. H. Lee and Paul Valiant, *Uncertainty about Uncertainty: Optimal Adaptive Algorithms for Estimating Mixtures of Unknown Coins*, arXiv:1904.09228; SODA 2021. Primary source checked on 30 October 2026: <https://arxiv.org/abs/1904.09228>.

**[R5]** P. M. Aronow, Nathan Kallus, and Patrick Lopatto, *A positive resolution of the gap-entropy conjecture*, arXiv:2609.10529, 9 September 2026. Primary source checked on 30 October 2026: <https://arxiv.org/abs/2609.10529>.

**[R6]** Jiarui Yao, Jiaxi Zhao, and Xiangxin Zhou, *Gap Entropy and Almost Instance-Wise Optimal Best-Arm Identification*, arXiv:2609.13703, 12 September 2026. Primary source checked on 30 October 2026: <https://arxiv.org/abs/2609.13703>.

Pinned repository source: <https://github.com/davidiach/adaptive-threshold-estimation/tree/6ad675e04570cc1ef6bece8e26beb81e1a176471>.

Code: Apache-2.0. This note and accompanying explanatory documentation: CC BY 4.0, matching the repository's stated license split.
