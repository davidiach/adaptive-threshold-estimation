# Computing the rare-event rate and a tighter selection comparison

The closed quantile functional can be evaluated without searching over subsets
or submeasures. This note gives the computation, an algebraic inversion for a
target value, and a stronger deterministic comparison:

$$
\boxed{\quad \frac35 Q(B)\le \mathcal K(B)\le Q(B).\quad}
$$

The comparison holds for every probability law on positive gaps, including
infinite-support laws. It improves the factor $1+2\sqrt2$ in
[finite-gap revision 2, comparison section](../paper/finite-gap-rare-events/revision-2/sections/comparison.tex)
to $5/3$. A slightly smaller algebraic constant is given below. No claim that
either new constant is optimal is made.

The baseline is repository checkpoint `6ad675e04570cc1ef6bece8e26beb81e1a176471`.
The preserved comparison is the starting point for this improvement; this note
does not assert a new statistical characterization or worldwide novelty.

**Verification boundary:** the new comparison is an elementary paper proof in
this note, not a Lean-checked theorem. The numerical toolkit evaluates a
functional of a supplied finite law. It does not implement the rare-event
statistical estimator, learn an unknown law, or certify a confidence interval.
The existing statistical characterization retains the
[scope recorded in RESULTS.md](RESULTS.md#general-law-rare-event-characterization).
No frozen manuscript, formal statement, or published evidence is changed by
this note.

## Definitions

Let $\mu$ be a probability law on $(0,1/2]$, let $0<\rho\le1/4$, and let
$B>0$. Write $h=B^{-1/2}$. Remove exactly the smallest-gap mass $\rho$:
let $t$ be the lower $\rho$-quantile, let $\nu$ be the restriction of $\mu$
to $(0,t)$ plus the necessary fraction of the atom at $t$, and put
$\kappa=\mu-\nu$. Thus

$$
\nu((0,1/2])=\rho,\qquad
\operatorname{supp}\nu\subseteq(0,t],\qquad
\operatorname{supp}\kappa\subseteq[t,1/2].
$$

The quantile $t$ is strictly positive: $\mu((0,s])\to0$ as $s\downarrow0$.
Consequently, the core $\kappa$ occupies only finitely many canonical bands.
The tail can occupy infinitely many.

For $I_j=(2^{-j-2},2^{-j-1}]$ and a finite measure $\xi$, define

$$
a_j(\xi)=\int_{I_j}d^{-2}\,\xi(dd),\qquad
H_\xi=\int d^{-1}\,\xi(dd).
$$

For a finite nonnegative vector $a$, with $A=\sum_j a_j$, set

$$
G(a)=A+\sum_{j:a_j>0}a_j\log(A/a_j),\qquad G(0)=0.
$$

Let $\Gamma_\xi=\sup_JG(a_0(\xi),\ldots,a_J(\xi))$. These are the
unchanged definitions in the
[general-law manuscript](../paper/rare-event/v2/sections/additive.tex) and
[Lean model](../lean/ThresholdHC/EntropyTail/Model.lean). All logarithms are
natural. Define

$$
\begin{aligned}
T_h&=\int\min\{1,h/d\}\,\nu(dd),\\
Q(B)&=\min\{\rho,T_h+h\sqrt{\rho\Gamma_\kappa}\},\\
\mathcal K(B)&=\min\left\{\rho,
\inf_{0\le\sigma\le\mu}
\left[h\sqrt{\rho\Gamma_\sigma}
+\int\min\{1,h/d\}\,(\mu-\sigma)(dd)\right]\right\}.
\end{aligned}
$$

## Two entropy inequalities

### Superadditivity and a square-root triangle inequality

For nonnegative finite measures $\xi,\zeta$,

$$
\Gamma_\xi+\Gamma_\zeta\le\Gamma_{\xi+\zeta},\qquad
\sqrt{\Gamma_{\xi+\zeta}}
\le\sqrt{\Gamma_\xi}+\sqrt{\Gamma_\zeta}.
\tag{1}
$$

Here and below infinite values are interpreted in the extended nonnegative
reals; an inequality with infinite right side is automatic. To prove (1),
first take finite vectors $a,b$ with totals $A,C>0$. Concavity of Shannon
entropy gives $G(a+b)\ge G(a)+G(b)$. To see the upper bound directly, write
$L(u,v)=(u+v)\log(u+v)-u\log u-v\log v\ge0$, using $0\log0=0$.
Expansion gives
$G(a+b)-G(a)-G(b)=L(A,C)-\sum_jL(a_j,b_j)\le L(A,C)$, and hence

$$
\begin{aligned}
G(a+b)-G(a)-G(b)
&\le A\log(1+C/A)+C\log(1+A/C)\\
&\le2\sqrt{AC}
\le2\sqrt{G(a)G(b)}.
\end{aligned}
$$

For completeness, $\log(1+u)\le\sqrt u$ for $u>0$, because the derivative
of $\sqrt u-\log(1+u)$ is
$(\sqrt u-1)^2/[2\sqrt u(1+u)]\ge0$ and its limit at zero is zero.
This proves the second inequality after squaring. A zero total is immediate.
Apply both finite-vector inequalities to increasing band prefixes and take
their limits to obtain (1).

We also use monotonicity: $\xi\le\zeta$ implies
$\Gamma_\xi\le\Gamma_\zeta$. On a positive coordinate,
$\partial G/\partial a_j=1+\log(A/a_j)\ge1$; continuity at zero gives the
finite-dimensional assertion, and increasing prefixes give the general one.
In particular $\Gamma_\xi\ge\int d^{-2}\xi(dd)$.

### A scale-separated cost bound with coefficient two

If $\xi$ is supported on $[t,1/2]$ for $t>0$, then

$$
\Gamma_\xi\le \frac{2H_\xi}{t}.
\tag{2}
$$

The zero measure is immediate. Otherwise $t\le1/2$; let $I_{j_0}$ contain
$t$ and index the occupied bands by their
offset $r=j_0-j\ge0$. Write $a_r$ and $g_r$ for their inverse-square and
inverse-gap costs. The band boundaries give

$$
a_0\le g_0/t,\qquad a_1\le g_1/t,\qquad
a_r\le2^{1-r}g_r/t\quad(r\ge2).
$$

Missing bands have cost zero. For $A=\sum_ra_r>0$, compare the probability
vector $a/A$ with

$$
\pi_0=\pi_1=3/8,\qquad \pi_r=2^{-r-1}\quad(r\ge2).
$$

This is a probability distribution. Nonnegativity of relative entropy gives

$$
\Gamma_\xi\le\sum_ra_r[1+\log(1/\pi_r)].
$$

Here the needed entropy inequality is finite: for $p_r=a_r/A>0$,
$\sum_rp_r\log(\pi_r/p_r)\le\sum_rp_r(\pi_r/p_r-1)
=\sum_{r:p_r>0}\pi_r-1\le0$, by $\log u\le u-1$.

For $r=0,1$, the coefficient after using the cost bound is
$1+\log(8/3)<2$. For $r\ge2$, it is
$2^{1-r}[1+(r+1)\log2]\le2$: use $\log2<1$ and
$r+2\le2^r$. Summing proves (2).
The finite band support justifies all the entropy expressions without any
moment assumption on the original law $\mu$.

## The comparison theorem

**Theorem.** For every law, rarity and budget above,

$$
\mathcal K(B)\le Q(B)\le\frac53\mathcal K(B).
\tag{3}
$$

If $h\ge t$, then $\mathcal K(B)=Q(B)=\rho$.

**Proof.** Taking $\sigma=\kappa$ in the selection objective proves
$\mathcal K\le Q$.

For the other direction take any $0\le\sigma\le\mu$ with finite objective.
Such competitors exist, since $\sigma=0$ has objective at most one.
Write $f=d\sigma/d\mu\in[0,1]$ and split it across the quantile measures:

$$
\eta=f\nu,\qquad \alpha=f\kappa,\qquad \beta=(1-f)\kappa.
$$

Thus $\sigma=\eta+\alpha$ and $\kappa=\alpha+\beta$. These identities also
hold when $\nu$ and $\kappa$ share the quantile atom: they use
$\nu+\kappa=\mu$, not disjoint supports. Set

$$
\begin{aligned}
s&=\int\min\{1,h/d\}\,\eta(dd),&
b&=\int\min\{1,h/d\}\,(1-f)\nu(dd),\\
a&=h\sqrt{\rho\Gamma_\alpha},&
x&=h\sqrt{\rho\Gamma_\sigma}.
\end{aligned}
$$

Cauchy--Schwarz, $\eta((0,1/2])\le\rho$, and (1) give

$$
s^2\le h^2\rho\int d^{-2}\eta(dd)
\le h^2\rho\Gamma_\eta,
\qquad s^2+a^2\le x^2.
\tag{4}
$$

Also $T_h=s+b$. Every finite selection objective is at least
$x+b\ge s+b=T_h$; infinite objectives satisfy the same lower bound
automatically.
Since $T_h\le\rho$, it follows that $T_h\le\mathcal K$. If $h\ge t$,
then $T_h=\rho$, proving the saturation assertion and (3) in this case.

Now suppose $h<t$. Define $c=hH_\beta$. The selection objective is exactly
$S=x+b+c$, because all core gaps are at least $t>h$. Put
$p=s+b=T_h$ and $w=x+b$. Equation (4) and the triangle inequality in
$\mathbb R^2$ imply

$$
\sqrt{p^2+a^2}
\le\sqrt{s^2+a^2}+b\le w.
\tag{5}
$$

Every tail gap is at most $t$, so $h\rho/t\le T_h=p$. Equations (1)--(2)
therefore give

$$
\begin{aligned}
h\sqrt{\rho\Gamma_\kappa}
&\le a+h\sqrt{\rho\Gamma_\beta}\\
&\le a+\sqrt{2(h\rho/t)(hH_\beta)}
\le a+\sqrt{2pc}.
\end{aligned}
$$

Consequently,

$$
\begin{aligned}
Q
&\le p+a+\sqrt{2pc}\\
&\le \frac{13}{10}p+a+\frac53c\\
&\le\frac{\sqrt{269}}{10}\sqrt{p^2+a^2}+\frac53c\\
&\le\frac53(w+c)=\frac53S.
\end{aligned}
$$

The second line uses
$\sqrt{2pc}\le(3/10)p+(5/3)c$, which follows by squaring the
nonnegative difference of the corresponding square roots. The third is
Cauchy--Schwarz. The last uses (5) and $269/100<25/9$.

Take the infimum over all finite-objective selections. Combining the result
with $Q\le\rho$ yields
$Q\le(5/3)\min\{\rho,\inf_\sigma S\}=(5/3)\mathcal K$.
This also covers the case where the infimum is not attained. ∎

### A smaller algebraic coefficient

The same proof gives $Q\le\lambda_*\mathcal K$, where $\lambda_*>1$ is
the unique root of

$$
4\lambda_*^4-8\lambda_*^2-4\lambda_*-1=0,
\qquad \lambda_*\approx1.6434789011.
$$

Indeed, for any $\lambda>0$,
$\sqrt{2pc}\le p/(2\lambda)+\lambda c$. Hence

$$
p+a+\sqrt{2pc}
\le\sqrt{(1+1/(2\lambda))^2+1}\,w+\lambda c.
$$

The two coefficients coincide at $\lambda=\lambda_*$. Uniqueness above
one follows because
$\lambda^2-2-1/\lambda-1/(4\lambda^2)$ is strictly increasing and
changes sign. The displayed decimal is a numerical approximation; the
algebraic definition and inequalities are the proof. Neither coefficient is
asserted to be the best possible comparison for the original functionals.

## Evaluation for a finite law

Let $\mu=\sum_{i=1}^nw_i\delta_{d_i}$ with positive weights, distinct sorted
gaps $0<d_1<\cdots<d_n\le1/2$, and total mass one. Merge duplicate gaps
first. The tail weights are

$$
\tau_i=\min\left\{w_i,\left(\rho-\sum_{\ell<i}w_\ell\right)_+\right\}.
$$

Compute the core band costs from the actual gaps,

$$
a_j=\sum_{i:d_i\in I_j}\frac{w_i-\tau_i}{d_i^2},\qquad
\Gamma_\kappa=A+\sum_{j:a_j>0}a_j\log(A/a_j),\qquad A=\sum_ja_j.
$$

The entropy groups **inverse-square costs by dyadic band**, not individual
atoms and not ordinary probability weights. Splitting an atom into duplicate
entries must therefore leave the mathematical value unchanged. At most one
distinct gap is split between the tail and core.

Sorting costs $O(n\log n)$ comparisons; the quantile split and aggregation
take $O(n)$ arithmetic operations once sorted. There are at most $n$ occupied
bands, regardless of the distances between their indices. A dictionary of
occupied bands avoids iterating through empty bands. Memory use is $O(n)$.
These are real-arithmetic operation counts; they do not assert bit-complexity
or floating-point error bounds.

### Dyadic boundary convention

The upper endpoint of a band is included and the lower endpoint is excluded.
In particular, $1/2$ is in band zero, $1/4$ in band one, and $1/8$ in band two.
For binary floating-point input, if `m, e = math.frexp(d)`, the exact band of
that represented value is

```python
j = -e if m == 0.5 else -e - 1
```

This avoids rounding a logarithm onto the wrong side of a dyadic boundary,
including for subnormal floats. It does not remove overflow or underflow
concerns from inverse moments, which need separate treatment in numerical
implementations.

### Piecewise linear evaluation and inversion

Set $C=\sqrt{\rho\Gamma_\kappa}>0$ and

$$
F(h)=\sum_i\tau_i\min\{1,h/d_i\}+Ch,
\qquad Q(B)=\min\{\rho,F(B^{-1/2})\}.
$$

For the tail gaps at or below $h$, define

$$
P_k=\sum_{i\le k}\tau_i,\qquad
J_k=\sum_{i>k}\tau_i/d_i.
$$

On $d_k\le h\le d_{k+1}$,

$$
F(h)=P_k+h(C+J_k).
\tag{6}
$$

Use $P_0=0$ and $J_0=\sum_i\tau_i/d_i$ before the first tail gap; the
formula also agrees at either endpoint. Beyond the last positive tail atom,
$P_k=\rho$ and $J_k=0$. Prefix masses and suffix inverse moments therefore
permit $O(\log n)$ mathematical evaluation queries after preprocessing.

For a target $0<\varepsilon<\rho$, $F$ is continuous and strictly increasing,
so there is exactly one $h_\varepsilon>0$ with $F(h_\varepsilon)=\varepsilon$.
After locating its interval by the increasing breakpoint values $F(d_k)$,

$$
h_\varepsilon=\frac{\varepsilon-P_k}{C+J_k},\qquad
B_\varepsilon=h_\varepsilon^{-2},\qquad
Q(B)\le\varepsilon\ \Longleftrightarrow\ B\ge B_\varepsilon.
\tag{7}
$$

Thus inversion needs a scan or binary search through breakpoints and one
algebraic calculation, rather than an iterative root finder. Precomputing
breakpoints allows $O(\log n)$ mathematical inversion queries; a direct scan
is $O(n)$. A target at least $\rho$ is already met by every positive budget,
and a nonpositive target is unattainable at any finite budget. These are
statements about $Q$, not the exact minimax risk or an implemented estimator.

For the one-atom law $\mu=\delta_d$, the formulas reduce to

$$
Q(B)=\min\left\{\rho,
\rho\min\{1,(d\sqrt B)^{-1}\}
+\frac{\sqrt{\rho(1-\rho)}}{d\sqrt B}\right\}.
$$

For $0<\varepsilon<\rho$, its inverse is exactly

$$
B_\varepsilon=
\left[\frac{\rho+\sqrt{\rho(1-\rho)}}{d\varepsilon}\right]^2.
$$

This is an identity for the quantile functional. The exact point-mass
selection functional is instead
$\mathcal K(B)=\min\{\rho,\sqrt\rho/(d\sqrt B)\}$, so the distinction
between a comparison and an equality matters even with one gap.

## What follows, and what does not

For a supplied finite law, the computation and (3) provide a numerical
evaluation of $Q$ and the mathematical comparison
$\mathcal K\in[3Q/5,Q]$. Since the proof also gives $T_h\le\mathcal K$,
the implementation returns the sharper interval
$[\max\{T_h,3Q/5\},Q]$. In particular it reports the singleton
$\{\rho\}$ in the proved saturation regime $h\ge t$.
Finite examples can check implementation behavior;
they do not establish (3) for all laws. The proof above establishes that
deterministic assertion at paper level.

Combining (3) with a statistical theorem is a separate step. For example, if
the general-law manuscript's bounds
$10^{-17}\mathcal K\le R\le33000\mathcal K$ are used, then
$6\cdot10^{-18}Q\le R\le33000Q$. This consequence inherits the
manuscript's paper-proof status and all its assumptions. It is not a new
Lean verification of the rare-event characterization. The independently
stated finite-law constants and their provenance remain as recorded in
[RESULTS.md](RESULTS.md#known-finite-gap-rare-events-paper-proof-characterization).

In particular, the functional and its inverse do not by themselves provide
a deterministic observation cap, a high-confidence radius, a data-computable
interval when the law is unknown, or executable code for the paper's
observable rare-event upper construction.

## Implementation and checks

The standard-library implementation is
[`rare_events.py`](../toolkit/threshold_toolkit/rare_events.py), with a
[command-line guide and example](../toolkit/README.md#3-compute-the-rare-event-rate-for-a-known-finite-law).
`FiniteGapLaw` prepares a weighted finite law and `RareEventProfile` prepares
its quantile split. `evaluate(B)` returns the terms of $Q$ and the comparison
interval; `budget_for_rate(target)` inverts $Q$ using (7). Logarithmic costs
avoid overflow in intermediate inverse moments, exact binary-float prefix
sums avoid cancellation in target-minus-prefix differences, and `frexp`
implements the dyadic convention above. These precautions do not constitute
interval certification.

The [analytic and boundary tests](../toolkit/tests/test_rare_events.py) are
complemented by an independently written
[rational/Decimal oracle](../toolkit/tests/test_rare_events_oracle.py).
The oracle evaluates mass and cost sums with exact rational arithmetic and
logarithms at 90 decimal digits; it also enumerates all 1,472 hard selections
across 13 small laws and four budgets per law. For a finite law this
enumeration evaluates $\mathcal K$ exactly: $G$ is concave and nonnegative,
so $\sqrt G$ is concave, and the band costs are linear in the selection
density $f\in[0,1]^n$. The objective is therefore concave on that box and
attains its infimum at a vertex. Its inverse check uses an
independent monotone search. These are finite implementation checks, separate
from the general proof. The
[command tests](../toolkit/tests/test_rare_event_cli.py) check installed-style
entry points, scope reporting, invalid input, and overflow output.

Run the whole toolkit suite from the repository root:

```sh
python -m unittest discover -s toolkit/tests -v
python toolkit/examples/rare_events.py
```
