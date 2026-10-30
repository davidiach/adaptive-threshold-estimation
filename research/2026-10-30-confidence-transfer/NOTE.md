---
title: "Confidence and hard budgets for adaptive threshold estimation"
subtitle: "A smoothing transfer from null-work obstructions to sharp confidence rates"
author: "Research contribution prepared for David Iach"
date: "30 October 2026 — Round 2"
---

# Result and verification boundary

This is an additive contribution to `davidiach/adaptive-threshold-estimation`, pinned to commit `6ad675e04570cc1ef6bece8e26beb81e1a176471`. It builds on, but does not modify, the round-one contribution *Certified computation of the entropy–tail rate*. The present result is statistical rather than another improvement of the deterministic comparison constant.

Write $K_{\mu,\rho}(B)$ for the repository's entropy–tail selection functional. Let $r^{\rm exp}_{\mu,\rho}(B,\delta)$ be the minimax error radius at failure probability $\delta$ under a uniform expected-flip budget $B$. Define $r^{\rm hard}$ by requiring the total number of flips to be at most $\lfloor B\rfloor$ on every execution. Put $\ell=\log(1/\delta)$.

**Main paper-proof extension.** In the original hidden-gap, hidden-sign experiment, for every probability law $\mu$ on $(0,1/2]$, $0<\rho\le1/4$, $B>0$, and $0<\delta\le1/4$,

$$
\boxed{
 r^{\rm exp}_{\mu,\rho}(B,\delta)
 \asymp r^{\rm hard}_{\mu,\rho}(B,\delta)
 \asymp K_{\mu,\rho}(B/\ell).
}
$$

The constants are universal. The upper algorithms may know $(\mu,\rho,B,\delta)$; no unknown-law adaptation is asserted. The lower bound permits randomized, nonlinear, fully adaptive creation, revisiting, interleaving, and unbounded stopping under the expected-work constraint.

The new proof is a **paper proof, not a Lean theorem**. Its smoothing inequality, adaptive KL transfer, confidence transfer, and hard-budget amplification are proved below. The general-law application imports the repository's paper-only common-pair theorem, null-work obstructions, and deterministic entropy packing, and imports its RMS upper construction. It does not independently validate those inherited ingredients. The critical-law corollary also has a shorter dependency path through the existing critical null-work obstruction and critical RMS upper bound, without the general-law entropy packing.

The implementation supplies an exact schedule and an observation-capping driver for an eligible base estimator. It does **not** implement the general-law rare-event base estimator, verify a caller's mean-squared-error assumption, or formally verify Python. Finite rational audits test the new bridge, not the universal statistical theorem. No literature-wide priority claim is made.

# Experiment and notation

A fresh coin has a latent magnitude $D\sim\mu$ and a latent sign $S\mid D=d\sim\operatorname{Ber}(q(d))$. Its successive flips are conditionally iid Bernoulli with probability $1/2+(2S-1)D$. Different fresh coins have independent latent states and observation tapes. A revisit keeps the same latent state. The algorithm sees its independent randomness and the purchased flips, not $D$ or $S$.

The admissible class is

$$
\mathcal Q_\rho(\mu)=\{q:0\le q\le1,\ \theta(q):=\textstyle\int q\,d\mu\le\rho\}.
$$

Rarity is a global integral constraint, not the pointwise constraint $q(d)\le\rho$. Algorithms may know the law and rarity bound but must be fixed before $q$ is supplied. Every physical observation costs one, including the first on a coin. Arithmetic is uncharged. Estimates can be clipped to $[0,\rho]$; the zero-work constant $\rho/2$ gives radius $\rho/2$ with failure probability zero.

For an algorithm $A$, let $T_A$ be its physical observation count. Work is infinite on nontermination. Define

$$
r^{\rm exp}(B,\delta)=\inf_{A:\ \sup_q E_qT_A\le B}
 \inf\{r\ge0:\sup_q P_q(|\widehat\theta_A-\theta(q)|>r)\le\delta\}.
$$

For $r^{\rm hard}$ replace the expected-work condition by $T_A\le\lfloor B\rfloor$ on every execution. Then $r^{\rm exp}\le r^{\rm hard}$.

Use the squared-Hellinger normalization

$$
\mathfrak h(P,Q)=1-\int\sqrt{dP\,dQ}
               =\frac12\int(\sqrt p-\sqrt q)^2.
$$

A local experiment means one genuine coin, an arbitrary independent auxiliary seed, and a capped observation policy. Conditional on its latent state, the policy is independent of the unknown sign law. Consequently its transcript law is affine in $q$. The law of a whole iid-coin population transcript is generally **not** affine in $q$.

The lower-bound subclass is

$$
X_\rho=\{q:0\le q\le1/2,\ \theta(q)\le\rho\}.
$$

Restricting the adversary to this subclass does not restrict the full upper guarantee. If $q\in X_\rho$, its one-coin latent law dominates one half of the all-negative latent law. Any nonnegative local work statistic therefore satisfies

$$
E_0T\le2E_qT. \tag{1}
$$

# Smoothing and adaptive KL transfer

## A universal smoothing inequality

**Lemma 1 (quarter smoothing).** For any probability measures $P,Q$, set

$$
P^\circ=\tfrac34P+\tfrac14Q,\qquad
Q^\circ=\tfrac14P+\tfrac34Q.
$$

Then, in both directions,

$$
\boxed{D_{\rm KL}(P^\circ\Vert Q^\circ)\le\tfrac83\mathfrak h(P,Q).} \tag{2}
$$

**Proof.** Use densities $p,q$ relative to $P+Q$. The smoothed measures have the same support. The elementary bound $D_{\rm KL}\le\chi^2$ follows from $\log x\le x-1$. Thus

$$
\begin{aligned}
D_{\rm KL}(P^\circ\Vert Q^\circ)
&\le\int\frac{(p-q)^2}{p+3q}\\
&=\int(\sqrt p-\sqrt q)^2\,
             \frac{(\sqrt p+\sqrt q)^2}{p+3q}\\
&\le\frac43\int(\sqrt p-\sqrt q)^2
 =\frac83\mathfrak h(P,Q).
\end{aligned}
$$

The last pointwise inequality is exactly

$$
4(x^2+3y^2)-3(x+y)^2=(x-3y)^2\ge0
$$

with $x=\sqrt p$, $y=\sqrt q$. The integrand is defined as zero when both densities vanish. Exchange $P,Q$ for the reverse direction. $\square$

No absolute continuity assumption on the original pair is needed. For example,

$$
P=(1-\eta,\eta,0),\quad Q=(1-\eta,0,\eta)
$$

have $\mathfrak h(P,Q)=\eta$ but infinite KL divergence. Their smoothed KL is only $(\eta/2)\log3$. This is why a Hellinger bound cannot simply be relabeled a KL bound in a high-confidence proof.

## A common local pair controls the adaptive population

**Theorem 2 (null-work Hellinger to population KL).** Suppose $q_-,q_+\in X_\rho$ satisfy, for every capped randomized local policy $A$,

$$
\mathfrak h(P_{q_-}^A,P_{q_+}^A)\le\kappa E_0T_A. \tag{3}
$$

Define fixed smoothed priors

$$
q_0=\tfrac34q_-+\tfrac14q_+,\qquad
q_1=\tfrac14q_-+\tfrac34q_+.
$$

They remain in $X_\rho$, and their target separation is one half of the original separation. Every population algorithm capped after $N$ observations satisfies

$$
\boxed{
D_{\rm KL}(\mathsf P_{q_0}^{(N)}\Vert\mathsf P_{q_1}^{(N)})
 \le\frac{16}{3}\kappa E_{q_0}T^{(N)}.
} \tag{4}
$$

The conclusion also holds for finitely many observable component types, each with its own pair satisfying (3) with the same coefficient. A type may be selected adaptively, but must be fixed before the coin's first observation and retained on revisits.

**Proof, one type.** Include the independent seed in the transcript and index coins by their first observation. There are at most $N$ slots. Under a fixed seed, a consistent global leaf $z$ gives a local observation word $h_i(z)$ for each slot, with the empty word for unused slots. Independence of the persistent latent states gives

$$
p_0(z)=\prod_i p_0(h_i(z)),\qquad
p_1(z)=\prod_i p_1(h_i(z)). \tag{5}
$$

The common policy-consistency indicator is implicit. The observation order can depend on all previous bits; (5) is not an independence claim about the adaptively stopped local words.

Let $\mathsf P_i$ be the hybrid with prior $q_1$ only in slot $i$ and prior $q_0$ in every other slot. Its likelihood ratio to the reference population is the local ratio for slot $i$. Hence, exactly,

$$
\frac{p_1(z)}{p_0(z)}
 =\prod_{i=1}^N\frac{p_i(z)}{p_0(z)},\qquad
D_{\rm KL}(\mathsf P_0\Vert\mathsf P_1)
 =\sum_{i=1}^N D_{\rm KL}(\mathsf P_0\Vert\mathsf P_i). \tag{6}
$$

Each slot ratio lies between $1/3$ and $3$, because it comes from quarter smoothing. There is therefore no integrability difficulty at a fixed cap.

To bound summand $i$, simulate every other coin under $q_0$ using auxiliary tapes. Put those tapes into the local policy's independent seed, leaving slot $i$ as its one genuine coin. This policy is fixed while the genuine coin's prior is varied among $q_-$, $q_+$, their smoothings, and zero. The common-pair hypothesis (3) applies to this policy. Its local transcript includes the auxiliary seed and determines the hybrid global transcript.

Affineness holds for the law of this one genuine coin. Lemma 1 and data processing give

$$
D_{\rm KL}(\mathsf P_0\Vert\mathsf P_i)
 \le\tfrac83\kappa E_0T_i^{\rm local}
 \le\tfrac{16}{3}\kappa E_{q_0}T_i^{\rm local}. \tag{7}
$$

The second inequality is (1), for this same fixed local policy and auxiliary-seed distribution. Summing local reference works counts each physical observation once, giving (4).

**Adaptive types.** Before a slot's first observation, generate its prehistory under the reference population. The selected type is determined by that prehistory. Conditional on it, the genuine coin is fresh with that type's prescribed law and is independent of remaining auxiliary randomness. Later reference coins can be generated from a preallocated independent array of potential tapes indexed by slot and type. Selecting a type never reveals the genuine coin's latent magnitude or sign. Apply (7) conditionally and integrate. The likelihood factorization (5) uses the selected type-specific kernel at each leaf; the hybrid identity remains exact. This proves the typed assertion. $\square$

The argument smooths **latent priors coin by coin**. It never assumes that smoothing a prior mixes whole population laws. For two deterministic-sign-observation coins with original sign probabilities $0$ and $1/4$, the smoothed prior $1/16$ gives probability $1/256$ of two positive signs. A $3/4$--$1/4$ mixture of the two original population laws gives probability $1/64$ instead.

## Unbounded stopping

The pair in (3) must work for **all** capped local policies and all caps before the population algorithm is considered. Fix that pair, its smoothings, the budget, and confidence level. Apply Theorem 2 at each deterministic observation cap $N$.

If the original algorithm has uniform expected work at most $B$, both smoothed endpoints have expected work at most $B$. Markov's inequality bounds each endpoint's overflow probability by $B/N$. Any terminal decision can be implemented in the capped experiment, with an arbitrary decision on overflow, changing its error probability by at most $B/N$. Taking $N\to\infty$ in the binary testing inequality below proves the same terminal lower bound. No cap-dependent re-selection of the pair or interchange with an unbounded likelihood sum is needed.

# Confidence transfer from a variance--null-work obstruction

## The inherited common-pair premise

The repository's `appendix-transfer-foundations.tex`, Theorem `thm:bias-transfer`, establishes the following statement as a paper proof. If every capped bounded one-coin output having uniform bias at most $b>0$ on $X_\rho$ satisfies

$$
\left(\sup_{q\in X_\rho}\operatorname{Var}_qY\right) E_0T\ge J,
\qquad 0<J<\infty,
$$

then for every $0<s\le b/3$ there is **one** oriented pair $q_-,q_+\in X_\rho$ with target separation at least $s$ such that

$$
\mathfrak h(P_{q_-}^A,P_{q_+}^A)
 \le42\frac{s^2}{J}E_0T_A \tag{CP}
$$

simultaneously for every capped randomized local policy. This quantifier order is essential. The present note imports (CP), including its proof's compactness/minimax step; it does not replace it with policy-dependent pairs or a finite numerical check.

## The confidence version

**Theorem 3 (confidence null-work transfer).** Under the same obstruction premise,

$$
\boxed{
 r^{\rm exp}_{\mu,\rho}(B,\delta)
 \ge\frac1{128}\min\left\{b,\sqrt{\frac{J\ell}{B}}\right\},
 \qquad \ell=\log(1/\delta).
} \tag{8}
$$

**Proof.** Choose

$$
s=\frac1{32}\min\{b,\sqrt{J\ell/B}\}.
$$

It is positive and at most $b/3$. Obtain the common pair from (CP), then smooth it as in Theorem 2. Its new target separation is at least $s/2$. At every global cap, its KL divergence is bounded by

$$
\frac{16}{3}\,42\,\frac{s^2 B}{J}
 =224\frac{s^2 B}{J}
 \le\frac7{32}\ell. \tag{9}
$$

An estimator of radius less than $s/4$, with failure probability at most $\delta$ at both endpoints, yields a midpoint test with both errors at most $\delta$. Data processing for KL then requires

$$
D_{\rm KL}\ge \operatorname{kl}(1-\delta,\delta)
 =(1-2\delta)\log\frac{1-\delta}{\delta}
 \ge\frac14\ell. \tag{10}
$$

Indeed $1-2\delta\ge1/2$, $1-\delta\ge1/2$, and $\ell\ge\log4=2\log2$. Equations (9) and (10) contradict one another because $7/32<1/4$. For unbounded stopping, use the fixed-pair cap passage described above; the capped test errors are at most $\delta+B/N$ and converge to $\delta$. Thus the radius is at least $s/4$, proving (8). $\square$

Notably, the numerical coefficient $1/128$ is the same as in the repository's RMS transfer, with $B$ replaced by $B/\ell$. The factors are exactly $1/32$ for the chosen original separation, $1/2$ for smoothing, and $1/2$ for midpoint testing.

## Additive localization at high confidence

Let $\sigma_i$ be finitely many nonzero submeasures with $\sum_i\sigma_i\le\mu$, masses $\tau_i$, and normalized laws $\nu_i=\sigma_i/\tau_i$. They need not have disjoint supports. Choose $0<r_i\le1/4$ with $\sum_i\tau_i r_i\le\rho$. Suppose the conditional experiment on $\nu_i$ has a variance--null-work obstruction $(b_i,J_i)$ as above on $X_{r_i}(\nu_i)$.

**Theorem 4 (confidence additive localization).**

$$
\boxed{
 r^{\rm exp}_{\mu,\rho}(B,\delta)
 \ge\frac1{128}\sum_i\tau_i
       \min\left\{b_i,\sqrt{\frac{J_i\ell}{B}}\right\}.
} \tag{11}
$$

**Proof.** For each component choose

$$
s_i=\frac1{32}\min\{b_i,\sqrt{J_i\ell/B}\}.
$$

Its common pair satisfies (CP) with coefficient at most $42\ell/(1024B)$, the **same** coefficient for every component. Orient the pairs in the same target direction and smooth each one. Theorem 2 for selected types bounds population KL by $7\ell/32$, while the target separation is at least $\tfrac12\sum_i\tau_i s_i$.

To transfer back to the original experiment, privately choose a component label for each fresh coin with probabilities $\tau_i$. Simulate the residual known all-negative law without genuine observations. Keep every label and latent state on revisits. For fractional restrictions the resulting original parameters are

$$
q_a(d)=\sum_i\frac{d\sigma_i}{d\mu}(d)q_{i,a}(d),\qquad a=0,1.
$$

They belong to $X_\rho$ because the density coefficients sum to at most one and their rarity contributions sum to at most $\rho$. Genuine oracle work is no greater than original work. The target difference is the sum of the weighted conditional differences. Midpoint testing and the unbounded-cap passage give (11). $\square$

Again the coefficient is unchanged from the RMS additive-localization theorem. This exact match lets the existing deterministic entropy packing be reused without losing another confidence-dependent factor.

# Hard-budget amplification from expected work and MSE

The upper construction is general. It does not use any special property of coins except the ability to run independent fresh copies and charge each observation.

**Theorem 5 (capped independent-block median).** Suppose an eligible base estimator, at expected-work allowance $b$, satisfies uniformly over the parameter class

$$
E T\le b,\qquad E(\widehat\theta-\theta)^2\le R(b)^2.
$$

For a hard budget $B>0$, let $m$ be the smallest positive odd integer with

$$
(3/4)^m\le\delta^2. \tag{12}
$$

Run $m$ independent base copies with allowance $b=B/(8m)$. Cap each copy after $\lfloor B/m\rfloor$ observations; on timeout return any fixed value. Return the median of their clipped outputs. Then total physical work never exceeds $B$, and

$$
P\left(|\widehat\theta_{\rm med}-\theta|>\sqrt8\,R(B/(8m))\right)
\le\delta. \tag{13}
$$

**Proof.** Couple each truncated block with its uncapped copy. Since work is integer-valued,

$$
\{T>\lfloor B/m\rfloor\}=\{T>B/m\},\qquad
P(T>B/m)\le\frac{B/(8m)}{B/m}=\frac18.
$$

Chebyshev's inequality bounds the uncapped output error above $\sqrt8R(b)$ by $1/8$. No independence of cost and estimation error within a block is required: a union bound makes its bad-output probability at most $1/4$.

The blocks themselves are independent. If $Z_j$ indicates a bad block, then $E3^{Z_j}\le3/2$. The median can be bad only if more than half the blocks are bad, so

$$
P(\text{bad median})
 \le3^{-m/2}\prod_j E3^{Z_j}
 \le(\sqrt3/2)^m\le\delta.
$$

Clipping does not increase error when the target belongs to the clipping interval. The observation driver caps each block separately, hence $T_{\rm total}\le m\lfloor B/m\rfloor\le B$ on every execution. $\square$

Condition (12) can be checked with integer arithmetic: for rational $\delta=u/v$, it is exactly $3^m v^2\le4^m u^2$. The implementation neither computes a small floating-point failure probability nor rounds a logarithm to select $m$.

For comparison, without timeouts use allowance $B/m$ per independent block. Chebyshev at radius $2R(B/m)$ already gives bad-block probability at most $1/4$, yielding an expected-budget confidence upper bound at that radius.

**Block-count bound.** Since $\log(4/3)>1/4$, an odd integer at least $8\ell$ satisfies (12). Consequently

$$
m\le8\ell+2\le10\ell \qquad(\delta\le1/4). \tag{14}
$$

Also $m\ge2\ell/\log(4/3)>\ell$. The proof is deliberately conservative; the exact schedule is smaller than the $8\ell$ prescription in many cases.

Only a first work moment and a second error moment are needed. No exponential tail for a base run's work, deterministic per-coin depth, or independence between a run's cost and output is assumed. The result caps observations, not CPU time, memory, or arbitrary callback behavior.

# The general-law confidence characterization

## Functional and scaling

For canonical bands $I_j=(2^{-(j+2)},2^{-(j+1)}]$, write

$$
a_j(\sigma)=\int_{I_j}d^{-2}\sigma(dd),\quad
G(a)=A+\sum_j a_j\log(A/a_j),\quad A=\sum_j a_j,
$$

and let $\Gamma_\sigma$ be the supremum of finite-prefix values. With $h=B^{-1/2}$,

$$
K_{\mu,\rho}(B)=\min\left\{\rho,
 \inf_{0\le\sigma\le\mu}
 \left[h\sqrt{\rho\Gamma_\sigma}
       +\int\min\{1,h/d\}(\mu-\sigma)(dd)\right]\right\}.
$$

For every $c\ge1$,

$$
K(B/c)\le\sqrt c\,K(B). \tag{15}
$$

For a fixed selection, the entropy term scales by $\sqrt c$, and $\min(1,\sqrt c\,x)\le\sqrt c\min(1,x)$. Infima and the outer cap preserve the inequality. No smoothness, finite moment, or regular-variation hypothesis is involved.

## Reassembling the lower bound

The pinned general-law lower proof has two statistical inputs. Both are variance--null-work obstructions followed by the transfers replaced above.

First, for

$$
\Psi_{\mu,\rho}(h)=\sup_{0\le w\le1,\ \int w\,d\mu\le\rho}
 \int\min\{w(d),h\sqrt{w(d)}/d\}\,\mu(dd),
$$

the inherited Proposition `prop:psi-null` states

$$
\mathfrak J_0(b)\ge
 \sup_{h>0}\frac{(\Psi(h)-4b)_+^2}{192h^2},
 \qquad 0\le b\le\rho/64. \tag{16}
$$

Evaluate at $h=\sqrt{\ell/B}$ and set $b=\Psi(h)/64$. Choosing

$$
J=\frac{(15\Psi(h)/16)^2}{192h^2}
$$

in Theorem 3 gives, with exactly the same arithmetic as the RMS proof,

$$
r^{\rm exp}(B,\delta)\ge\Psi(\sqrt{\ell/B})/8192. \tag{17}
$$

Second, the inherited separated-annulus obstruction `prop:scaled-annular` supplies conditional parameters

$$
b_i=r_i/64,\qquad
J_i=c_{\rm ann}\min\{r_i\Gamma_i^\circ,w_{*,i}/a_i^2\},\qquad
c_{\rm ann}=e^{-28}/2000000. \tag{18}
$$

Here $\Gamma_i^\circ$ and $w_{*,i}$ are conditional cost entropy and minimum band mass, and $a_i$ bounds the support. Theorem 4 applies with these same parameters. Crucially, the original minimum-band-mass saturation constraint is retained; it is not replaced by an inverse-gap moment.

Now run the deterministic finite-prefix selection and packing argument in `appendix-entropy-tail-lower.tex` at the effective budget

$$
B'=B/\ell.
$$

Its canonical factor-two comparison, optimal-band inequalities, ordinary/ignored-cost estimates, entropy tiers, parity split, trimming, and rarity allocation are deterministic statements at a positive budget. None changes with the risk criterion. Equation (17) supplies its ordinary/ignored contribution; equation (11), with (18), supplies its retained-entropy contribution. Both statistical replacements have exactly the coefficients used in the original assembly, at $B'$.

In particular, if the retained entropy is $F$, the construction gives disjoint components with $\sum_iG_i\ge F/896$ and $\theta_i/G_i=\lambda^2/1024$, $\lambda^2=\rho/F$. Their confidence contributions share one crossover because

$$
\sum_i\min\{\theta_i,\sqrt{\theta_iG_i\ell/B}\}
 =\left(\sum_iG_i\right)
   \min\{\lambda^2/1024,\lambda\sqrt{\ell/B}/32\}.
$$

Thus the original finite-prefix lower comparison holds for $r^{\rm exp}(B,\delta)$ and $K(B')$. The omitted tail probability tends to zero at the fixed $(\mu,\rho,B,\delta)$, exactly as in the pinned proof. No uniform truncation depth or new infinite-dimensional optimization is asserted.

Keeping the repository's conservative arithmetic yields

$$
\boxed{r^{\rm exp}(B,\delta)\ge10^{-17}K(B/\ell).} \tag{19}
$$

This application depends on (16), (18), (CP), and the inherited deterministic packing. It is not an inference from an RMS minimax inequality alone: a generic RMS lower bound would not justify (19).

## Upper bound and explicit constants

The pinned paper supplies $R_{\mu,\rho}(b)\le33000K_{\mu,\rho}(b)$ for every positive $b$. Apply Theorem 5 to its upper family. If the infimum is not attained, choose arbitrarily small risk slack and pass to the infimum; attainment is not needed.

Combining (13)--(15),

$$
\begin{aligned}
r^{\rm hard}(B,\delta)
&\le\sqrt8\,(33000)K(B/(8m))\\
&\le8(33000)\sqrt{m/\ell}\,K(B/\ell)\\
&\le8(33000)\sqrt{10}\,K(B/\ell)
 <840000K(B/\ell).
\end{aligned}
$$

The uncapped median similarly gives $r^{\rm exp}(B,\delta)\le210000K(B/\ell)$.

**Theorem 6 (general-law confidence and hard budgets).** Subject to the inherited paper-proof ingredients identified above,

$$
\boxed{
10^{-17}K(B/\ell)
 \le r^{\rm exp}(B,\delta)
 \le r^{\rm hard}(B,\delta)
 \le840000K(B/\ell).
} \tag{20}
$$

Both upper radii can additionally be capped by the trivial $\rho/2$. This establishes the main rate statement. The constants are conservative theoretical constants, not practical flip recommendations.

# Consequences

## Critical quadratic confidence

For the repository's critical law $\mu(dd)=32d\,dd$ on $(0,1/4]$, let

$$
L=1+\log(1/\rho),\qquad H=1+\log L.
$$

The confidence rate, under either budget convention, is

$$
\boxed{
 r(B,\delta)\asymp
 \min\left\{\rho,\sqrt{\frac{\rho L H\log(1/\delta)}{B}}\right\}.
} \tag{21}
$$

There is a shorter proof than Theorem 6: the existing critical null-work obstruction has $b=\rho/64$ and $J=c_0\rho LH$. Theorem 3 supplies the confidence lower bound. The existing critical RMS upper bound and Theorem 5 supply the hard-budget upper bound. Thus this corollary does not need the arbitrary-law entropy packing or the round-one $8/5$ comparison.

At nontrivial accuracy $\varepsilon$ sufficiently smaller than $\rho$, the resulting sample-complexity order is

$$
B\asymp\frac{\rho L H}{\varepsilon^2}\log(1/\delta).
$$

The scale-entropy factor $H$ multiplies the confidence logarithm. It is not replaced by $H+\log(1/\delta)$. This conclusion follows from the common-pair lower argument; median amplification by itself would establish only an upper bound.

## Above the quadratic boundary and the fixed-gap anchor

For an exact power law $F(d)=(d/a)^\alpha$ on $(0,a]$ with fixed $\alpha>2$,

$$
\boxed{
 r(B,\delta)\asymp_\alpha
 \min\left\{\rho,\frac{\sqrt{\rho\log(1/\delta)}}{a\sqrt B}\right\}.
} \tag{22}
$$

Constants may depend on the fixed exponent; no uniform bound as $\alpha\downarrow2$ is claimed. The known power-envelope RMS upper constructions can also be amplified without acquiring a requirement to know the exact law, provided their original uniform work/MSE assumptions hold.

For a point mass $\mu=\delta_d$, equation (20) reduces to

$$
r(B,\delta)\asymp\min\{\rho,\sqrt{\rho\log(1/\delta)/(Bd^2)}\},
$$

in agreement with the known fixed-gap rare-mixture result of Lee and Valiant. That special case and the general hybrid-decomposition mechanism are antecedents, not new results claimed here.

## Connection to round one

Round one proved $K\le Q\le(8/5)K$ for the closed quantile functional. Applied at the effective budget $B/\ell$, it gives a closed-form confidence-rate characterization as well:

$$
r^{\rm exp}(B,\delta)\asymp r^{\rm hard}(B,\delta)\asymp Q(B/\ell).
$$

Writing $h_\delta=\sqrt{\ell/B}$, and removing exactly the smallest-gap mass $\rho$ to obtain $\nu$ with core $\kappa=\mu-\nu$,

$$
Q(B/\ell)=\min\left\{\rho,
 \int\min(1,h_\delta/d)\,\nu(dd)
 +\sqrt{\frac{\rho\Gamma_\kappa\ell}{B}}\right\}.
$$

The earlier numerical certificates enclose this deterministic functional. They do not become executable-estimator risk certificates merely by changing the budget input. The statistical interpretation still needs the theorem and constants above, an eligible upper algorithm, and its implementation assumptions.

# Implementation and finite audits

## Observation-capping driver

`toolkit/threshold_toolkit/confidence_amplification.py` is standard-library-only. `MedianSchedule` computes the least odd block count satisfying (12) by exact integer comparisons, records $B/(8m)$ as a rational, and sets the block cap to $\lfloor B/m\rfloor$. `verify_schedule_record` recomputes a record against separately supplied expected parameters and rejects altered, missing, or extra fields. This is deterministic replay, not an independent proof checker.

A base estimator is an interactive generator. It yields a nonnegative local coin ID to request an observation and returns its estimate to stop. The driver alone calls the observation source. A new ID creates a latent coin at its first purchased observation, while repeated IDs revisit it. IDs are independently namespaced for each block. Exactly reaching the cap and then returning is accepted; requesting another flip causes a timeout before that extra flip is purchased. Unused work is not reallocated between blocks.

The program receives its own randomness and returned bits, but not a direct observation callback or the source RNG. Exact rational estimates remain rational through clipping and median selection; only optional display conversion uses floats. NaN, infinity, malformed IDs, and invalid observation outputs are errors, not silently accepted estimates. Exceptions propagate.

The caller must supply a valid base estimator and independent population source. Python's pseudorandom streams support reproducible experiments but are not a formal proof of probabilistic independence or a security boundary against adversarial callback code. Physical observations are capped; CPU execution inside callbacks is not. A program that loops without yielding is outside the claimed wall-clock behavior.

## Audits actually run

The new unit suite has **29 passing tests**. It covers exact block selection, failure-bound arithmetic, tiny rational failure probabilities (including $10^{-1000}$), floor budgets, zero-cap blocks, corrupted records, exact cap completion, endless observation requests, source-call counting, revisits, interleaving, independent block namespaces, rational output preservation, error handling, generator cleanup, reproducibility, and 100 randomized control-flow budget cases.

`verify_transfer.py` independently constructs rational finite experiments. Its current deterministic run contains:

| Check | Count |
|:---|---:|
| Categorical pairs, including singular originals | 202 |
| Directed smoothing inequalities with rational enclosures | 404 |
| Adaptive population policies | 48 |
| One-slot hybrid experiments | 216 |
| Exact leaf likelihood-factorization identities | 1,198 |
| Null-work domination checks | 216 |
| Exact expected-work partitions | 48 |
| KL sum comparisons by enclosing intervals | 48 |

The policies include adaptive creation, persistent revisits, interleaving, pre-observation type selection depending on observed history, and early stopping. Transcendental bounds use an integer-square-root enclosure and a rational logarithm series with a rigorous remainder, not a floating-point tolerance. The proof's pointwise square identity and its rational constant arithmetic are also checked.

These are finite tests of the new transfer, not a proof of (CP), the annular obstruction, the full minimax theorem, or Python correctness. The paper proof is the source of universal quantifiers. The numeric checks can catch implementation and normalization mistakes but cannot replace that proof.

The reproduction also executes an elementary known-single-gap base at $B=10^6$, $\rho=1/4$, $\delta=1/100$, and gap $1/4$. It used 33 blocks of 3,787 fresh one-flip coins: **124,971 actual observations**, with no timeouts. For the illustrative true fraction $1/10$, it returned $733/7574\approx0.09677845$. Its analytic uniform radius bound is $\sqrt{8/3787}\approx0.04596$. This is one execution, not an empirical coverage estimate, and this elementary base is not the general-law optimal estimator.

# Integration and unresolved boundaries

The patch adds new paths only. It does not alter any frozen statement, hash lock, source manuscript, published PDF, existing audit record, or the separate open calculator PR. No GitHub write or new CI run is claimed. The complete upstream test suite and Lean kernel have not been rebuilt in this environment; a full clone was unavailable. The new tests and finite audits were actually executed locally.

For formalization, a useful dependency order is: quarter-smoothing KL; capped hybrid KL factorization; reference/null work domination; confidence transfer against the existing common-pair statement; typed additive localization; the fixed-pair cap limit; hard-budget median amplification; and the unchanged deterministic entropy packing at the effective budget. Each formal target should quantify the observable algorithm class before a proof is attempted. An unconditional Lean claim for the general-law result additionally requires its inherited paper-only ingredients to be formalized.

This round does not prove unknown-law adaptation, optimize the statistical constants, implement the general-law base estimator, establish a simultaneous-in-budget confidence sequence, or equate deterministic-budget **RMS** risk with expected-budget RMS risk. The hard-budget equivalence proved here concerns the confidence-radius problem. A different estimator can be used for each $(B,\delta)$.

The work is a proposed mathematical extension relative to the pinned repository. It has not received external specialist review and is not represented as an independent review of its own inherited proof chain. A completed wider-literature priority survey has not been performed.

# References and exact dependencies

**[R1]** David Iach, *Adaptive Threshold Estimation*, pinned commit `6ad675e04570cc1ef6bece8e26beb81e1a176471`, `docs/WORKPLAN.md`, `docs/RESULTS.md`, and the consolidated v6 manuscript. At this checkpoint sharp rare-event confidence rates at and above the quadratic boundary are listed as open research.

**[R2]** Same repository, `paper/v6/appendix-transfer-foundations.tex`, Theorem `thm:bias-transfer` and equation `eq:bias-common-pair`: the policy-uniform common-pair premise (CP); Proposition `prop:psi-null`: (16); Theorem `thm:additive-localization`: the RMS predecessor of (11). Blob identity: `9a1a501fbee10d8a2f9dab0ad83648019c5f00c6`.

**[R3]** Same repository, `paper/v6/appendix-lower-foundations.tex`, Proposition `prop:scaled-annular`: the conditional annular variance--null-work obstruction (18). Its minimum-band-mass branch must remain present.

**[R4]** Same repository, `paper/v6/appendix-entropy-tail-lower.tex`, the canonical-prefix comparison, finite-selection optimality, entropy-tier grouping, trimming, saturation and rarity allocation, and the final explicit constants. Blob identity: `279cb89b70af692b136d96bb5abaa97aa9990660`. This deterministic assembly is reused at $B/\ell$, with its two statistical transfers explicitly replaced.

**[R5]** Same repository, `paper/v6/appendix-entropy-tail-upper.tex` and the explicit-constant calculation at the end of [R4]: the all-positive-budget RMS family with comparison constant 33000. Existence of this family, not just a numerical value of $K$, is needed by Theorem 5.

**[R6]** Same repository, `paper/v6/appendix-critical.tex`, Theorem `crit:thm:base-cost` and the critical upper construction: the shorter dependency path to (21). The corresponding existing critical statistical statements have Lean results; this new confidence extension does not.

**[R7]** Same repository, `paper/v6/appendix-localization.tex`, Lemma `loc:lem:hybrid`: the existing bounded-relative-change hybrid mechanism. The present proof uses exact KL decomposition after local prior smoothing, instead of assuming bounded ratios for the original common pair.

**[R8]** Jasper C. H. Lee and Paul Valiant, *Uncertainty about Uncertainty: Optimal Adaptive Algorithms for Estimating Mixtures of Unknown Coins*, arXiv:1904.09228, SODA 2021. Primary abstract and author publication listing checked during this round. Fixed-gap confidence rates and adaptive hybrid decomposition are established antecedents.

**[R9]** Round-one contribution, *Certified computation of the entropy–tail rate*, 30 October 2026, supplied package `adaptive_threshold_improvements_2026-10-30.zip`. The $8/5$ comparison is used only in the optional closed-$Q$ corollary, not the core confidence transfer.

Code is Apache-2.0. This note and explanatory documentation are CC BY 4.0, consistent with the repository's license split.
