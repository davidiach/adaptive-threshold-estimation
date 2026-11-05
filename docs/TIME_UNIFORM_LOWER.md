# Gap-law-dependent time-uniform lower bounds

This development uses the original hidden-gap experiment, a known positive-gap
probability law $\mu$, and $0<\rho\le1/4$. One online controller reports an
interval after each integer physical flip budget. Its deterministic half-width
envelope $t(n)$ is nonincreasing. For every admissible sign prior, simultaneous
coverage and the width bound must hold together with probability at least
$1-\delta$, where $0<\delta\le1/4$.

The target is a lower bound at the known-law upper scale
$\mathcal K_{\mu,\rho}(n/[\log(1/\delta)+\log\log n])$ infinitely often.
The native development begins with a quadratic information bound along prior
segments. The sequential argument and asymptotic consequences below are paper
proofs. The final section proves the matching comparison for arbitrary positive-gap laws.

## A prior segment in the original experiment

Write $I_\mu(q,r)$ for the infinite-cap information/work ratio with the midpoint
of $q,r$ as both references. Suppose $I_\mu(q,r)\le J<\infty$.
For $x\in[3/8,5/8]$, let $q_x=xq+(1-x)r$. Every member remains admissible
whenever the two endpoints are admissible. For any adaptive controller and
physical prefix of length $n$,
\[
 D_{\rm KL}(P_{q_x}^{(n)}\Vert P_{q_y}^{(n)})
 \le {64\over3}Jn(x-y)^2.                                      \tag{1}
\]
The prefix includes the private seed and actual observed tape. Revisits and
adaptive acquisition are included.

To see this, set $a=(3x-y)/2$ and $b=(3y-x)/2$. Both belong to $[0,1]$,
their sum lies in $[1/2,3/2]$, and quarter smoothing the pair $q_a,q_b$
gives $q_x,q_y$. Each midpoint reference dominates half the original midpoint.
Its variance denominator and work denominator therefore lose at most a factor
two each. The numerator scales by $(a-b)^2$, so
\[
 I_\mu(q_a,q_b)\le4(a-b)^2 I_\mu(q,r).
\]
The existing midpoint reference bound and observable KL transfer give (1),
because $a-b=2(x-y)$ and actual prefix work is at most $n$.

The native statements are in
[Segment](../lean/ThresholdHC/AnytimeLower/Segment.lean),
[Embedding](../lean/ThresholdHC/AnytimeLower/Embedding.lean), and
[Quartet](../lean/ThresholdHC/AnytimeLower/Quartet.lean). The first checkpoint has [11 exact statements and axiom audits](../results/anytime-lower-family-20261105/README.md).

## A sequential testing lemma

Here is the needed extension to dependent observations. Suppose one consistent
experiment has prefix laws $P_\theta^{(n)}$ on a common filtration, with
$\theta\in[\theta_0,\theta_0+r]$, $r>0$, and
\[
 D_{\rm KL}(P_\theta^{(n)}\Vert P_{\theta'}^{(n)})
       \le Mn(\theta-\theta')^2,\qquad M>0.                     \tag{2}
\]
Any simultaneously valid deterministic error envelope satisfies
\[
 \limsup_{n\to\infty}t(n)\sqrt{n/\log\log n}
       \ge \sqrt{(1-\delta)/(72M)}.                             \tag{3}
\]
An interval midpoint has the required error bound on the joint coverage and
width event. Define its midpoint arbitrarily when the interval is empty.

The proof uses finite Cantor families. For binary words $v$ of length $L$, set
\[
 \theta_v=\theta_0+2r\sum_{j=1}^L v_j3^{-j}.
\]
Two parameters whose first $k$ bits differ are separated by at least $r3^{-k}$.
Parameters sharing their first $k-1$ bits differ by at most $r3^{-(k-1)}$.
If $t(n_k)<r3^{-k}/2$, nearest-parameter decoding at $n_k$ recovers the
first $k$ bits on the coverage event.

For each prefix $b$ of length $k-1$, condition on earlier decoded bits being
correct. This event has probability at least $1-\delta$ under every parameter
extending $b$. Conditional KL is at most unconditional KL divided by this
probability. Pairing opposite next bits and applying the two-point
Bretagnolle–Huber bound gives average conditional error at least
\[
 {1\over4}\exp\!\left\{-{Mn_kr^2\,9^{-(k-1)}\over1-\delta}\right\}.
\]
Average uniformly over all finite words. For each word, first-error events
are disjoint and their total probability is at most $\delta$. Thus
\[
 \sum_{k=1}^L
 \exp\!\left\{-{Mn_kr^2\,9^{-(k-1)}\over1-\delta}\right\}
       \le {4\delta\over1-\delta}.                             \tag{4}
\]
The same argument applies after fixing any finite initial bit prefix.

For $k\ge2$, take
$n_k=\lfloor c9^k\log k\rfloor$ with
$c=(1-\delta)/(18Mr^2)$. The exponential terms in (4) are at least
$k^{-1/2}$, whose sum diverges. Hence
$t(n_k)\ge r3^{-k}/2$ infinitely often. Since
$n_k/(9^k\log k)\to c$ and $\log\log n_k/\log k\to1$, (3) follows.
The common filtration makes the earlier decoding events measurable at $n_k$.
Independence of successive observations is unnecessary.

This adapts the sequential testing method of Duchi and Haque. The finite-word
argument above explicitly uses closeness for a prefix of length $k-1$ when
testing bit $k$. [Duchi and Haque, COLT 2024](https://proceedings.mlr.press/v247/duchi24a.html)

## The law-dependent coefficient

For an admissible four-prior certificate $Q$, put
$\Delta_Q=(\theta(Q_H)-\theta(Q_L))_+$ and
$I_Q=I_\infty(\mu,Q)$. Define the extended coefficient
\[
 V_{\mu,\rho}
   =\sup_{\substack{Q\ {\rm admissible}\\J>0,\ I_Q\le J}}
        {\Delta_Q^2\over J}.                                  \tag{5}
\]
Reference absorption gives admissible endpoints with gap $\Delta_Q/3$ and
midpoint information at most $J$. Parameterizing their central segment by its
actual mean turns (1) into (2) with
$M=192J/\Delta_Q^2$. Equation (3) and $13824<128^2$ yield
\[
 \limsup_{n\to\infty}t(n)\sqrt{n/\log\log n}
       \ge {\sqrt{1-\delta}\over128}\sqrt{V_{\mu,\rho}}.         \tag{6}
\]
The bound holds for each positive-gap certificate before taking the supremum.
If $V_{\mu,\rho}=\infty$, its meaning is that the limsup is infinite.

The existing [infinite-cap duality](../lean/ThresholdHC/Genie/InfiniteDuality.lean) identifies
\[
 V_{\mu,\rho}=\sup_{B>0}B P_\infty(B)^2
            =\lim_{B\to\infty}B P_\infty(B)^2.                 \tag{7}
\]
Indeed, after multiplying the dual identity by $B$, each term is
$\Delta_Q^2/(4/B+I_Q)$, increasing in $B$. Suprema over $B,Q$ commute.
For $0<I_Q<\infty$ the limit is $\Delta_Q^2/I_Q$. A zero information
coefficient gives zero when $\Delta_Q=0$ and infinity otherwise. Infinite
information contributes zero. These are exactly the cases included by (5).

## Matching when the asymptotic coefficient is finite

Let
\[
 C_{\mu,\rho}=\sup_{B>0}\sqrt B\,\mathcal K_{\mu,\rho}(B).
\]
[Square-root budget scaling](../lean/ThresholdHC/HardBudget/SelectionScale.lean) makes the expression inside the supremum
nondecreasing. The existing comparisons
$10^{-17}\mathcal K(B)\le R(B)\le P_\infty(B)\le8R(B)\le224000\mathcal K(B)$
give
\[
 10^{-17}C_{\mu,\rho}\le\sqrt{V_{\mu,\rho}}
        \le224000 C_{\mu,\rho}.                               \tag{8}
\]
If $C_{\mu,\rho}<\infty$, positivity of the selection functional implies
$0<C_{\mu,\rho}<\infty$. Equations (6)–(8) give the matching lower bound
\[
 \limsup_{n\to\infty}
 {t(n)\over\mathcal K_{\mu,\rho}(n/\log\log n)}
 \ge {\sqrt{1-\delta}\over128\cdot10^{17}}.                     \tag{9}
\]
For each fixed $\delta$, inserting $\log(1/\delta)$ in the budget inflation
has the same asymptotic conclusion. The existing known-law upper bound and
(9) therefore match up to universal constants, including their dependence on
the fixed law and rarity.

This includes every law with finite inverse moment
$I_\mu=\int d^{-1}\,d\mu<\infty$, because selecting the empty core gives
$\mathcal K(B)\le I_\mu/\sqrt B$. In particular it includes all finite-support
positive-gap laws. No lower bound on the support is required for the
finite-inverse-moment conclusion.

## Infinite inverse moment

Assume $I_\mu=\infty$. Choose $0<\tau\le1/4$ with
$0<\mu((0,\tau])\le\rho/2$, and set $S=(0,\tau]$ and
$T(h)=\int_S\min(1,h/d)\,d\mu$.
The mass-$\rho$ quantile threshold is above $\tau$. The quantile core has finite
entropy and the quantile tail above $\tau$ has finite inverse moment.
Since $T(h)/h\to\infty$, the checked $8/5$ comparison gives, eventually as $h\downarrow0$,
\[
 (5/8)T(h)\le\mathcal K(h^{-2})\le2T(h).                       \tag{10}
\]

### Bounded prior profiles

Set $\varepsilon_j=\tau4^{-j}$ and
\[
 f_j(d)={\varepsilon_j\over d}\mathbf1_{\{\varepsilon_j<d\le\tau\}},
 \quad a_j=\int f_j\,d\mu,\quad W_j=\sum_{i\ge j}a_i.
\]
Geometric summation gives
\[
 T(\varepsilon_j)/3\le W_j\le4T(\varepsilon_j)/3,\quad
 W_{j+1}\ge W_j/4,\quad W_j\downarrow0,\quad W_j>0.             \tag{11}
\]
For $d>\varepsilon_j$, the pointwise sum is $4\varepsilon_j/(3d)$.
For $0<d\le\varepsilon_j$, start at the first index with $\varepsilon_i<d$.
The sum lies in $[1/3,4/3]$. The strict indicator handles atoms at grid endpoints.

Let $j_1=0$, and let $j_{k+1}$ be the first index after $j_k$ with
$W_{j_{k+1}}\le W_{j_k}/4$. Then
$W_{j_k}/16<W_{j_{k+1}}\le W_{j_k}/4$.
For a finite binary word $v$ of length $L$, define
\[
 q_v(d)={1\over4}\mathbf1_S(d)+{3\over128}
     \sum_{k=1}^L v_k\sum_{j=j_k}^{j_{k+1}-1}f_j(d).
\]
This lies in $[1/4,9/32]$ on $S$, is zero outside $S$, and is admissible.
Its block-$k$ mean increment is $(3/128)(W_{j_k}-W_{j_{k+1}})$.
Parameters whose first $k$ bits differ are separated by at least
\[
 \delta_k=(3/256)W_{j_k}.                                    \tag{12}
\]
If their first $k-1$ bits agree, then at every gap
\[
 d\,|q_v(d)-q_w(d)|\le\varepsilon_{j_k}/32.                   \tag{13}
\]
Both bounds hold uniformly in finite depth $L$.

### Information under adaptive observation

Augment the transcript with the whole iid gap sequence, whose distribution
is independent of the sign prior. The controller still uses its original
seed and observed flips. Forgetting the extra gaps gives the original
experiment, so data processing makes its KL no larger.
Conditional on the augmented seed and an observed history, a queried coin has sign
likelihoods $A,B\ge0$, $A+B>0$. Its posterior sign probability is
$\pi(q)=qA/[qA+(1-q)B]$.
For $q,r\in[1/4,3/4]$, both denominators are at least $(A+B)/4$, so
\[
 |\pi(q)-\pi(r)|
 ={AB|q-r|\over[qA+(1-q)B][rA+(1-r)B]}\le4|q-r|.
\]
Thus the next-head probabilities differ by at most
$8d|q-r|\le\varepsilon_{j_k}/4$ on $S$. Both are in $[1/4,3/4]$.
The Bernoulli chi-square bound gives one-step KL at most
$\varepsilon_{j_k}^2/3\le\varepsilon_{j_k}^2$.
Outside $S$, the two conditional laws agree.

Given the history and seed, the adaptive action is the same function under
both hypotheses. The queried coin's posterior uses its own flips, and revisits
retain its latent sign. Chain rule over at most $n$ physical flips, followed
by forgetting the revealed gaps, gives
\[
 D_{\rm KL}(P_v^{(n)}\Vert P_w^{(n)})\le n\varepsilon_{j_k}^2   \tag{14}
\]
whenever the first $k-1$ bits agree. The posterior and per-flip inequalities
are checked in [TailInformation](../lean/ThresholdHC/AnytimeLower/TailInformation.lean);
the adaptive chain-rule transfer here remains a paper proof.

### Two possible spacings of the blocks

First suppose $j_k\le k^2$ eventually. Take
$n_k=\lfloor(1-\delta)\varepsilon_{j_k}^{-2}\log k/2\rfloor$.
The finite-tree argument of (4), using (12) and (14), forces
$t(n_k)\ge(3/512)W_{j_k}$ infinitely often. Otherwise its error sum would
dominate $\sum k^{-1/2}$.

Put $\lambda(n)=\log(1/\delta)+\log\log n$. Eventually
$\lambda(n_k)\le4\log k$ and
$n_k\ge(3/16)\varepsilon_{j_k}^{-2}\log k$. Hence
$\sqrt{\lambda(n_k)/n_k}\le5\varepsilon_{j_k}$.
By (10), (11) and $T(5h)\le5T(h)$,
$\mathcal K(n_k/\lambda(n_k))\le30W_{j_k}$.
The ratio of the envelope to this functional is at least $1/5120$
infinitely often.

Otherwise $j_k>k^2$ infinitely often. There are then infinitely many blocks
with $j_{k+1}-j_k\ge\sqrt{j_k}$. If all late increments were smaller,
$\sqrt{j_{k+1}}\le\sqrt{j_k}+1/2$ would imply
$j_k\le(k/2+O(1))^2<k^2$ eventually.

On each such long block put
$m_k=j_k+\lfloor\sqrt{j_k}/2\rfloor$ and
$n_k=\lceil\varepsilon_{m_k}^{-2}\rceil$.
Eventually $m_k+1<j_{k+1}$ and
\[
 \varepsilon_{m_k+1}\le n_k^{-1/2}
 \le\sqrt{\lambda(n_k)/n_k}\le\varepsilon_{j_k}.
\]
The inflation shifts a geometric gap index by $O(\log\log j_k)$,
whereas the distance to the block's start is of order $\sqrt{j_k}$.
Also $W_{m_k+1}>W_{j_k}/4$. Therefore
\[
 \mathcal K(n_k)\ge(15/128)W_{j_k},\qquad
 \mathcal K(n_k/\lambda(n_k))\le6W_{j_k}.
\]
In particular their ratio is at least $1/96$.
The [fixed-budget confidence lower bound](../lean/ThresholdHC/ConfidenceProgram/Lower.lean), using its conservative coefficient
$10^{-17}/30$, now yields
\[
 {t(n_k)\over\mathcal K(n_k/\lambda(n_k))}\ge10^{-17}/2880.     \tag{15}
\]
A physical cap implies an expected-work bound. The reported interval's midpoint
is a fixed-budget estimator with error at most $t(n)$ on its coverage event.

## Matching theorem for every positive-gap law

Every nonincreasing deterministic half-width envelope in the original online
experiment, with joint coverage and width probability at least $1-\delta$
for each admissible population, satisfies
\[
 \boxed{\displaystyle
 \limsup_{n\to\infty}
 {t(n)\over\mathcal K_{\mu,\rho}
       (n/[\log(1/\delta)+\log\log n])}\ge10^{-22}.}            \tag{16}
\]
Here $\mu$ is any known probability law on $(0,1/2]$,
$0<\rho\le1/4$, and $0<\delta\le1/4$. The limsup uses integer budgets
large enough for the logarithms to be defined.

For finite inverse moment, (9) gives (16). For infinite inverse moment,
the two block-spacing cases give it. These cases exhaust all laws.
The known-law upper inflation is asymptotic to $2\log\log n$ at fixed
$\delta$. Square-root budget scaling compares it to the inflation in (16)
by a universal factor. This proves matching law and rarity dependence in
the asymptotic deterministic-envelope sense.

The complete matching theorem is a paper proof. The native audit checks
the common-family information bounds and the posterior and per-flip KL inequalities.
The sequential testing lemma, infinite-moment construction, its acquisition-law
transfer and the asymptotic comparisons remain to be formalized in Lean.

Run `python tools/verify_anytime_lower_profiles.py` for 32,768 exact rational
profile comparisons across 16 finite atomic examples, including grid endpoints.
These are regression examples, not a proof for arbitrary laws.
