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
proofs. The unrestricted infinite-coefficient case remains open.

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
[Segment](../lean/ThresholdHC/AnytimeLower/Segment.lean) and
[Embedding](../lean/ThresholdHC/AnytimeLower/Embedding.lean).

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

The existing infinite-cap duality identifies
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
Square-root budget scaling makes the expression inside the supremum
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

## Remaining target

When $C_{\mu,\rho}=\infty$, (6) proves divergence relative to the ordinary
iterated-logarithm scale. It does not yet compare the width to the full
budget-dependent quantity $\mathcal K(n/\log\log n)$. A proof of that
comparison needs control across hard families whose shape changes with the
budget. The sequential testing lemma, dual-limit identity and conclusions
(6)–(9) also remain to be formalized in Lean.
