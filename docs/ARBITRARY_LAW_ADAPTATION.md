# Eventual oracle-rate adaptation over arbitrary unknown gap laws

This is a **paper proof**, with an executable construction. Its
[entropy and selection transport, CDF-envelope and observable-stage components](ARBITRARY_LAW_FORMALIZATION.md)
are now Lean-checked; the full theorem and Python execution are not formally verified. The previous
[tail-certificate theorem](ARBITRARY_LAW_TAIL.md) supplies the single-coin
probe and its physical work bound. The additional steps here are a learned
stochastic envelope, its entropy comparison, and a robustness proof for the
known-law classifier bank. In particular, running time itself is not assumed
monotone when gaps increase.

## Theorem and scope

Fix known $0<\rho\le1/4$ and $0<\delta\le1/4$. There is one observable online
procedure, independent of the unknown probability law $\mu$ on $(0,1/2]$,
with nested intervals $I(B)\subseteq[0,\rho]$ and at most $B$ physical flips
at every integer budget. For every such $\mu$, there is a deterministic
finite onset $H(\mu,\rho,\delta)$ such that, under every measurable sign law
with total positive fraction $\theta\le\rho$, with probability at least
$1-\delta$,
$$
 \theta\in I(B)\quad\hbox{for every integer }B\ge0,
 \qquad
 \operatorname{halfwidth}I(B)
 \le C K_{\mu,\rho}\!\left(\frac{B}{\Lambda(B,\delta)}\right)
 \quad\hbox{for every integer }B\ge H,
$$
where $C<\infty$ is universal and
$$
 \Lambda(B,\delta)=\log(1/\delta)+
 2\log\left(2+\frac{\log(1+B)}{\log2}\right).
$$
Coins are independent, with conditionally iid persistent flips. Signs may
depend arbitrarily on gaps. The procedure receives no candidate family,
moments, tail regularity, or integration oracle for $\mu$. The onset need
not be known to it and is not uniform over laws. The same simultaneous event
protects observation-dependent stopping budgets.

One conservative choice is $C=2^{32}C_*$, where $C_*$ is the universal
known-law interval coefficient established below. No sharp constant or
practical sample-complexity claim is made.

## 1. Finite envelopes and the zero atom

For the comparison argument, extend $K$ to probability laws on $[0,1/2]$:
the tail kernel at zero is one, and a selected measure with positive mass
at zero has infinite inverse-gap entropy. Otherwise retain exactly the
original dyadic entropy and infimum over all fractional submeasures. This
agrees with the original $K$ for positive-gap laws. A zero atom is unresolved
mass, not an observed label or a positive magnitude used in a denominator.

Write $\alpha\preceq\beta$ when their gaps admit a coupling
$D_\alpha\le D_\beta$ almost surely, equivalently
$F_\alpha(x)\ge F_\beta(x)$ for all $x$. The learned law will be a finite
$\bar\mu\preceq\mu$, with an explicit zero atom.

We use three entropy facts. Their proofs apply to finite submeasures, with
extended values. If the original entropy is infinite the asserted upper
bounds are automatic. Otherwise its inverse-square cost $A$ is finite.
For a countable cost vector $a$, write
$G(a)=\sum_j a_j[1+\log(A/a_j)]$, omitting zero terms. This equals the
increasing finite-prefix definition of $\Gamma$: the prefix totals increase
to $A$, and each fixed summand increases to the displayed summand. The
usual countable cross-entropy bound follows by the log-sum inequality on
finite partitions, followed by monotone limits. Merging cells decreases
$G$. For a probability vector $p$ positive on the nonzero costs,
$$
 G(b)\le\sum_i b_i[1+\log(1/p_i)].                      \tag{A1}
$$

**Increasing gaps.** If $\alpha\preceq\beta$, then
$$
 K_{\beta,\rho}(N)\le\sqrt3\,K_{\alpha,\rho}(N).        \tag{A2}
$$
Transport an arbitrary finite-entropy selection through the coupling.
Old band $j$ can only move to band $i\le j$. Put $k=j-i$, and let $f_{jk}$
be its old inverse-square cost on that cell, so $\sum_k f_{jk}=a_j$.
Its new cost $b_{jk}$ satisfies
$$
 b_{jk}\le r_k f_{jk},\qquad r_k=\min(1,4^{1-k}),
 \quad r_k\le1,\quad r_k(k+1)\le2.
$$
Apply (A1) with $p_{jk}=(a_j/A)2^{-(k+1)}$, allowing empty cells. After
merging cells with the same destination band,
$$
 \Gamma_{\rm new}\le
 \sum_{j,k}b_{jk}[1+\log(A/a_j)+(k+1)\log2]
 \le\Gamma_{\rm old}+2\log2\,A\le3\Gamma_{\rm old}.
$$
The ordinary tail kernel decreases when a gap increases. Transport preserves
the selection's total mass and domination by the ambient law. Taking the
infimum, then the cap at $\rho$, proves (A2). A finite-entropy selection has
no zero atom, and its transported mass stays positive. This proves the same
statement when either ambient law has an unresolved zero atom.

**A light random contraction.** The factor-32 comparison is [Lean-checked](ARBITRARY_LAW_FORMALIZATION.md#light-random-contraction), including a constructed multiplier with the exact CDF. Let $V$ be independent of $D\sim\mu$ and have
distribution function
$$
 G_V(v)=2e^{-1/(2v^2)}\quad(0<v<1/4),\qquad
 G_V(v)=1\quad(v\ge1/4).
$$
It has no mass at zero and an atom at $1/4$. For $\mu'=\mathcal L(VD/2)$,
$$
 K_{\mu',\rho}(N)\le32K_{\mu,\rho}(N).                 \tag{A3}
$$
Here are explicit bounds for this assertion. Put
$p_k=\Pr(2^{-k-1}<V\le2^{-k})$, $k\ge2$. Then
$p_2=1-2e^{-32}$ and $p_k\le2e^{-4^k/2}$ for $k\ge3$. Old band $j$ and
$V$-band $k$ can reach only bands $j+k$ and $j+k+1$ before the final
division by two. Their combined cost is at most $4^{k+1}a_jp_k$.
Using reference probabilities $(a_j/A)p_k/2$ in (A1) gives
$$
 \Gamma_{\mathcal L(VD)}\le C_V\Gamma_\mu,
 \qquad C_V=\sum_{k\ge2}4^{k+1}p_k[1+\log(1/p_k)+\log2]<256. \tag{A4}
$$
The same calculation applies to any selected submeasure, not just to $\mu$.
For $k=2$ the summand is less than 192, using
$p\log(1/p)\le1/e<1$ and $\log2<1$. For $k\ge3$, the function
$p(1+\log2+\log(1/p))$ is increasing on $(0,1]$. Writing $z=4^k$, each
summand is at most
$$
 8z(1+z/2)e^{-z/2}
 \le3072(z^{-3}+\tfrac12z^{-2}).
$$
The sum of these bounds is
$3072/258048+1536/3840<1$, by $e^x\ge x^4/24$.
Also $\mathbb EV^{-2}\le C_V\le256$ and
$\mathbb EV^{-1}\le16$. Division by two shifts every dyadic band exactly
one position, multiplying cost entropy by four. Thus the transported
selection has entropy at most $1024\Gamma$, and its residual tail cost is
at most 32 times the old tail cost. This proves (A3).

The formal proof uses an alternative fixed reference code, with weights
$7/16$ for each of the two first-band cells and $2^{-(n+4)}$ for each
cell in multiplier band $n=k-2\ge1$. It proves the post-division entropy bound
$1024\Gamma$ and tail coefficient 32 directly. The sharper intermediate
calculation $C_V<256$ in (A4) remains the paper calculation above.

**Dominated mass.** This comparison is [Lean-checked](ARBITRARY_LAW_FORMALIZATION.md#dominated-mass). If $\lambda$ is a probability measure satisfying
$\lambda\le c\eta+e\delta_0$, with $c\ge1$ and $e\ge0$, then
$$
 K_{\lambda,\rho}(N)\le cK_{\eta,\rho}(N)+e.             \tag{A5}
$$
Take a Radon--Nikodym density $0\le w\le1$ of $\lambda$ relative to the
right-hand measure. Transfer a selection $\sigma\le\eta$ to $wc\sigma$.
Monotonicity and homogeneity give entropy at most $c\Gamma_\sigma$;
the residual is at most $c(\eta-\sigma)+e\delta_0$. Since $\sqrt c\le c$,
its objective is at most $c$ times the old objective plus $e$. Infima prove
the result when $K_\eta<\rho$; if $K_\eta=\rho$, the cap proves it directly.

## 2. Learning the envelope under one physical cap

Fix a target depth $J\ge1$, $N=4^J$, $t=2^{-J}$, and pilot failure allowance
$0<\varepsilon<1$. For every $j=1,\ldots,J$, run independent copies of the
[depth-$j$ tail probe](ARBITRARY_LAW_TAIL.md). Give each copy the physical cap
$$
 b_j=\left\lceil\frac{N}{2j(j+1)}\right\rceil+2^{J+j-2},
 \qquad M=\left\lceil\sqrt{64N/\rho}\right\rceil.         \tag{A6}
$$
Stop a copy on its first unresolved coin, on completing $M$ coins, or on
exhausting $b_j$ flips. A partial coin is charged but not counted as completed.
Return $V_j=\min(1,8/n)$ after $n$ completed coins, or one if $n=0$.

The completed-coin cap preserves the original simultaneous coverage proof.
At a deterministic physical cap $b$, it changes the performance statement to
$$
 \Pr\{V_j\le\min(1,128\max(u_j,W_j/b,1/M))\}\ge3/4.    \tag{A7}
$$
Indeed use $A=\max(u_j,W_j/b,1/M)$ in the original proof. Its
$q=\lfloor1/(8A)\rfloor$ satisfies $q\le M/8$, so the extra stopping rule
cannot prevent completing those $q$ coins. All work bounds and the union of
the unresolved and excessive-work events remain valid.
The simultaneous coverage of one probe and (A7) are
[Lean-checked](ARBITRARY_LAW_FORMALIZATION.md#capped-tail-probe). So is the
[median of independent probes](ARBITRARY_LAW_FORMALIZATION.md#median-tail-certificate)
at one depth with the bound of (A7), with failure probability at most
$2e^{-m/8}$. (A8) itself, with its common number of probes and the caps (A6),
is [Lean-checked](ARBITRARY_LAW_FORMALIZATION.md#capped-multi-depth-pilot) for
every $m\ge8\log(2J/\varepsilon)$, as are (A9), (A10) and the domination
below. The checked pilot buys each probe's budget in full.

Use a common odd $m\ge8\log(2J/\varepsilon)$ and take a median $U_j$ at each
depth. A union bound gives, with probability at least $1-\varepsilon$,
$$
 F_\mu(t_j)\le U_j\le
 128\{u_j+W_j/b_j+1/M\}\quad(1\le j\le J),
 \qquad t_j=2^{-j}.                                    \tag{A8}
$$
The median also lies in $[0,1]$. Set $c_j=\min_{i\le j}U_i$ and construct
$$
 \bar\mu=c_J\delta_0+
       \sum_{j=1}^{J-1}(c_j-c_{j+1})\delta_{t_{j+1}}.    \tag{A9}
$$
Depth one never resolves a coin, so $c_1=1$ on every path. This is always a
probability law. On (A8), $F_\mu(t_j)\le c_j$; on each interval
$[t_{j+1},t_j)$, its distribution function is $c_j\ge F_\mu(t_j)$.
Below $t_J$ it is $c_J\ge F_\mu(t_J)$. Thus $\bar\mu\preceq\mu$, including
all grid boundaries and atoms.

All acquisitions are observable. In particular, the zero atom is computed
from completed probes, rather than assigned from a latent small-gap count.
The pathwise cap is $P_J=m\sum_j b_j\le mN$. To verify it, sum the reciprocal
terms in (A6) and use $\lceil x\rceil\le x+1$:
$$
 \sum_j b_j\le N+J-2^{J-1}\le N,
 \qquad \sum_j b_j\ge N/2.                             \tag{A10}
$$
For the lower bound the reciprocal sum contributes at least $N/4$, and
the geometric sum contributes at least $N/4$. The cap $M$ makes easy-law
pilots stop without spending all their authorized flips.

## 3. The learned law retains the oracle rate

For every fixed $\mu,\rho$, there is a finite $J_0(\mu,\rho)$ such that on
the same event (A8), for every $J\ge J_0$,
$$
 K_{\bar\mu,\rho}(N)\le2^{24}K_{\mu,\rho}(N).           \tag{A11}
$$
Let $\nu$ be the lowest-gap quantile submeasure of $\mu$ of mass $\rho$,
splitting a boundary atom, and let $\sigma=\mu-\nu$. Choose $a>0$ with
$\sigma$ supported on $[a,1/2]$. The existing quantile-tail floor gives
$\tau_\nu(t)\le K_{\mu,\rho}(N)$.

The tail-probe work bound gives
$$
 W_{j,\nu}\le2048t_j^{-2}\tau_\nu(t_j),
 \qquad W_{j,\sigma}\le1024(j+1)/a^2.
$$
Since $b_j\ge Nt/(4t_j)$ and
$\tau_\nu(t_j)\le(t_j/t)\tau_\nu(t)$,
$$
 W_{j,\nu}/b_j\le8192K_{\mu,\rho}(N),\qquad
 W_{j,\sigma}/b_j\le2048(J+1)^3t^2/a^2.                \tag{A12}
$$
Choose $J_0$ after which
$2048(J+1)^3t/a^2\le\sqrt\rho$. This also ensures
$t\le\sqrt\rho/2$, so the elementary objective floor gives
$K_{\mu,\rho}(N)\ge2\sqrt\rho\,t$. The core term in (A12) is at most
$K/2$, and $1/M\le\sqrt\rho\,t/8\le K/16$.
The split, (A12), this onset and its existence, the floor
$K\ge2\sqrt\rho\,t$ and $1/M\le K/16$ are
[Lean-checked](ARBITRARY_LAW_FORMALIZATION.md#learned-law-against-the-oracle-work-estimates-and-onset),
with $W_j/b_j\le8193K$ in place of $8192K+K/2$.

The Hoeffding form (2a) of the terminal unresolved bound in the
[tail proof](ARBITRARY_LAW_TAIL.md), applied at depth $j$, bounds the
unresolved probability of a coin with gap $d$ by $G_V(t_j/d)$: it is
$2e^{-d^2/(2t_j^2)}$ when $d>4t_j$ and one otherwise. Integrating over the
gap gives $u_j\le\Pr(VD\le t_j)$. For $x\in[t_{j+1},t_j)$ this is at most
$F_{\mu'}(x)$, where $\mu'=\mathcal L(VD/2)$ as in (A3). Consequently
$$
 F_{\bar\mu}(x)\le\min\{1,128F_{\mu'}(x)+e\},
 \qquad e=128\max_j W_j/b_j+128/M+c_J.                  \tag{A13}
$$
For $x<t_J$ the $c_J$ term proves this directly; for $x\ge t_1$ both laws
already have full mass. This covers zero and every grid endpoint.

The first two terms of $e$ are at most
$[128(8192+1/2)+8]K<2^{21}K$. Also $b_J\ge N/4$, and the earlier tail proof
gave $u_J+W_J/N\le(2052+1/2)K$ at this onset. Thus
$$
 c_J\le512(u_J+W_J/N)+128/M<2^{21}K,
 \qquad e<2^{22}K.                                    \tag{A14}
$$
Take the lowest unit mass of the finite measure $128\mu'+e\delta_0$,
splitting its quantile atom; call it $\lambda$. Its distribution function
is $\min(1,128F_{\mu'}+e)$, so (A13) says $\lambda\preceq\bar\mu$.
Using (A2), (A5), (A3) and (A14),
$$
 K_{\bar\mu}\le\sqrt3K_\lambda
 \le2(128K_{\mu'}+e)
 \le(8192+2^{23})K_\mu<2^{24}K_\mu.
$$
This comparison holds for the original infimum over all fractional
selections. It neither restricts the true law to finite support nor replaces
$K$ by an ordinary-rate surrogate. The auxiliary $V$, $\mu'$ and $\lambda$
are proof witnesses; the learner never samples or computes them.

(A13), (A14), the witness $\lambda$ and (A11) are
[Lean-checked](ARBITRARY_LAW_FORMALIZATION.md#learned-law-against-the-oracle-the-comparison).
(A13) is checked with one bound on $W_j/b_j$ for all depths in place of the
maximum. (A11) is checked for certificates that satisfy the upper half of
(A8), with a finite onset that depends on $\mu$ and $\rho$ only, and on the
pilot event for the learned law of the paid learning stage, on the coin array
of the original simulation law.

## 4. Robust use of the known-law estimator

Suppose a finite known reference law $\alpha$ on $[0,1/2]$ satisfies
$\alpha\preceq\mu$. Use the existing reference bank, ordinary race, finite
multilevel allocation and physical-cap median designed from $\alpha$.
Their error and work certificates remain valid for the actual law $\mu$,
with the same global rarity bound. Here is the transfer argument.
The finite reference null mixture is evaluated exactly, as in the
`GapEnvelope` implementation.

Couple $D_0\sim\alpha$ and $D_1\sim\mu$ with $D_0\le D_1$. Choose the sign
according to the true sign law at $D_1$; its conditional law at $D_0$ defines
an admissible reference sign allocation with the same positive fraction.
With common uniform flip tapes, actual flips are coordinatewise larger than
reference flips for a positive sign, and smaller for a negative sign.

For a fixed prefix length, every positive reference likelihood is
nondecreasing in the number of heads, and every all-negative mixture
likelihood is nonincreasing. The positive-bank crossing is therefore an
upward event; each negative-reference crossing is a downward event. The
ordinary positive boundary is upward and its negative boundary downward.
The complete raced classifier's positive output is upward: increasing bits
cannot introduce an earlier negative crossing and cannot delay a positive
crossing. Terminal majority with a negative tie has the same property.
Thus its error indicator under the actual law is bounded pathwise by that
under the coupled reference law. The usual joint false-positive and total
error bounds transfer, even when signs depend on the magnitude.

**Work requires a different argument.** Increasing a gap can eliminate a
wrong early exit, so the actual stopping time need not decrease. Instead
let $T_{\rm bank}^{s}$ be the hitting time of a correct-sign bank crossing,
ignoring wrong crossings. Let $T_{\rm ord}^{s}$ be the first correct ordinary
boundary crossing, capped at its terminal length $M$, again ignoring wrong
early crossings. Both times decrease under the sign-directed coupling.
Actual physical race work is bounded by
$$
 2\min(T_{{\rm bank},1}^{s},T_{{\rm ord},1}^{s})
 \le2\min(T_{{\rm bank},0}^{s},T_{{\rm ord},0}^{s}).     \tag{A15}
$$
On the selected core, Appendix D's negative- and positive-bank work proofs
already bound these correct crossing times: they use the matching negative
reference and the positive-mixture crossing separately. On the ordinary
tail, the bound
$\min\{M,17d^{-2}[1+\log_+(Md^2)]\}$ still bounds $\mathbb E_d T_{\rm ord}^{s}$.
Indeed, the proof in Appendix F only uses that survival past a check with
$d>2t_{n,M}$ forces a deviation of at least $d/2$; failing to cross the
correct boundary has exactly that implication. The dyadic survival sum and
constant 17 are unchanged. On unresolved mass, use the deterministic cap.
Integrating (A15) therefore recovers the original level-work certificate.
The global rarity surcharge uses the induced reference sign allocation,
whose total positive mass is still at most $\rho$.

Assign a reference zero atom entirely to the unresolved part. It contributes
at most its mass to error and its mass times $M$ to work. All selected-core
and ordinary-tail formulas are evaluated only at positive gaps. The null
prefix probability includes the zero atom's fair-coin likelihood exactly.
Large unresolved mass uses the existing constant-estimator fallback.

The binary correction variances, finite multilevel telescoping, clipping and
expected-work allocation now follow unchanged. Successive corrections use
unused flips of the same persistent coin; conditional on its parameters,
these suffixes remain fresh iid tapes. Fresh production coins and private
randomness remain independent of the pilot. Finally, the capped-median
argument supplies a physical cap on all paths.

For completeness, the quantile design used by the executable planner also
has a universal comparison in the presence of a zero atom. Write
$\alpha=z\delta_0+(1-z)\eta$. Its quantile value $Q_\alpha$ satisfies
$$
 Q_\alpha\le4K_\alpha.                                \tag{A16}
$$
If $z\ge\rho/2$, then $Q_\alpha\le\rho\le2K_\alpha$. If $z<\rho/2$, put
$r=(\rho-z)/(1-z)\le\rho$. The positive part of the quantile core removes
exactly mass $r$ under $\eta$, and
$\rho/[(1-z)r]\le2$. Comparing its two terms, including both cap cases,
$$
 Q_\alpha\le z+\sqrt2(1-z)Q_{\eta,r},\qquad
 K_\alpha\ge z,\qquad K_\alpha\ge(1-z)K_{\eta,r}.
$$
The positive-gap $8/5$ comparison proves (A16). If $z\ge\rho$, the cap gives
$K_\alpha=\rho$ directly. The elementary objective floor also extends:
finite-entropy selections have no zero mass, and zero has tail cost one.
(A16) is [Lean-checked](ARBITRARY_LAW_FORMALIZATION.md#quantile-design-with-a-zero-atom)
for every probability law on $[0,1/2]$, together with the converse
$K_\alpha\le Q_\alpha$.

Thus the [executable known-law rate argument](KNOWN_LAW_ESTIMATOR.md#comparison-with-the-paper-rate)
applies with 4 in place of $8/5$. If $C_{\rm sum}$ is the finite universal
multilevel coefficient proved in Appendix D, its RMS certificate is at most
$C_0K_\alpha(b)$, where
$$
 C_0=1+4\max\{4096,8\sqrt2C_{\rm sum}\}.
$$
Using a relative upper square-root enclosure, the returned median radius is
at most $C_*K_\alpha(b)$ with $C_*=6C_0$. Here $b$ is its base expected
budget. This is a deterministic bound on the reported radius, and a joint
coverage guarantee under the actual law, conditional on a valid reference
envelope. Fixed absolute rounding would not suffice for this asymptotic
claim; the implementation now retains relative precision for tiny radii.

## 5. Online composition and the effective budget

Use the existing confidence ladder with stage caps $c_s=4\,2^s$ and
$\delta_s=\delta/[(s+1)(s+2)]$, $s\ge0$. At a stage, take the largest $J\ge1$
whose exact pilot cap $P_J$ is at most $c_s/2$, using pilot allowance
$\varepsilon=\delta_s/2$ and
$$
 m_J=8\left\lceil\log_2(4J/\delta_s)\right\rceil+1.
$$
If none fits, return $[0,\rho]$ without acquisition. Otherwise learn
$\bar\mu$ and run its known-law capped-median interval on fresh coin labels
with remaining cap $c_s-P_J$ and failure allowance $\delta_s/2$.

Conditioning on any successful finite pilot history leaves the continuation
stream fresh. Section 4 is uniform over every resulting envelope and true
sign law. Pilot failure and conditional continuation failure sum to at most
$\delta_s$. Intersect stage intervals. A union bound over stages proves
all-budget coverage, including stages before the rate onset. All work caps
hold even when learning fails.

We give the budget comparison explicitly. By (A10),
$m_JN/2\le P_J\le m_JN$. Also $m_{J+1}\le2m_J$ and
$P_{J+1}\le8m_JN$. Maximality therefore gives
$$
 N>c_s/(16m_J),\qquad m_JN\le c_s.                    \tag{A17}
$$
The continuation's median block count is no greater than $m_J$:
$(3/4)^{m_J}\le e^{-m_J/4}\le(\delta_s/2)^2$, and the count is the least
odd integer satisfying that inequality. Its base expected budget is at
least $c_s/(16m_J)\ge N/16$. Budget monotonicity and square-root scaling of
$K$ give continuation radius at most $4C_*K_{\bar\mu,\rho}(N)$.

At any budget $B$ with completed stage $s$, the ladder has
$c_s\le B<4c_s$. Also $J\le s+2$. The definition of $m_J$,
$\log2\ge1/2$, and $\delta\le1/4$ give
$m_J\le64\Lambda(B,\delta)$. Thus (A17) implies
$$
 N>B/[4096\Lambda(B,\delta)].                          \tag{A18}
$$
As $s$ increases, the chosen $J$ tends to infinity, because $c_s$ grows
exponentially whereas each fixed-depth pilot cost grows only logarithmically
in $s$. Hence a deterministic finite $H(\mu,\rho,\delta)$ ensures that the
last completed stage has $J\ge J_0$ for every $B\ge H$.

On the single event that all stage learning and coverage bounds hold,
intersection can only reduce halfwidth. Combining (A11), (A18) and
square-root budget scaling gives
$$
 \operatorname{halfwidth}I(B)
 \le4C_*2^{24}\cdot64\,
 K_{\mu,\rho}(B/\Lambda(B,\delta))
 =2^{32}C_*K_{\mu,\rho}(B/\Lambda(B,\delta)).
$$
This completes the theorem. The procedure and confidence schedule are fixed
before the law, while the theorem's finite onset is allowed to depend on it.

## Executable interfaces and remaining formal work

The [finite envelope learner](../toolkit/threshold_toolkit/gap_envelope.py)
uses exact rational masses, integer thresholds, separate probe namespaces,
and the physical and completed-coin caps in (A6). `GapEnvelope` evaluates
its finite null mixture exactly, including the fair-coin zero atom. Its
positive conditional law supplies the remaining design integrals with the
appropriate mass scaling and split-boundary correction.

The [arbitrary-law ladder](../toolkit/threshold_toolkit/arbitrary_law_confidence.py)
combines the learner with the existing capped-median continuation:

```python
from threshold_toolkit.arbitrary_law_confidence import arbitrary_law_confidence

# coin_factory(rng) returns one fresh persistent coin's flip callback.
sequence = arbitrary_law_confidence(coin_factory, rho="1/4", delta="1/20", seed=17)
state = sequence.advance_to(100000)
print(state.interval, state.flips)
```

`plan_gap_envelope` and `run_gap_envelope` expose the learner separately.
Repeated cumulative budgets perform no work; callbacks and persistent
coin sampling obey the same contracts as the existing toolkit. Arithmetic
and input-size limits of Python interfaces do not form part of the
unbounded mathematical construction. The test suite checks finite exact
probabilities and arithmetic, controller accounting, namespaces, partial
coins, zero atoms, split boundaries, tiny-radius rounding and failure paths.
It does not prove the general theorem.

Lean now constructs increasing couplings from CDF domination and checks
entropy and fractional selection transport, including the zero-atom
extension and its agreement with positive-gap K. It also checks the light
random contraction with coefficient 32 and the dominated-mass inequality,
the capped pilot with the law it learns, and the learned-envelope comparison
(A11) on the pilot event. The quantile comparison (A16) is checked; the
planner's certificates and the coefficients $C_0$ and $C_*$ are not.
Formalization remains for them, the robustness
transfer and full adaptive controller. Existing Lean
results establish the positive-gap quantile-tail floor, objective floor,
budget scaling and known-law foundations used here; they do not automatically
formalize this new composition. Python and its PRNG remain unverified.
