# Anytime confidence: focused round-three extraction

This is a paper-only application, not a matching anytime minimax theorem.
The fixed-confidence transfer and the definition of the rate functional K are
in [NOTE.md](NOTE.md). The hard-budget RMS theorem is a separate PR. Historical
equation labels are retained where useful; this extraction supplies its own
schedule, scaling and width definitions. No previous validation record is
silently upgraded.

# Anytime confidence and optional stopping

## Exact error spending

Fix $0<\delta\le1/4$ and deterministic stage budgets $n_j=4\cdot2^j$. Give stage $j$ the failure allowance

$$\delta_j=\frac{\delta}{(j+1)(j+2)}. \tag{20}$$

Suppose it produces a random confidence set $I_j$ with $P_\theta(\theta\notin I_j)\le\delta_j$ uniformly in the parameter, using at most $n_j$ observations. Stage intervals need not be independent for the following coverage argument.

The cumulative reservation checkpoints are
$S_m=\sum_{j=0}^m n_j=4(2^{m+1}-1)$. At checkpoint $S_m$ report

$$J_m=[0,M]\cap\bigcap_{j=0}^m I_j. \tag{21}$$

Between checkpoints retain the last reported set, and before the first checkpoint use $[0,M]$. Empty intersections are retained as empty; they are not silently replaced by a full interval.

**Theorem 3 (simultaneous coverage).** The resulting sequence satisfies

$$\inf_\theta P_\theta\{\theta\in J(B)\text{ for every authorized }B\ge0\}\ge1-\delta. \tag{22}$$

It uses at most the current authorized budget in physical observations. For any stopping rule T based on the reported history,

$$P_\theta\{T<\infty,\ \theta\notin J_T\}\le\delta.$$

If T is almost surely finite, this is the usual coverage guarantee at stopping.
Without almost-sure termination, it is an unconditional bound on an erroneous
returned set, **not** a conditional coverage guarantee given termination.

**Proof.** The exact telescoping identity is

$$\sum_{j=0}^m\delta_j=\delta\frac{m+1}{m+2},\qquad
\sum_{j=m+1}^{\infty}\delta_j=\frac{\delta}{m+2}. \tag{23}$$

By the countable union bound, all intervals cover simultaneously with probability at least $1-\delta$. On this event every intersection contains $\theta$. The pathwise cap follows from the reservation identity $\sum_{j=0}^m n_j=S_m$; a stage is started only when its entire cap fits in the authorized allowance. Optional stopping follows by restricting the same simultaneous event, not by applying a fixed-time theorem at a random time. $\square$

A timed-out interval generator may safely contribute $[0,M]$, since this can only improve coverage relative to that generator's eventual raw interval. However it then need not satisfy a desired width bound. The width result below uses a base procedure that really has the required hard cap.

## Entropy-tail width bound

Assume the round-two paper theorem: the known-law rare-event hard-budget confidence radius has order $K(b/\log(1/\varepsilon))$ with upper coefficient 840000. Use coefficient $C_*=850000$ to allow strict slack in choosing procedures when an infimum is not attained. At stage $j$, choose the zero-work midpoint rule when appropriate, otherwise an eligible hard-budget procedure, so that

$$\frac12\operatorname{diam}(I_j\cap[0,\rho])
\le\min\left\{\rho/2,\ C_*K(n_j/\ell_j)\right\},\qquad
\ell_j=\log(1/\delta_j). \tag{24}$$

The radius and the procedure may use known $\mu$. This is not an honest data-computable interval for an unknown magnitude law.

For $B\ge4$, let $m$ be the last completed checkpoint. Then

$$n_m>B/4,\qquad m+2\le2+\log_2(1+B),$$

so $\ell_m\le\Lambda(B,\delta)$ for

$$\Lambda(B,\delta)=\log(1/\delta)+2\log\!\left(2+\log_2(1+B)\right).$$

The definition of K implies monotonicity in B and
$K(B/c)\le\sqrt c\,K(B)$ for $c\ge1$: apply the inequality to each
fixed selection before taking the infimum and rarity cap. Consequently

$$K(n_m/\ell_m)\le K(B/(4\Lambda))\le2K(B/\Lambda). \tag{25}$$

The nonempty intersection cannot have larger diameter than the last interval. Hence the half-width is bounded by

$$\min\!\left\{\rho/2,\ 1700000\,K\!\left(B/\Lambda(B,\delta)\right)\right\}.$$

On the simultaneous-coverage event the intersections are nonempty. For
$1\le B<4$, the full interval and the saturated rate suffice. Only finitely many stages are needed at a finite budget; the coverage event concerns countably many possible stages.

For the critical law, the resulting half-width has order at most

$$\min\left\{\rho,\sqrt{\frac{\rho L_\rho H_\rho}{B}
\left[\log(1/\delta)+\log\log(e+B)\right]}\right\}. \tag{26}$$

This is an upper bound. No matching time-uniform minimax lower bound is proved here. Error spending over a geometric schedule is standard confidence-sequence methodology; Howard et al. [4] provide much more general and sharper frameworks. The contribution here is the explicit compatible construction and bookkeeping for the hidden-gap rate and strict observation budgets, not invention of confidence sequences or stitching.

## Stopping at a requested width

A valid rule is to stop at the first nonempty intersection of width at most $2\varepsilon$ and return its midpoint. An empty intersection is an explicit certification failure, not an estimate. On the simultaneous-coverage event the returned midpoint is within $\varepsilon$ of $\theta$.

For the theoretical known-law intervals, $K(B/\Lambda)\to0$: choose $\sigma=0$ in the definition of K and apply dominated convergence to the ordinary integral. Thus the prescribed widths tend to zero. A finite deterministic checkpoint eventually forces either the width criterion or an empty-set failure; the latter is contained in the coverage-failure event. This is not a claim that arbitrary user-provided interval factories shrink.

## Authorized allowance versus realized spend

The software uses a reservation clock: a stage is launched only when its entire cap fits in the authorized budget. Actual observations may be fewer. The separate RMS theorem is indexed by deterministic authorization, not the random actual observation count at completion. Confidence coverage remains valid when the next authorized checkpoint is chosen from the observed history, because (22) is simultaneous.

A literal physical-time version is possible in the statistical model: after an early completion, spend the unused stage slots on ignored observations and release the new output only at the deterministic checkpoint. During an incomplete stage retain the old output. This consumes no more than the caps already charged in the proof and aligns checkpoints with physical observation times. The supplied driver deliberately avoids those statistically wasted observations; it reports both counters explicitly.

## Repeatedly inspecting fixed-time intervals is not valid

Let $X_t$ be iid Bernoulli$(1/4)$ and $H_n=\sum_{t\le n}X_t$. For every fixed $n$, Chebyshev's inequality gives

$$P\{(4H_n-n)^2>12n\}\le1/4. \tag{28}$$

Equivalently, the interval centered at $H_n/n$ with radius $\sqrt{3/(4n)}$ has fixed-time coverage at least $3/4$, uniformly for every $\theta\in[0,1/4]$.

Now stop at the first time this interval excludes the fixed reference value $1/4$, or at time 512. At true parameter $1/4$, exact integer path counting gives

$$P\{\exists n\le512:(4H_n-n)^2>12n\}=0.42809100970105135\ldots>1/4. \tag{29}$$

The stop rule is observable; the value $1/4$ is specified in advance. No unknown parameter is used by the rule. This is a legal hidden-coin example with $\mu=\delta_{1/2}$, not an unrelated Gaussian approximation.

The verifier keeps integer counts of paths that have not crossed. A tail transition multiplies its count by three and a head transition by one; the common denominator at time $n$ is $4^n$. It removes crossings and sums surviving weights. The saved JSON contains the exact rational probability, not just the displayed decimal.


## Implementation

The maintained module is `toolkit/threshold_toolkit/confidence_ladders.py`,
which imports observation accounting from `budget_ladders.py`. A timeout preserves
the current set but does not give a shrinking-width guarantee. The supplied
Bernoulli interval is only for iid fresh Bernoulli samples, not pooled repeated
flips of heterogeneous hidden coins. The driver does not validate statistical
coverage premises supplied by callbacks.

Reference [4] in the extraction is Howard et al., Time-uniform, nonparametric,
nonasymptotic confidence sequences, arXiv:1810.08240. Error spending is standard;
no novelty is claimed for confidence sequences or the union-bound construction.
