# Alternate attack on the critical exponent two

Date: 2026-10-27. Author: the formal-foundations agent, now contributing an alternate mathematical attack. This is not an independent review of any argument to which I contribute. No new Lean target or accepted minimax theorem is claimed here. Existing Route A locks, Tier 5 work, and `research/2026-10-27-minimax-audit/` are untouched.

## Starting point and overlap

The target is the hidden-magnitude iid experiment with known a,ρ, exact law F(d)=(d/a)² on (0,a], and the global constraint ∫q dμ≤ρ. The desired error is a universal constant times

    min{ρ, sqrt(ρ(1+log(1/ρ)))/(a sqrt(B))}.

I read the concurrently existing `research/2026-10-27-minimax-audit/theorem/critical.tex`. It already proves on paper a capped-classifier upper bound with an extra factor sqrt(1+log(1+log(1/ρ))), including a moment bound 165ρ/56, explicit expected work, and the cutoff integrals below. Those calculations are existing overlap, not a new result of this alternate pass. The problem is removing the remaining log(number of gap scales), or proving that some such loss is unavoidable for all population algorithms.

For orientation, with U=max(D,δ), l=log(a/δ), direct integration gives

    E U⁻² = a⁻²(1+2l),
    E[U⁻² log(a/U)] = a⁻²(l²+l),

and the sharp global-rarity integral is

    sup_(0≤q≤1, Eq≤ρ) E[qU⁻²]
      = ρ/δ²,                              if ρ≤δ²/a²,
      = a⁻²[1+log(ρa²/δ²)],                otherwise.

Thus δ=a sqrt(ρε) makes the positive weighted integral a⁻²(1+log(1/ε)). Paying log(1/ρ) only on positive coins is affordable at the conjectured critical rate. The unresolved issue is the cost of negative screening across many unknown gap scales.

## A limitation of the dictionary proof certificate

Consider K dyadic bins I_k=(a2^(-k-1),a2^(-k)], k=0,...,K−1. Each has the same inverse-square integral:

    ∫_(I_k) d⁻² μ(dd) = 2 log(2)/a².

Suppose a proof controls negative expected work in bin k by an expression proportional to d⁻²[log(1/ε)+log(1/π_k)], where π_k>0 and ∑π_k≤1 arise from a union-bound allocation over likelihood tests. Integrating this certificate produces a term proportional to

    a⁻² ∑_(k<K) log(1/π_k).

The arithmetic-geometric mean inequality gives ∏π_k≤K^(−K), hence

    ∑_(k<K) log(1/π_k) ≥ K log K.

Consequently, merely reweighting such a finite dictionary cannot make that particular upper-bound certificate O(K/a²). Uniform weights achieve the best K log K scale; geometric weights have a K²-scale certificate. **This is not a lower bound on actual classifier work, and certainly not on all population estimators.** It only identifies why this proof technique cannot remove its own final iterated logarithm by numerical tuning of weights.

One sufficient missing lemma would be observable classifiers Z_j with

    P(Z_j≠S) ≤ Cρ16^(-j-1),
    E T_j ≤ C a⁻²[L(j+1)+(j+1)²],       L=1+log(1/ρ),

uniformly over the global rarity class. A standard single-term telescope with p_j=2^(-j-1) would then have E Y²≤(2+3C/7)ρ, and expected work ≤8CL/a² for nested same-tape stopping (≤16CL/a² if two costs must be added). Here E(J+1)=2 and E(J+1)²=6. Poisson replication would give the desired rate. This is a sufficient unproved interface, not a new construction, and it overlaps the architecture of the existing capped proof. The exact missing improvement is eliminating its log K negative-screening cost without assuming observed magnitudes or pointwise q≤ρ.

## Why a direct reduction from population estimation to SIGN is incomplete

The source-review agent identified a finite-gap entropy lower bound for single-arm sign testing. This pass did not independently re-audit that primary theorem. Even accepting it, two natural reductions fail to yield the desired population lower bound.

### Encoding an arm in the sign selector

Let the source arm have unknown mean 1/2±d. For each new simulated population coin, use one source flip X and an independent selector with probability ρ, making its sign positive exactly when the selector succeeds and X=1. Draw its D independently from the required μ and simulate its subsequent tape from the retained sign and D. This preserves exact μ and independent fresh-coin laws, and gives constant sign functions within the required rarity class:

    q_± = ρ(1/2±d) ∈ [0,ρ].

The two target fractions differ by 2ρd. A fixed-budget population mean estimator therefore yields only an ordinary estimate of a scalar whose unknown separation is proportional to d. To turn this into a uniformly correct sign procedure one must still select a stopping budget without knowing d. That adaptation step can itself incur the finite-gap entropy loss. It is invalid to choose the population budget as if the source gap were observed. Thus this encoding does not contradict the sign lower bound and does not refute the critical minimax conjecture.

### Planting only a d²-mass component

A more attractive reduction would plant the source arm into a component of mass approximately (d/a)², preserve the rest of the fixed μ law, and relate both the resulting θ-separation and source-observation cost sharply to the proposed population budget. Changing only that component can change θ by at most its mass, so a gap-independent positive separation cannot be assumed. The simulator must not know d. Sampling such a component with exactly the required unknown mass is a nontrivial Bernoulli-factory task; assigning d to a closure silently grants the missing oracle.

The following elementary fact rules out one particularly simple universal version of this simulator.

**Finite-trigger lemma (paper proof).** Fix one randomized sequential procedure observing Bernoulli(p) flips. Its seed is independent of p, and triggering is determined after finitely many observed flips whenever it occurs. Let A be the trigger event. If P_(p*) A>0 for some p* in (0,1), then for every p₀ in (0,1),

    liminf_(p→p₀) P_p A > 0.

The procedure need not terminate under p₀.

**Proof.** Since a trigger occurs at a finite observation count, some n has P_(p*)(A and trigger time≤n)>0. Pad the tape to n flips. After integrating the independent seed, this finite-prefix probability has the form

    f_n(p)=∑_(z∈{0,1}^n) c_z p^(#ones(z))(1−p)^(n−#ones(z)),

where every c_z is nonnegative. Positivity at p* implies at least one c_z>0. Every Bernoulli word has positive probability at the interior point p₀, so f_n(p₀)>0. Continuity gives liminf P_p A≥lim f_n(p)=f_n(p₀)>0. This proof does not require a bounded stopping time or optional stopping. ∎

For a fixed simulator valid at arbitrarily small unknown d, a trigger probability c d² would tend to zero as p=1/2±d approaches the interior point 1/2, contradicting the lemma. This is a familiar kind of finite-prefix positivity obstruction, not a claimed novel minimax result.

**Essential limitation:** the lemma does not prohibit a different simulator for each known finite gap set bounded away from zero. That is exactly the setting in which a finite-gap entropy reduction might still work. One would have to construct that simulator and bound its own arm-observation cost tightly enough that it does not already pay the proposed extra logarithm. No such cost-preserving construction was obtained in this pass.

## State of this attempt

No all-algorithm counterexample and no removal of the remaining iterated logarithm was obtained here. A lower bound restricted to the current classifier, its union-bound certificate, or a single-coin estimator family would not settle the population question. Conversely, invoking a single-arm sign lower bound without the unknown-gap, exact-μ, iid-preserving simulation and its work analysis would overstate the evidence.

The next precise question for this alternate route is: can a population estimator with the conjectured fixed-budget guarantee be converted into a uniformly correct sign procedure over a finite gap set by a parameter-independent simulator that preserves the same magnitude law and charges every source observation, while spending less than the finite-gap entropy lower bound? The simple sign-selector construction leaves unknown-gap stopping unresolved; the natural rare-planting construction leaves its Bernoulli-factory cost unresolved. Until one of those gaps is closed, this route is parked as an incomplete reduction rather than an impossibility theorem.

The separate source-review agent read this note, checked the finite-trigger proof and telescope constants, and found the certificate-versus-algorithm distinction appropriate. It flagged an earlier planting desideratum that incorrectly requested a gap-independent positive θ-separation from a component whose mass vanishes like d²; that phrase was corrected above. This is a limited agent review of the reduction discussion, not an all-algorithm lower-bound review or external specialist review.

## Finite-horizon local-Fisher diagnostic

The parent proposed a radial finite-atom experiment as a quick falsifier for one possible information obstruction. I implemented that specified diagnostic in `fisher.py`; its reproducible output is `fisher.json`. Run from the repository root:

```text
python research/2026-10-27-critical-two/fisher.py
```

The command returned exit 0. There are no Monte Carlo samples or seeds. All calculations use NumPy float64; log-sum-exp stabilizes finite-prefix posterior weights, but there is no interval enclosure or certified numerical optimum.

For K=2,3,4, let a=1/4, d_i=a2^(−i), μ_i proportional to d_i², and q_i=(1/16)4^(i−K), i=0,...,K. Write ρ=∑μ_iq_i. The local path is q_η=(1+η)q. Its two-sided neighborhood lies in the rarity class with bound 2ρ, not in Q_ρ itself for positive η; the recorded ρ is the baseline mean. The diagnostic is not presented as a minimax converse on Q_ρ.

For a particular length-n word with h heads, let f be its baseline probability and g its η-derivative. The next-head probability and derivative are

    p=f_head/f,              dp=(g_head−p g)/f,

giving conditional Fisher information I=(dp)²/[p(1−p)]. The seed and chosen policy are independent of η. For every fixed finite stopping policy, likelihood-score increments have conditional mean zero, so cross terms vanish and the stopped transcript's Fisher information is the expected sum of these conditional I values. This bounded-horizon argument does not assume unproved regularity at unbounded stopping. Finite mixture probabilities are smooth and strictly positive because every component's Bernoulli parameter lies in [1/4,3/4].

For an information/work penalty λ, backwards recursion uses

    V(n,h)=max{0, I(n,h)−λ+p V(n+1,h+1)+(1−p)V(n+1,h)},

with terminal value zero. The extracted deterministic count-state policy continues exactly when the displayed advantage is positive. It is fixed at η=0 and is not allowed to change when η is perturbed. Separate recursions compute its expected work and information; the identity V(0,0)=information−λ work is checked numerically. Forty-four ratio-search iterations are used. At horizon three, all 64 count-state stopping policies are separately enumerated and their best ratio agrees with the recursion. Nine distinct finite-prefix states also pass central-difference checks of the predictive Fisher formula. These are implementation sanity checks, not error-certified bounds.

The main posterior/information tables occupy at most 8,396,800 bytes. The nine prescribed cases yielded:

| K | Maximum flips | (I_η/E T)/(a²ρ/K) |
|---|---:|---:|
| 2 | 256 | 4.73941 |
| 2 | 512 | 4.74332 |
| 2 | 1024 | 4.74337 |
| 3 | 256 | 5.55589 |
| 3 | 512 | 5.64615 |
| 3 | 1024 | 5.66600 |
| 4 | 256 | 5.79075 |
| 4 | 512 | 6.06478 |
| 4 | 1024 | 6.19822 |

Thus these explicitly extracted finite-horizon policies already have information/work ratios of the proposed a²ρ/K scale on the tested radial submodels. This diagnostic gives no support for an additional logarithmic information loss on that direction. It does not establish a uniform-in-K result: K is small, horizons are finite, floating-point optimization is uncertified, and the policy is tuned to the specified radial shape. Estimating one known-direction parameter can exploit informative scales without learning an arbitrary q. Accordingly, this experiment neither proves the target upper bound nor rules out a different least-favorable perturbation or an all-population obstruction.

## First-order projection investigation: an incomplete reduction

The parent proposed a possible first-order/Hájek projection of an interacting population estimator. This subsection records what can be justified and the remaining gaps; no projection reduction is accepted here.

First fix a finite number N of independent potential coin tapes and a deterministic observation horizon H. Under the all-negative law P₀, define

    f_i(X_i)=E₀[F | X_i]−E₀F.

The tape projections are centered and mutually orthogonal, so ∑E₀ f_i²≤Var₀F. If the same F were exactly unbiased for every global-rarity allocation, differentiating the finite-product experiment along q=t r would give

    ∑_i (E_(d,+)f_i−E_(d,−)f_i)=1     for μ-almost every d.

For bounded F this differentiation is a finite polynomial expansion. With the requisite finite integrability under nearby mixture laws it remains justified by domination of the finitely many hybrid terms. It is not an unbounded-stopping differentiation argument.

There is an immediate limitation: **in this threshold model the bounded-horizon exact-unbiased case is impossible.** Each f_i depends on at most H bits of its tape and has finitely many conditional values after the independent seed and other tapes are integrated out. Its fixed-sign expectation is a finite sum of Bernoulli-word probabilities, hence a polynomial in d. The difference between the plus and minus expectations vanishes at d=0. The displayed response identity would make their finite sum equal to one almost everywhere on (0,a] under a strictly positive power-law density. Continuity would make it equal to one throughout that interval, contradicting its value zero at d=0. This auxiliary paper argument concerns a deterministic finite observation bound; it says nothing against the unbounded finite-mean procedures already constructed.

For approximate unbiasedness, a small uniform bias alone does not control the required derivative. As a function-level counterexample, b(t)=δ(1−t/ρ)^N on [0,ρ] has |b(t)|≤δ but b'(0)=−Nδ/ρ. This example is only a warning about the logical inference from a uniform error bound to a derivative bound; no observable-policy realization is claimed for this particular formula. An approximation or horizon-limit argument must prove its own derivative and integrability control.

Even if a suitable algebraic projection is obtained, the observation cost is unresolved. Computing f_i averages over counterfactual seed choices and other-coin histories. Those histories can request genuine-coin prefixes not seen on the original realized path. For example, let a seed trigger with probability ε, and only on that event observe H bits and return their parity. The original expected work is εH. Its exact pathwise first projection is ε times the centered parity, whose value cannot be determined before observing all H bits: every shorter prefix has extensions of both parities with positive probability. A fresh simulation of the original procedure retains the cheap expected work but also retains seed noise; it does not realize the exact projection variance. This example refutes the naive pathwise cost assertion, not every possible product-preserving implementation or the minimax conjecture.

There is a second gap: the orthogonality estimate is under P₀. It does not by itself provide the separate uniform-in-q moment bound required by the single-coin product theorem. At unbounded horizons, full positive and negative tapes can be mutually singular, so an arbitrary P₀-almost-everywhere version of a projection also cannot simply be evaluated under every alternative without a specified extension and proof.

The separately developed additive reduction avoids these obstacles because its components are already actual observable single-coin procedures. For a known seed-preselected count N(U) of finite positive mean m, its size-biased seed law N(U)P(dU)/m and a uniformly selected component implement the new single-coin estimator directly. Conditional baseline centering preserves the population expectation and the shared-negative-mixture calculation controls alternative moments. That argument covers the stated additive class, including shared seeds and preselected finite-mean random counts; it does not construct projections of interacting or nonlinearly aggregated outputs. The exact theorem and assumptions belong in `construction.tex`, not in this exploratory subsection.

**Conclusion:** no observable, uniformly controlled, cost-preserving first-order projection for the full population class was obtained. The finite-horizon polynomial contradiction, missing derivative control for approximate bias, counterfactual-prefix cost, and alternative-law moment control are explicit obstacles to the proposed reduction. The full critical minimax question remains open.
