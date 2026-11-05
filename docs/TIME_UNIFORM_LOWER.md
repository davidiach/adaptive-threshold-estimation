# Gap-law-dependent time-uniform lower bounds

For every known probability law μ on positive gaps, 0<ρ≤1/4 and 0<δ≤1/4,
one online controller and measurable prefix estimates with simultaneous
deterministic error envelope t must satisfy, beyond every prescribed integer
budget M,

    t(n) ≥ 10^(−22) K_(μ,ρ)(n/[log(1/δ)+log log n])

at some integer n≥max(M,3). Here t is nonnegative. Monotonicity of t is not
required. The same conclusion holds for observable intervals when simultaneous
coverage and half-width control hold jointly with probability at least 1−δ
under every rare sign prior.

The final [interval theorem](../lean/ThresholdHC/AnytimeLower/Intervals.lean)
and [online-estimate theorem](../lean/ThresholdHC/AnytimeLower/Full.lean) use
the original hidden-gap experiment, one common adaptive policy, its private
seed, and actual observed prefixes. The result concerns deterministic
envelopes; it does not assert a pointwise lower bound on every random interval
or every budget. The [finite-family theorem](FINITE_FAMILY_ADAPTATION.md) now gives eventual oracle-rate adaptation after a paid identification pilot. Adaptation over arbitrary unknown gap laws remains open.

## First-crossing testing

Let Q have mean θ and let P_k have mean θ+a_k, with a_k>0 and 3a_k≤a_i for
i<k. Let N_k be increasing physical budgets and let the actual observable
prefix KL under P_k relative to Q be at most K_k.

If t(N_k)<a_k/6 at every k, define E_k={estimate at N_k>θ+a_k/2} and let A_k
be its first crossing. On simultaneous accuracy under P_k, the first crossing
is exactly k. Under Q there is no crossing. Thus P_k(A_k)≥1−δ,
the A_k are disjoint, and their total Q mass is at most δ. Binary data
processing and the bound log 2 on binary entropy give

    Q(A_k) ≥ exp(−K_k/(1−δ))/4.

Consequently the testing terms must be summable. Applying the argument to
every tail proves infinitely many violations whenever they are not summable.
There is no independence assumption across prefixes.
[Sequential proof and audit](ANYTIME_SEQUENTIAL.md).

For any positive antitone scale s_k, the explicit schedule

    N_k = floor(((1−δ)/2) log(k+2)/s_k²)

is monotone and tends to infinity. Its KL terms, when K_k=N_k s_k², dominate
exp(−log(k+2)/2), which is not summable. Eventually
log(k+2)/8≤N_k s_k² for δ≤1/2.

## Finite coefficient

Put C=sup_(B>0) sqrt(B) K_(μ,ρ)(B). If the inverse gap is integrable, C is
finite: selection of the empty core bounds K(B) by
B^(−1/2) ∫d^(−1) dμ. Also C>0, since selection saturates at ρ for small budgets.

Choose B with sqrt(B)K(B)>C/2. The attained infinite-cap four-prior dual and
the existing 10^(−17) comparison supply an admissible certificate with positive
mean gap Δ and finite information bound J>0 such that

    (10^(−17) C/2)² J ≤ Δ².

Absorb its variance and work references into the endpoints and use their
central segment. At shifts u_k=(1/8)4^(−k), the mean increments are u_kΔ/3
and their observable prefix KL is at most (64/3)Jn u_k².
Take s_k=sqrt((64/3)J)u_k. First-crossing testing forces
t(N_k)≥u_kΔ/18 infinitely often.

Write λ(n)=log(1/δ)+log log n and h(n)=sqrt(λ(n)/n). The geometric schedule
satisfies λ(N_k)≤3 log(k+2) eventually, hence h(N_k)≤5s_k.
The definition of C gives

    K(N_k/λ(N_k)) ≤ C h(N_k) ≤ 25 C sqrt(J) u_k.

Combining these inequalities proves the claimed 10^(−22) coefficient.
The [finite-coefficient theorem](../lean/ThresholdHC/AnytimeLower/FiniteMatching.lean)
only assumes that C is finite, so it also applies beyond integrable-inverse laws
when that stronger premise is known.

## Infinite inverse moment

Choose 0<τ≤1/4 with 0<μ{d≤τ}≤ρ. Define

    g_h(d) = min(1,h/d) on {d≤τ}, and zero elsewhere,
    T(h) = ∫g_h dμ,   ε_j=τ4^(−j),   W_j=T(ε_j).

The small-gap region exists by dominated convergence. Its inverse gap remains
nonintegrable, since the complementary inverse gap is bounded by 1/τ.
Monotone convergence of g_h/h proves T(h)/h→∞ as h decreases to zero.
Selecting the empty core gives

    K(h^(−2)) ≤ T(h)+h/τ ≤ 2T(h)

for all sufficiently small positive h. Also T(ah)≤aT(h) for a≥1.
These upper comparisons suffice for the infinite-moment proof; no quantile
comparison factor is needed here.

The masses W_j are positive, antitone, tend to zero, and satisfy
W_(j+1)≥W_j/4. Choose j_0=0 and each j_(k+1) as the first later index with
W_(j_(k+1))≤W_(j_k)/4. Before that index, W_j>W_(j_k)/4.

Use q_0=1/4 on {d≤τ}, zero elsewhere, and

    q_k=q_0+(g_(ε_(j_k))−g_(ε_(j_(k+1))))/32.

These are admissible rare sign priors. Their positive mean increments satisfy
a_k≥3W_(j_k)/128 and 3a_k≤a_i for i<k.
Their gap-weighted contrast is at most ε_(j_k)/32.
The finite-transcript posterior argument, integration over the hidden gap array,
and data processing give KL(P_k^n||Q^n)≤n ε_(j_k)² for the actual observable
prefix, including adaptive acquisition, revisits and early stopping.
[Construction and audit](ANYTIME_TAIL.md).

### Dense blocks

If j_k≤(k+2)² eventually, use the testing schedule with s_k=ε_(j_k).
It forces t(N_k)≥W_(j_k)/256 infinitely often. The polynomial index bound
gives λ(N_k)≤3log(k+2), and the floor estimate gives h(N_k)≤5ε_(j_k).
Therefore, eventually,

    K(N_k/λ(N_k)) ≤ 2T(h(N_k)) ≤ 10W_(j_k).

This proves the stronger coefficient 1/2560 in the
[dense-block theorem](../lean/ThresholdHC/AnytimeLower/DenseTail.lean).

### Sparse blocks

Otherwise j_k>k² infinitely often. If eventually every increment were less
than sqrt(j_k), then sqrt(j_(k+1))≤sqrt(j_k)+1/2, contradicting that growth.
Thus j_(k+1)−j_k≥sqrt(j_k) infinitely often.

For a large such block start j=j_k, put

    a=floor(sqrt(j)/2), m=j+a, n=ceil(16^m/τ²).

Then m+1<j_(k+1), n ε_(m+1)²≤1/8, and n→∞ along these blocks.
Elementary geometric bounds give λ(n)≤3(j+1)≤16^a≤n ε_j², so h(n)≤ε_j.
Hence K(n/λ(n))≤2W_j.

Use the single alternative q=q_0+g_(ε_(m+1))/32. Its mean gap is
W_(m+1)/32, while its observable prefix KL is at most 1/8.
If t(n) were smaller than half this gap, simultaneous accuracy would give
a test with power at least 3/4 and size at most 1/4. Binary Pinsker would
force KL≥1/2, a contradiction. Therefore

    t(n) ≥ W_(m+1)/64 > W_j/256 ≥ K(n/λ(n))/512.

This proves the [sparse-block theorem](../lean/ThresholdHC/AnytimeLower/SparseTail.lean).
Both infinite-moment branches are stronger than 10^(−22).

## Intervals and verification

On the joint coverage and width event, the interval midpoint has error at
most t(n) for every n. Its measurability follows from that of the endpoints.
This gives the final real-valued interval theorem without a monotonicity
assumption on the envelope.

Run the audits sequentially:

    python tools/verify_anytime_sequential.py
    python tools/verify_anytime_tail.py
    python tools/verify_anytime_asymptotics.py

The last audit independently restates fourteen exact statements, including
both asymptotic branches, the complete all-law theorem, and the interval
consequence, and checks their transitive axioms.
The [asymptotic native record](../results/anytime-asymptotic-20261105/README.md)
identifies the proof checkpoint, compiler input, empty fresh compiler logs,
and dependency hashes. The earlier
[15-root information audit](../results/anytime-lower-20261105/README.md),
[8-root sequential audit](../results/anytime-sequential-20261105/README.md), and
[15-root tail-family audit](../results/anytime-tail-20261105/README.md)
retain their original scopes and checkpoint identities.
