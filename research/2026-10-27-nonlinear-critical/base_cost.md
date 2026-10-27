# Critical entropy product with all-negative reference cost

Date: 2026-10-27. **Status: proposed paper lemma, pending independent review.**
This is a new adaptation of the inherited critical-two argument, not a new
formal theorem and not by itself a population lower bound. The parent
identified the need for all-negative cost and the cap `q <= 1/2`; this
agent checked the adaptation and supplied the constants below.

## Statement

Fix `a=1/4` and `mu(dd)=2d/a^2 dd` on `(0,a]`. Put

`X_rho={q measurable: 0<=q<=1/2, integral q dmu<=rho}`,
`L=1+log(1/rho)`, and `H=1+log L`, for `0<rho<=1/4`.

A procedure sees only its independent seed and observations from **one**
genuine reservoir coin. It may depend on `a,mu,rho`; it does not know its
latent magnitude, its sign, or the unknown function `q`. Its observable
stopping time `T` may be zero or unbounded. Suppose that it outputs a real
`Y`, and that

`sup_{q in X_rho}|E_qY-theta(q)| <= rho/64`,
`M=sup_{q in X_rho} E_qY^2 < infinity`, and
`sup_{q in X_rho} E_qT < infinity`.

Write `W0=E_{q=0}T`. There is a universal constant `c>0`, independent of
`rho` and of the procedure, such that

`M W0 >= c rho L H`.

The same lower bound, with a possibly smaller universal constant, holds
for `V W0`, where `V=sup_{q in X_rho} Var_q(Y)`. Indeed the variance floor
below gives `V>=2rho/3`, and the bias bound gives
`M<=V+(65rho/64)^2<=(3/2)V`. This corollary was pointed out by the
construction agent after checking the base-cost statement.

In particular, the cost in this lower bound is **only** its expected work
under the all-negative population. The separate finite uniform work
assumption ensures that all conditional restarts below terminate. The
proof does not replace that finite-work assumption by knowledge of a
latent gap. For capped procedures this assumption is automatic.

The constants here are universal with the fixed `a=1/4`; no claim uniform
in a varying endpoint `a` is made.

## Imported dependency, exact scope

We use the finite-grid Bernoulli sign lemma proved in the preserved
`research/2026-10-27-critical-two/construction.tex`, Section 2:

If `d_1>...>d_K`, `d_j/d_(j+1)>=2`, and `d_j<=1/128`, and one observable
single-coin sign test has error at most `1/10` at every Bernoulli law
`1/2 +/- d_j`, with finite expected stopping under both signs, then

`sum_j d_j^2 E_{-d_j}tau >= c_s K log K`,

where `c_s=1/512` and `K>=K_s=ceil(exp(32))` suffice. The test is the same
at every gap and need not terminate or be correct at the fair coin.
Its proof uses finite-prefix comparisons and the overlap of finite time
windows; it does not import an optional-stopping assertion under the fair
law. This inherited paper lemma was separately agent-reviewed, not Lean
formalized or externally reviewed. The present adaptation does not modify
that source or its review record.

## 1. Conditional integrability and a baseline variance floor

Define nonnegative extended conditional moments under a fixed gap and sign,

`M_s(d)=E_{d,s}Y^2`, `w_s(d)=E_{d,s}T`.

Both admissible populations `q=0` and `q(d)=rho` belong to `X_rho`.
Their finite moments imply

`integral M_- dmu <= M`, `integral M_+ dmu <= M/rho`,

and finite integrals of both work functions. Outside one common null set,
all these conditional quantities are finite. Define the signed conditional
means there, and assign arbitrary values on that null set. In particular,
the response

`f(d)=E_{d,+}Y-E_{d,-}Y`

is integrable. Subtracting the two bias guarantees gives

`integral f dmu=(E_rho Y-E_0Y)/rho >= 31/32`.

Condition first on the hidden magnitude and then on the sign at the
constant-prior population `q=rho`. The law of total variance and Jensen
yield

`Var_rho(Y) >= rho(1-rho) integral f^2 dmu
            >= rho(1-rho)(31/32)^2 >= 2rho/3`.

This step uses no exact unbiasedness and no pointwise response identity.
It holds for every procedure satisfying the stated bias condition,
including the normalized procedure constructed next.

## 2. Remove pre-observation thinning without changing expectations

The event `A={T>=1}` is decided by the independent seed alone. Its
probability `p` is the same under every latent state. We have `p>0`:
otherwise the output expectation would be independent of the population,
contradicting the bias guarantees at target values zero and `rho`.
The output on `A^c` has no observed bits, so

`c0=E[Y 1_(A^c)]`

is finite and independent of the population. With the seed conditioned on
`A`, define a new observable procedure

`Z=pY+c0`, `T_Z=T`.

It has exactly the original expectations at every `q`, and always makes
at least one observation. Conditioning on a known seed event can be
implemented by resampling independent seeds before observing the coin;
the reduction may use the known constants `p,c0` because neither depends
on the unknown population or its realized latent variables.

For `p<1`, expanding the square and using Cauchy--Schwarz on `A^c` gives

`E_qZ^2 = p E_q[Y^2 1_A]+2c0 E_qY-c0^2
         <= pM+2c0 E_qY-c0^2/(1-p)
         <= pM+(1-p)(E_qY)^2
         <= pM+2rho^2 =: m`.

For `p=1`, take `c0=0`; the final inequality holds directly. The bound
uses `|E_qY|<=65rho/64`. The preceding variance floor applied to `Z`
shows `m>=2rho/3`, and consequently

`pM >= 2rho/3-2rho^2 >= rho/6`.

Let `P0=MW0` and `W0Z=E_0 T_Z=W0/p`. Since `W0Z>=1`,

`m <= 4pM <= 4P0`,
`m W0Z <= 4P0`, and `P0>=rho/6`.                 (A)

Indeed `2rho^2<=rho/2<=3pM`. All occurrences of work in (A) are
all-negative work, so there is no hidden replacement by a supremum.

## 3. Good gaps under the capped global class

Use conditional moments and means of `Z` from now on, with the same
notation. Its uniform raw second moment is at most `m`. The negative
moment bad set

`B_-={d: M_-(d)>1/64}`

has mass at most `64m`. Define

`B_+={d: M_+(d)-M_-(d)>2m/rho}`.

If `mu(B_+)>=2rho`, nonatomicity of the exact power law gives a measurable
subset `E` of mass `2rho`. The population `q=(1/2)1_E` is admissible and
would satisfy

`E_qZ^2 = integral M_- dmu + (1/2)integral_E(M_+-M_-)dmu > 2m`,

contradicting its moment bound. Thus `mu(B_+)<2rho`.

The response bad set `B_f={d:f(d)<3/4}` also has mass less than `2rho`.
Otherwise choose such a set `E` of mass `2rho`. Its population has target
exactly `rho`, while

`E_(1_E/2)Z-E_0Z=(1/2)integral_E f dmu < 3rho/4`.

The bias bounds instead force this difference to be at least `31rho/32`.
This contradiction uses the actual capped global class, not a pointwise
constraint `q<=rho` and not a known target equality for all populations.

After excluding these sets and the integrability null sets, the good set
`G` satisfies

`mu(G^c)<=64m+4rho<=70m`.

At every good gap,

`|E_-Z|<=1/8`, `E_+Z>=5/8`,
`M_-<=1/64`, `M_+<=1/64+2m/rho`.                  (B)

## 4. One common sign test and its negative work

Set `n=ceil(512(1+m/rho))`. Since `m/rho>=2/3`,

`n<=1282m/rho`.

On one fixed-gap coin, run the active procedure `n` times with independent
seeds, each restart using the next unused flip. Output plus if the mean
of the `n` outputs exceeds `3/8`. Conditional on the fixed hidden state,
the restarts are iid: condition on each finite stopping prefix, use
independence of its unused iid suffix, and sum over the countably many
prefixes. Finite conditional expected work makes the stopping times
finite almost surely at each selected good gap and both signs. No new
latent magnitude is drawn by these restarts.

By (B), both mean separations from the threshold are at least `1/4`.
Chebyshev bounds either error by

`16(1/64+2m/rho)/n < 1/10`.

This is the *same* test for all good gaps. At gap `d` its negative expected
work is exactly `n w_-(d)`.

## 5. Geometric gap selection charges only all-negative work

For `j>=3`, let

`I_j=(a4^(-j)/2,a4^(-j)]`, `mu(I_j)=(3/4)16^(-j)`.

Put

`J=floor(log_16(3/(560m)))`, `K=J-2`.

When `J>=3`, every retained annulus has mass at least `140m`, so the
good set occupies at least half its mass. Select `d_j in G intersect I_j`
with

`w_-(d_j) <= (4/mu(I_j)) integral_(I_j) w_- dmu`.

This is possible by averaging; strict positivity of the integral follows
because the active procedure always takes at least one observation.
The selections are only existential proof objects. They are not inputs
to the procedure. Their successive ratios exceed two, and every gap is
at most `1/256`, within the sign lemma's range. Also

`sum_j d_j^2 w_-(d_j) <= (16a^2/3) integral w_- dmu
                       = (16a^2/3) W0Z`.

For `K>=K_s`, the imported sign lemma, the restart bound, and (A) imply

`c_s K log K <= sum_j d_j^2 n w_-(d_j)
             <= (16a^2/3)(1282m/rho)W0Z
             <= 30000 a^2 P0/rho`.                         (C)

The last constant is conservative: `(16/3)*1282*4 < 30000`.

## 6. All rarities and a nonzero constant

For sufficiently small `rho`, if `P0>=sqrt(rho)` the required lower bound
already follows, since `sqrt(rho)LH -> 0`. Otherwise (A) gives
`m<=4sqrt(rho)`, and

`K >= [0.5 log(1/rho)-log(2240/3)]/log16 - 3`.

Thus for all sufficiently small universal `rho`, `K` exceeds `K_s`, is
at least a positive universal multiple of `L`, and has
`log K >= (1/2)log L`. Inequality (C), with fixed `a=1/4`, yields
`P0>=c rho L H`. For the remaining compact interval of rarities, (A)
gives `P0>=rho/6`. Decreasing the same positive universal constant covers
that interval. The proof therefore establishes the stated result for
every `0<rho<=1/4`, not only along an asymptotic sequence.

## Audit notes and remaining work

- The strengthened statement uses one specified work law and either a
  separate uniform raw moment or a separate uniform variance. It does not
  replace these products by a supremum of same-population products.
- The unknown allocation is capped by `1/2`; the good-set proof explicitly
  uses sets of mass `2rho`. The old uncapped proof's sets of mass `rho`
  cannot simply be reused.
- This proof handles arbitrary pre-observation thinning and unbounded
  stopping. Conditional sign tests are only run at gaps where both
  conditional moments and conditional work are finite.
- The inherited entropy lemma is the only non-elementary dependency.
  It remains a reviewed paper argument, not an accepted Lean target.
- Turning this lemma into hard pairs against every acquisition policy,
  interchanging the policy/pair optimizations, and transferring those pairs
  to arbitrary population interleaving are separate unproved steps here.
  In particular this file alone does not refute the full rare-event
  minimax conjecture.
