# Critical power margin: a controlled iterated-logarithm upper gap

Status: PROVED-ON-PAPER, reviewed in a separate adversarial agent pass; not Lean checked, not externally reviewed, priority unresolved. All logarithms without a subscript are natural. This file and its construction are new in this run. Existing route-a files are inputs, unchanged. The reviewer inspected the critical proof, arbitrary-law bracket, and bounded-channel extension, found no blocking issue, and requested the conditional iid suffix clarification now included below. Agent agreement is not external peer review.

## Precise claim

In the iid hidden-gap Bernoulli reservoir, suppose the known envelope is
`mu((0,x]) <= (x/a)^2` for `0<x<a`, with `0<a<=1/2`. Let `0<rho<=1/4` be known and require only `integral q dmu <= rho`. Put

`L=1+log(1/rho)`, `H=1+log L`.

There is an observable unbiased one-coin estimator Y, using only a,rho and flips, such that uniformly over all such laws and q,

`E Y = theta`, `E Y^2 <= 4 rho`, `E T_Y <= 1350 a^(-2) L H`.

Consequently for every B>0 there is an algorithm with uniform expected work <=B and RMS at most

`min(rho/2, sqrt(5400 rho L H/(a^2 B)))`.

The work is an expectation, not a deterministic or high-probability cap. The moment and work suprema are separate. Unknown individual gaps, signs, q, and individual mu are never queried. The theorem supplies a known-envelope, known-rarity upper bound; it also covers the exact alpha=2 power law.

For the exact law `F(d)=(d/a)^2` on `(0,a]`, the existing candidate has

`rho = (t/a)^2 [1+2 log(a/t)]` and, for `0<h<t`,
`Psi(h) = [2ht(1+log(a/t))-h^2]/a^2`;
for `h>=t`, `Psi(h)=rho`.

Uniformly in h,rho,a, this is comparable with universal constants to
`min(rho, h sqrt(rho L)/a)`.
Thus, conditional on the separately audited arbitrary-law lower theorem, the remaining RMS factor is only `sqrt(H)`, which is of order `sqrt(log log(1/rho))` as rho tends to zero. No matching alpha=2 result is asserted. At fixed positive rho the displayed upper is B^(-1/2), with a rho-dependent constant.

## Algorithm (finite arithmetic at every step)

For level j>=0 set `epsilon_j=16^(-(j+1))`,
`N_j=ceil(1/(a^2 rho epsilon_j))`,
`K_j=ceil(log_2(a sqrt(N_j)))`.
For k=0,...,K_j use references `r_k=a 2^(-(k+1))` and weight `1/(K_j+1)`.
For a coin with observed heads H_n, define

`L^+_(k,n)=(1+2r_k)^(H_n)(1-2r_k)^(n-H_n)`,
`L^-_(k,n)=(1-2r_k)^(H_n)(1+2r_k)^(n-H_n)`.

At times n=1,...,N_j-1, stop and output 0 if any L^- >= `(K_j+1)/epsilon_j`; output 1 if any L^+ >= `(K_j+1)/(rho epsilon_j)`. Give 0 priority in a simultaneous crossing. At time N_j, if neither rule has stopped earlier, output 1 iff H_N>N_j/2 (negative ties). This defines Z_j, work T_j<=N_j.

Draw J independently with `P(J=j)=2^(-(j+1))`, then draw one fresh coin. At J=0 run Z_0 and set Delta_0=Z_0. At J>=1 run Z_J and Z_(J-1) on two successive disjoint observation blocks **of that same coin**, and set Delta_J=Z_J-Z_(J-1). Return `Y=Delta_J/P(J)`. All subsequent fresh estimator calls use fresh iid coins and independent seeds. The two blocks need not have independent unconditional signs: they have exactly the same latent sign. This is essential to the disagreement bound.

Conditional on (D,S), the observations following the first classifier's bounded stopping time are again an iid Bernoulli tape, independent of the stopped prefix. To see this without an unbounded stopping theorem, condition on each event that the first stopping time equals n and each length-n observed binary prefix; the unused coordinates of an iid tape have their original product law. Summing these finitely many prefix events proves the claim. Thus the second block has exactly the marginal classifier law used in the telescoping and error arguments.

## Proof of errors and termination

All level procedures terminate by their deterministic cap; J is finite almost surely. Under the wrong sign each likelihood ratio is a nonnegative supermartingale starting at 1, since its expected multiplicative increment is `1-4r_k d<=1`. Finite-horizon stopping and the union bound imply a wrong crossing probability at most epsilon_j on positive coins, and rho epsilon_j on negative coins.

The forced empirical-majority error at N_j is at most `exp(-2 N_j d^2)` for either sign, including negative ties for positive coins. This is Hoeffding's inequality for iid Bernoulli observations. The event of a forced wrong answer is a subset of the full-tape majority-error event; no independence from prior stopping is used.

A self-contained proof of the concentration input is as follows. The centered Bernoulli log moment-generating function phi satisfies phi(0)=phi'(0)=0 and phi''(lambda)<=1/4, since its second derivative is the variance of a tilted Bernoulli law. Thus phi(lambda)<=lambda^2/8. Multiplying mgfs over independent observations and applying Markov at lambda=4d or -4d proves exp(-2Nd^2). The same argument covers the failure-indicator concentration used in confidence amplification.

For an envelope law, stochastic dominance by the exact alpha=2 law gives

`E exp(-2N D^2) <= (1-exp(-2Na^2))/(2Na^2) <= 1/(2Na^2)`.

Therefore `P(Z_j!=S) <= (theta+rho)epsilon_j +1/(2N_j a^2) <= (5/2)rho epsilon_j`.
More specifically `P(Z_j=1,S=0) <= (3/2)rho epsilon_j`.
All estimates are uniform over the global rarity class, without the pointwise condition q<=rho.

## Proof of work

Write x=min(d,a). Define
`A_s=1+log(K_j+1)+log(1/epsilon_j)+s log(1/rho)`, s=0,1.
For x>=N_j^(-1/2), choose k=ceil(log_2(a/x))<=K_j. Then x/4<=r_k<=x/2 and r_k<=1/4. The correct-sign log likelihood has iid increments, upward increments <1, and drift

`g=(1/2)log(1-4r_k^2)+d log((1+2r_k)/(1-2r_k)) >= (2/3)x^2`.

This follows from `log(1-z)>=-z/(1-z)` and `log((1+u)/(1-u))>=2u`. A bounded stopped-sum identity at the first crossing sigma of the appropriate threshold yields `E(sigma wedge n)<=A_s/g`; monotone convergence gives `E sigma <=(3/2) A_s/x^2`. Our capped work is no greater than sigma or N_j, even though the threshold rule is tested only before N_j. Thus

`E(T_j|d,s) <= min(N_j, (3/2)A_s/x^2)`.

For x<N_j^(-1/2) the same inequality holds because A_s>=1 and the right-hand side is N_j. This handles every d>0, including deterministic d=1/2.

Let c=3/2. The alpha=2 stochastic dominance and layer cake give

`E min(N,cA_0/x^2) <= c A_0 a^(-2)[1+log_+(Na^2)]`.

For the positive contribution, the sharp global-rarity rearrangement gives

`E q(D) min(N,cA_1/x^2) <= c A_1 a^(-2)[1+log_+(Na^2 rho/(cA_1))]`
`<= c A_1 a^(-2)[1+log_+(Na^2 rho)]`.

To verify the first positive inequality directly, integrate the decreasing bounded function `min(N,cA_1/(a^2 u))` over `0<u<rho`. When `Na^2 rho<=cA_1`, the integral is N rho<=cA_1/a^2; otherwise it is `(cA_1/a^2)[1+log(Na^2 rho/(cA_1))]`. For general envelope laws the same upper follows from `E[q 1_{x^-2>v}]<=min(rho, P(x^-2>v))` and Tonelli. This is not an assumption of conditional independence of S and D.

Bounding the negative-sign term by the full unweighted integral and adding the positive term therefore bounds E T_j. For L>=1, H=1+log L and all j>=0,

`Na^2 <= 2/(rho epsilon_j)`,
`K_j+1 <=5(L+j+1)`,
`A_0 <=7H(j+1)`, `A_1<=7H(j+1)+L`,
`1+log(Na^2) <=5L(j+1)`,
`1+log(Na^2 rho) <=5(j+1)`.

For clarity, the A_0 inequality uses `log(L+j+1)<=log L+j+1`, `4 log 2<3`, and `1+log5<3`; all other displayed bounds follow by substitution. These intentionally loose constants are universal.

Consequently

`E T_j <= (225/2) a^(-2) L H (j+1)^2`.

The increment uses two procedures only when j>=1, so its expected work is at most `225 a^(-2) L H (j+1)^2`. Since `sum_j 2^(-(j+1))(j+1)^2=6`, `E T_Y <=1350 a^(-2) L H`.

## Proof of second moment and unbiasedness

At the base, `E Delta_0^2=E Z_0<=rho+(3/2)rho/16=(35/32)rho`.
For j>=1, different decisions on the same latent coin imply at least one sign error, so

`E Delta_j^2 <= (5/2)rho(epsilon_j+epsilon_(j-1))=(85/32)rho16^(-j)`.

This does not require shared prefixes or independence. Tonelli and the independent level imply

`E Y^2 <= (35/16)rho + (85/16)rho sum_(j>=1)8^(-j) = (165/56)rho <4rho`.

The same error bounds imply `sum_j E|Delta_j|<infinity`. Thus signed expectations can be interchanged, telescope, and converge to theta:

`E Y=sum_j E Delta_j=lim_j E Z_j=theta`.

This proves integrability before the signed telescope, and proves finite expected work before any expected-budget aggregation.

## Expected-budget and confidence procedures

Put W=1350 a^(-2)LH and lambda=B/W. Draw an independent Poisson(lambda) number M of fresh independent Y calls, return lambda^(-1) sum Y_i, and clip to [0,rho]. The unclipped output has expectation theta and variance E Y^2/lambda<=4rho W/B. Expected work is at most B. If its displayed RMS bound exceeds rho/2, use the constant rho/2 instead. Clipping improves squared error but does not preserve unbiasedness.

For 0<delta<=1/4 let k be the least odd integer >=8 log(1/delta). Run k independent copies at budget B/k and take their median. Each copy, at radius `4 sqrt(rho W k/B)`, has failure probability <=1/4 by Chebyshev. Hoeffding's bound for the number of failures is <=exp(-k/8)<=delta. The constant rho/2 remains available, hence radius

`min(rho/2, 4 sqrt(rho W k/B))`

with total expected work at most B. There is no claim of a work-tail guarantee or data-computable inference under unknown mu.

When rho/2 is the smaller confidence radius, the algorithm explicitly chooses the constant rho/2 instead of the median procedure.

## Exact candidate calculation and limits

For alpha=2 and x=t/a, direct integration gives rho=x^2(1+2log(1/x)). With u=1+2log(1/x)>=1 this is rho=u exp(1-u), so L=u-log u. Since log u<=u/2 for u>=1, `L<=u<=2L`. For h<t,

`Psi(h)/h=(t/a^2)(u+1-h/t)`

lies between t u/a^2 and t(u+1)/a^2, hence between sqrt(rho L)/a and `2 sqrt(2rho L)/a`. Also Psi<=rho. For h>=t, Psi=rho. At h<t, `h sqrt(rho L)/a <=rho sqrt(L/u)<=rho`; at h>=t the minimum with rho is between rho/sqrt2 and rho. These observations prove the universal two-sided comparison, including transition and saturation, rather than only a fixed-rho limit.

## Remaining failing lemma

Matching Psi would require eliminating H from expected work or establishing a stronger lower obstruction. The finite family pays log(K_j+1) to control wrong crossings simultaneously over unknown latent scales; alpha=2 spreads negative work over logarithmically many scales. No proof that this loglog loss is necessary exists here. Neither the optimizer identity nor this construction resolves the arbitrary-law minimax conjecture.

## Arbitrary-law constructive upper bracket

This additional statement is PROVED-ON-PAPER and does not assume a margin or finite inverse moment. Set a=1/2 and choose any finite levels j=0,...,m with integer caps N_j>=4 and epsilon_j in (0,1]. Use the same finite-reference classifiers. Define beta_j=E_mu exp(-2N_j D^2), e_j=2rho epsilon_j+beta_j, and A_(j,s)=1+log(K_j+1)+log(1/epsilon_j)+s log(1/rho). Let f_(j,s)(d)=min(N_j,(3/2)A_(j,s)/d^2) and

`Q_rho(f)=integral_0^infinity min(rho,mu{f>u}) du`,
`c_j=E_mu f_(j,0)+Q_rho(f_(j,1))`.

For 0<=q<=1, integral q<=rho, layer cake gives integral q f<=Q_rho(f); equality holds by taking the top rho mass of f, with a fractional value of q on a possible cutoff atom. Thus this formula covers atoms and singular laws. All f are bounded and every c_j is finite regardless of inverse moments.

Put v_0=rho+rho epsilon_0+beta_0, C_0=c_0; and for j>=1 put v_j=e_j+e_(j-1), C_j=c_j+c_(j-1). Independent Poisson replication of each same-coin increment, with mean `lambda_j=B sqrt(v_j/C_j)/S`, where `S=sum_(j=0)^m sqrt(v_j C_j)`, has expected work <=B and variance <=S^2/B. Its expectation is E Z_m, so RMS is at most

`sqrt(e_m^2+S^2/B)`.

Explicitly, the unclipped estimator is `sum_j lambda_j^(-1) sum_(i=1)^(M_j) Delta_(j,i)`, where M_j are independent Poisson(lambda_j), fresh coins and seeds are independent across every (j,i), and each within-call pair retains its common latent coin.

The constants are positive, so no division by zero occurs. Projecting onto [0,rho] and comparing with rho/2 gives a fully specified upper bracket. This finite multilevel allocation is an established variance-cost argument, included to document the exact observable model and global-rarity work bound, not claimed as novel.

Known mu may be used to hardcode the finitely many design constants or certified upper bounds on beta_j,c_j; no sampled coin's D is provided. For arbitrary abstract mu, this is existence of an algorithm at that fixed known law, not a claim of uniform computability from every possible representation of a probability measure. An implementation using floating-point quadrature alone has numerical, rather than certified, risk constants. This bracket is separate from Psi and no universal comparison between them is proved here.

## Reusable bounded-channel theorem and its boundary

PROVED-ON-PAPER. Both upper constructions extend, with exactly the same constants, to an iid fresh-state reservoir whose repeated observations are conditionally iid X in [0,1] with mean `1/2+(2S-1)D`. The conditional observation laws can otherwise be arbitrary. Cost is one per X; the algorithm sees neither latent D nor S and receives no selected-state oracle. Replace the reference processes by

`M^+_(k,n)=product_i [1+2r_k(2X_i-1)]`,
`M^-_(k,n)=product_i [1-2r_k(2X_i-1)]`,

and use the same thresholds, caps, and empirical-mean tie convention. These factors are positive. Wrong-sign conditional mean factor is 1-4r_k d<=1. For the correct sign, concavity of log gives

`log(1+2r(2X-1)) >= X log(1+2r)+(1-X) log(1-2r)`.

Taking expectations gives at least the same drift g as before; upward log increments remain <1. The centered log mgf for any tilted [0,1] law has second derivative equal to a variance <=1/4, so the same concentration proof applies. All subsequent work, moment, and telescope arguments are unchanged. This is a direct real-observation rule; it does not discard X by Bernoulli conversion.

Nontrivial example: conditional on d,s, let X be uniform on `[1/2+(2s-1)d-1/4,1/2+(2s-1)d+1/4]`, with independent noise across revisits. For d<=a<=1/4 this lies in [0,1], has the required mean and positive variance 1/48. Thus for a quadratic margin envelope the same rare-event upper rate follows with one real draw per charged step. This is a synthetic derived example, not an empirical application or a minimax equality.

There is also an exact reduction: for an independent U~Uniform(0,1), `1{U<=X}` is conditionally iid Bernoulli with mean E[X|d,s]; it uses one X per converted bit and preserves theta. It discards information. Its direction transfers a Bernoulli upper algorithm to the bounded channel, not a Bernoulli lower bound to every bounded channel. For example, if X is deterministically equal to its conditional mean, each draw reveals S. Then n fresh states give variance <=rho/n, independent of a. No universal inverse-gap minimax lower can hold across all such channels. No extension to unbounded observations is asserted.

A separate explicit cross-state boundary uses an observed outer state Z~Uniform[-1,1], unknown beta in [-1/2,1/2], and real observation `X=1/2+(Z-beta)/8+xi`, where xi~Uniform[-1/16,1/16] independently. These observations lie in [0,1]. The target fraction whose conditional mean exceeds 1/2 is theta=(1-beta)/2. One draw at each independent observed Z gives the unbiased estimate `beta_hat=mean[Z-8(X-1/2)]`, with variance 1/(12n); `(1-beta_hat)/2` has variance 1/(48n). Charge one unit per outer draw and one per inner observation, total 2n. Although the margin near zero is linear, the shared regression parameter supplies O(B^-1/2) RMS without a margin logarithm. This is a different experiment with observed states and a common parametric regression structure; it proves why an unstructured reservoir lower bound cannot automatically be transferred merely because a marginal gap density looks similar.
