# Population information, a radial estimator, and verified single-coin limits

Date: 2026-10-27. Status: **PROVED-ON-PAPER**. Only the verified small-bias
result imports the finite-gap sign entropy lemma audited in the companion
single-coin review; the population information results below are independent
of that lemma. Not Lean formalized. No external review or priority claim.

## New population information results

The complete statements and elementary proofs are in
[population_information.tex](population_information.tex). They do not use
the finite-gap sign entropy lemma.

**Finite-prefix information/work direct sum.** Fix an admissible affine
submodel `q_t=q_*+t u` with hidden iid magnitudes supported below `a<1/2`.
If every capped one-coin observation policy has directional Fisher
information at most `kappa(t)` times its expected charged flips, the same
inequality holds for every capped population policy, including adaptive
coin creation and arbitrary interleaving. The proof freezes a reference
value `t` and simulates the other coins only inside the mathematical
comparison; it does not supply simulations, gaps or `q` to the actual
algorithm. Independent seeds and policies are held fixed when
differentiating.

For an algorithm satisfying the uniform expected budget `B` along the
path, finite prefixes and separate almost-sure endpoint termination give

    TV(P_alpha, P_beta) <= (sqrt(B)/2) integral_alpha^beta sqrt(kappa(t)) dt.

If the right side is at most `1/2`, the two-point worst-case RMS is at
least one quarter of the target separation. This is a reusable conditional
reduction for unrestricted population algorithms. It does not assert the
missing one-coin directional information bound, or unbounded-stopping
quadratic-mean differentiability.

**DISPROVED: the extra-logarithm radial information bound.** In the exact
quadratic model with `a=1/4`, let `w_b=min(1,b^2/d^2)` satisfy `Ew_b=rho`,
and take `q_eta=(1+eta)w_b/2`, `|eta|<=1/2`. This is an admissible radial
submodel. A directly observable walk stopped at `-1` or
`M=ceil(8a/b)` has at `eta=0` expected work `<25` and its upper-hit
indicator has Fisher information at least `(2/5)b^2/a`. Consequently
the finite-cap one-coin information/work envelope is at least

    a^2 rho / [32(1+log(1/rho))].

This rules out a uniform radial information envelope of order
`a^2 rho/[L(1+log L)]`. It replaces the earlier small-scale floating-point
diagnostic with a paper proof valid for every allowed rarity. The stopped
walk itself has unbounded work; finite-cap truncations converge in work,
event probability and its derivative, so the envelope statement concerns
finite-cap policies exactly as stated. All original observations are
charged. This is not an estimator valid for arbitrary `q`, and it neither
proves nor disproves the unrestricted minimax conjecture.

**Constructive radial-submodel upper bound.** Calibrating the same walk
indicator using its known radial-profile probabilities gives a single-coin
output with `E_eta Y=theta(q_eta)`, uniform variance at most
`(11/2)rho L`, and uniform expected work `<29`. Independent centered
Poisson replication then yields, for every `B>0`,

    RMS <= min{rho/4, sqrt(160 rho L/B)}

on this radial submodel. Every flip is charged, and the count and production
coins are independent. The TeX proof supplies pseudocode, termination,
moment/work calculations, and a finite-calibration error bound. The ideal
statement allows exact deterministic evaluation of known one-dimensional
calibration integrals; no numerical implementation or practical benchmark
is claimed. In particular, these calibration integrals use the **known
profile**, not an oracle for an arbitrary unknown `q`.

This proves that the extra critical logarithm is avoidable on this known
one-dimensional family, even though magnitudes remain hidden. It isolates
the unresolved obstruction in the general nuisance allocation and possible
nonlinear population procedures.

## Verified small-bias theorem (inherited concurrently; refined proof here)

Provenance correction: the pre-existing, concurrently maintained
`research/2026-10-27-critical-two/construction-notes.md` already contained the
small-bias extension when the separate reviewer inspected it. Its canonical
`construction.tex` also now contains that theorem. The derivation here was
independent and refines constants, but is **not counted as discovery of a new
theorem**. The review packet pins the inherited source snapshot separately.

Let `a=1/4`, `mu(dd)=2d/a^2 dd` on `(0,a]`, `0<rho<=1/4`,
`L=1+log(1/rho)`, and `H=1+log L`. A single-coin procedure observes one
genuine hidden-gap reservoir coin; its policy, auxiliary randomness, stopping
time and real-valued output may depend on `mu,rho` but not on the unknown
measurable sign allocation `q`. It may stop without observing the coin.
Every observed flip is charged. Computation and independent randomization
are free. The global class is `Q_rho={0<=q<=1: integral q dmu<=rho}`.

Write `V=sup_q Var_q(Y)` and `W=sup_q E_q T`. There is a universal constant
`c>0` such that every procedure satisfying `V,W<infinity` and

    sup_q |E_q Y - theta(q)| <= rho/64

satisfies

    V W >= c rho L H.

The same lower bound holds with `sup_q E_q Y^2` in place of `V`.
The companion unbiased construction supplies the matching upper order, since
zero bias is permitted. Consequently the infimum over this larger class of
uniformly small-bias single-coin procedures is still of order `rho L H`.
All constants here are universal because `a` is fixed. No uniform claim in
varying `a` is made by this theorem.

The complete independent proof is in [proof.tex](proof.tex). It extends the exact-response
identity of the inherited argument to an integrated response inequality.
It handles arbitrary signed outputs, arbitrary thinning before the first
observation, and unbounded stopping with finite expected work. The proof
does not exchange `sup_q Var_q(Y) * sup_q E_q T` with
`sup_q [Var_q(Y) E_q T]`.

## Consequence for a restricted population class

Consider a deterministic arithmetic average of `n>=1` independent copies of
the same single-coin procedure, with no nonlinear postprocessing:

    theta_hat = (Y_1+...+Y_n)/n.

If its worst-case RMS is at most `epsilon<=rho/64` and its uniform expected
work is at most `B`, then

    B epsilon^2 >= c rho L H.

Indeed the RMS guarantee gives uniform kernel bias at most `epsilon` and
`V/n<=epsilon^2`; the budget gives `n W<=B`. This remains valid when the
kernel and `n` depend on `B,rho`. Thus introducing a controlled bias and
choosing a new single-coin kernel for each budget does not remove the
iterated logarithm in this class.

This corollary **does not** apply automatically after clipping or nonlinear
aggregation, to interaction among genuine coins, to unequal kernels with
cancelling biases, or to data-dependent replication counts. A large raw
variance-work product is not a lower bound on the clipped squared-error risk.
The lower bound for unrestricted population algorithms remains unresolved.

## Why the elementary projection route remains incomplete

At a fixed finite number of iid coins, first-order Hoeffding projection at a
known reference `q0` can extract a response identity from a fully unbiased
population estimator. But that identity alone is insufficient here:

1. The conditional expectation defining the projection may depend on an
   entire infinite coin tape. Its existence in `L2` is not an observable
   finite-work implementation.
2. The orthogonal-projection variance inequality is at the reference law.
   It does not supply the uniform moment bound over all `Q_rho` used above.
3. Uniformly small population bias does not by itself bound pointwise
   derivatives of its expectation along submodels. Taking a derivative is
   therefore not a valid replacement for the exact unbiased identity.
4. A clipped or otherwise nonlinear population estimate is not an arithmetic
   average of the extracted single-coin outputs.

These are missing premises, not an impossibility theorem for a better
reduction. No purported all-population lower bound is accepted in this file.

## Actual verification and review

The small-bias proof uses only the finite-gap entropy lemma as its
non-elementary input; its exact statement is reproduced in the TeX fragment.
The population information proof uses finite transcript likelihoods,
Cauchy--Schwarz, elementary gambler's-ruin recurrences, and dominated/monotone
convergence. All calculations are explicit. No numerical experiment or Lean
run is claimed for these results. The `audit_singlecoin` agent reviewed the
complete small-bias proof, direct-sum argument, radial obstruction, and
calibrated radial estimator, finding no blocking defect. Its exact arithmetic
checks and source hashes are recorded in the companion audit directory.
The `population_upper` agent independently checked the direct-sum and radial
obstruction, then suggested the calibrated upper corollary; that suggestion
is a mathematical contribution, not independent review of its own work.
The integrating agent also checked the corollary constants and requested the
explicit fixed-`b,M` qualification for calibration error. These are agent
reviews, not external peer review or a priority certification.
