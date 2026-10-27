# Critical alpha=2 contract — 27 October 2026

Principal target: for the exact law F(d)=(d/a)^2 on (0,a], known a and
0<rho<=1/4, prove or refute the uniform all-algorithm characterization

    R_mu,rho(B) ~ min(rho, sqrt(rho(1+log(1/rho)))/(a sqrt(B))).

The experiment is the ordinary iid fresh-coin experiment. Magnitudes and signs
are hidden; q is any measurable [0,1]-valued function with integral q dmu<=rho.
Policies see only their independent seed and observable flip history, may
create/revisit/interleave coins, and have expected work<=B uniformly over q.
No pointwise q<=rho, known positive conditional law, observed D, known equality
theta=rho, deterministic cost cap, or unknown-rarity guarantee is substituted.
Universal constants must precede a,rho,B,q. Initially the law may be known.

The exact cutoff t satisfies rho=(t/a)^2[1+2log(a/t)]. For h<t,
Psi(h)=[2ht(1+log(a/t))-h^2]/a^2, and for h>=t it equals rho. Thus the stated
rate and Psi(B^-1/2) are universally comparable, including saturation.

## Actual new starting point

The previous session's alpha>2 theorem is preserved at commit d4f74a2, including
its reviewed source and locked separate-moment Lean bridge. HEAD at this turn's
first inspection was db25e62. Origin remains the renamed
davidiach/adaptive-threshold-estimation. Concurrent work modifies the workflow
and adds Tier5 and research/2026-10-27-minimax-audit. These are not this task's
files and must not be edited, reverted, staged or committed by it.

In particular, the other audit already contains a complete proposed paper proof
of the critical upper bound with an additional sqrt(1+log log(1/rho)) factor:
research/2026-10-27-minimax-audit/theorem/critical.tex. Its capped finite dictionary
has E Y²<=165rho/56 and E T<=1350a^-2 L(1+log L), L=1+log(1/rho).
This is pre-existing workspace work, not a discovery in this turn. Its exact
observed source hash is recorded in BASELINE.json. This task does not change
its review status or adopt its proof as Lean-checked. The desired improvement
must remove that factor or show an appropriate obstruction.

## Dependencies and early failure tests

Matching upper: a classifier-free or differently corrected estimator must avoid
the K log K cost of the current scale dictionary, where K~log(1/rho). Merely
altering summable dictionary weights cannot do this. The hard tests are q=1
on the bottom-rho gap region, log-uniform positive mass across geometric scales,
the saturation boundary, and joint limits in B,rho,a.

All-algorithm counterexample: a lower bound must apply to possibly biased,
budget-dependent, multi-coin policies. A sign-test entropy bound, a restricted
estimator search, or an unbiased single-coin obstruction is insufficient by
itself. Any reduction must account for simulation work, parameter dependence,
and preservation of the fixed magnitude law.

## Explicit fallback, not a weakening of the principal claim

An emerging fallback is a sharp characterization of the *unbiased single-coin*
variance-work product at one fixed critical law. This class may know rho and
the law, but observes at most one coin per output, may revisit it with unbounded
stopping, and is unbiased for every q in the global rarity class. Proving an
unavoidable log log(1/rho) factor for the entire class, including arbitrary
moment/work tradeoffs, would explain why the current unbiased constructions
cannot settle the principal problem. It would not refute the full minimax
conjecture. Any final report must say explicitly if that conjecture remains open.

Construction and adversarial review have separate owners. The reviewer does
not write the proof being judged. A second analytic pass will be used for a
complete candidate where possible; model diversity is not guaranteed. New
numerics have explicit finite horizons and floating-point limitations. No new
Lean target is accepted without a separately reviewed, locked specification;
formalization is pursued only if it removes a needed mathematical dependency.

Primary literature triage focuses on finite-gap sign-testing entropy and its
actual oracle model, rather than repeating the previous broad source audit.
Existing verification records and all previous locks are preserved.

## Explicit extension of the fallback after review

The single-coin product proof extends to uniform bias at most rho/64. A further
reviewed reduction selects one component using a seed distribution weighted by
the preselected number of coins. It transfers the lower bound to noninteractive
additive estimators, including heterogeneous components, shared randomness and
an unbounded finite-mean coin count selected independently of observations.
The class and its separate moment conditions are stated exactly in the TeX
note. This yields a matching restricted minimax rate with the extra factor
sqrt(1+log L). The extension broadens the fallback openly; it does not replace
the principal all-algorithm target. Nonlinear terminal aggregation and decisions
using observations from other coins remain outside the lower theorem.
