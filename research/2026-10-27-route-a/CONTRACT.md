# Route A research contract — 27 October 2026

## Principal question and selected restriction

The principal question remains the arbitrary-law, known-mu/known-rho upper
bound R <= C Psi with a universal constant. Initial attacks on point masses,
separated atoms, endpoint atoms, and power margins did not refute it. The
selected smallest substantial result is its previously unresolved power-margin
regime **alpha > 2**, allowing constants depending on alpha. This restriction
is explicit; it does not settle the arbitrary-law conjecture or alpha = 2.

**Proposed statement.** For every alpha > 2 there are finite constants
c_alpha,C_alpha > 0 such that, for every 0 < a <= 1/2, 0 < rho <= 1/4,
B >= 1, with F_mu(d)=(d/a)^alpha on (0,a],

    c_alpha min(rho, sqrt(rho)/(a sqrt(B)))
      <= R_mu,rho(B)
      <= C_alpha min(rho, sqrt(rho)/(a sqrt(B))).

The upper algorithm may depend on alpha,a,rho,B, and must work for every
measurable q:(0,1/2] -> [0,1] with integral q dmu <= rho. It receives neither
q nor the individual D or S. A stronger upper statement is sought for every
law satisfying F_mu(d) <= min(1,(d/a)^alpha), using the same algorithm and
constants. Loss is ordinary RMS. Cost counts coin flips, with uniform
expected total <= B; no deterministic cost cap or computational-time bound
is asserted. The lower bound concerns every randomized, creating/revisiting/
interleaving iid-coin algorithm with measurable observable-history policies
and the same uniform expected budget. No equality theta=rho or pointwise
q<=rho is assumed.

The construction target is an observable estimator Y, unbiased for all q,
with E Y^2 <= C rho and E T <= C_alpha/a^2 uniformly over that class. These
are separate bounds. Exact-budget batching and clipping should yield the
displayed rate, with a constant estimator covering saturation. The lower
bound may use the audited imported single-coin theorem, explicitly retaining
paper-proof status and its source dependency.

## Dependency graph and decisive tests

Asymmetric exponential tests -> observable sign classifier with errors
(rho epsilon,epsilon) -> randomized telescoping with second moment O(rho)
-> integrated work bound using the power margin and only integral q<=rho
-> exact expected-budget estimator. Independent chain: Lee–Valiant input +
finite-prefix hybrid reduction -> existing Psi lower bound -> power-law rate.

Falsifiers include: a noncomputable/infinite dictionary check at a finite
prefix; hidden access to D; false-negative control only for a fixed gap;
assuming E(q/D^2) <= rho E(D^-2); a residual log(1/rho) in uniform work;
uncertified optional stopping; telescope convergence without integrability;
wrong saturation when B is below one-estimator cost; or a predecessor already
proving the same model and regime. Test D=1/2, very small D, rho tending to
zero jointly with B, q concentrated on the smallest gaps, and alpha down to 2.
The constants may diverge as alpha decreases to 2; suppressing this dependence
would invalidate the intended claim.

## Triage and fallback

| Target | Importance / overlap | Plausibility and decisive failure test |
|---|---|---|
| Full arbitrary-law Route A | Main open question; optimizer already solved, but no observable upper | Unknown-gap screening across many separated scales is the missing lemma. A restricted estimator failure is insufficient for impossibility. |
| Power margins alpha > 2 | Explicitly open in continuation; standard sequential-test and randomized-telescope ingredients overlap prior work | Asymmetric errors make negative noise O(rho); integrable inverse-square work and a rearrangement bound may absorb positive log-rarity cost. Test concentration of q near zero. Selected restricted principal target. |
| alpha = 2 | Critical unresolved regime | Current inverse-square work integral diverges; needs cutoff-dependent construction. Keep open rather than extrapolate. |
| Two separated atoms | Useful stress test and possible fallback | Finite test dictionaries remove unknown-scale tail. Existing separated-coin theorems overlap; any result must be uniform in masses and scale separation to be substantial. |
| Route B strict two-atom gap | Important structural alternative | All-algorithm information regularity and hidden-magnitude nuisance remain substantial new dependencies. No reason to divert before testing the Route A construction. |

Fallback: if the alpha > 2 construction fails, finish a fully explicit two-atom
analysis, identifying precisely whether constants depend on atom masses or
scale separation. Do not label a mass-dependent extension of known minimum-gap
results a major advance. Route C is not activated while Route A has a credible
construction; exact unknown-rarity adaptation is already refuted.

## Evidence and review

The main result will initially be a **paper proof with agent review**, not
Lean-checked and not externally specialist-reviewed. A separate agent audits
sources and attacks the proof without authoring it. Model diversity is not
guaranteed. Numerical diagnostics are implementation/identity checks, never
an all-algorithm argument. A separately locked Lean bridge for the existing
713 construction supports correct separate-supremum accounting but is not
evidence for the new rare-event theorem. Imported sources and old locks stay
unchanged. Failed approaches, exact commands and source hashes are retained.
