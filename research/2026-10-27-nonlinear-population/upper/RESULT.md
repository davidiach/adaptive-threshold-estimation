# Nonlinear acquisition attempt: exact bounded-depth obstruction

**PROVED-ON-PAPER:** arbitrary feedback and pilot-dependent acquisition cannot
repair a fixed per-coin observation-depth loss of identification. For the
known exact quadratic gap law and global rarity rho, there are two explicit
feasible allocations with identical transcripts for every algorithm that
uses at most 2K flips on each individual coin, while their target values
differ by rho / ((K+1)(2K+1)). Thus even unlimited total work in this restricted
experiment leaves RMS error at least half that difference.

There is also a necessary condition for **unrestricted** feedback. With
Delta_K=rho/((K+1)(2K+1)), any algorithm of RMS error at most epsilon under
both constructed populations must observe more than 2K flips on some coin
with the same probability p_K under each population, and

    p_K >= 1 - 4 epsilon^2/Delta_K^2.

In particular Delta_K>=4epsilon forces p_K>=3/4 under each law. Expected
total work under each law is at least (2K+1)p_K. The proof uses a common
terminal subprobability measure on the event that no coin exceeds the cap;
it does not truncate the algorithm and silently retain its original risk.
Each K uses its own constructed pair of allocations. These bounds cannot
be integrated over K as tails under one fixed allocation without a separate
argument.

This does **not** settle the unrestricted population minimax rate. The
identification theorem's cap is explicit, and the additional depth-tail
necessity is too weak to determine the critical work rate. No novelty claim,
Lean formalization, or human
peer review is asserted. It is a diagnostic for the attempted feedback
construction, not a resolution of the rare-event minimax problem.

## Construction attempted and point of failure

The attempted route was to use pilot coins to learn a positive-gap profile,
then select survivor/gambler filters and recalibrate their outputs using that
profile. Acquisition could depend on previous population observations, so
this route genuinely left fixed independent transcript designs.

A gambler upper-hit probability measures a weighted positive mass, with a
gap-dependent response approximately proportional to d. Radial-profile
calibration therefore does not estimate integral q uniformly over arbitrary
q. In general, if a pilot-selected single-coin output has conditional means
m_plus(d), m_minus(d), and g=m_plus-m_minus, and is calibrated at q_hat, its
actual conditional bias is

    integral (q-q_hat)(g-1) dmu.

Controlling fitted target mass or fitting observed pilot moments does not
control this residual. No argument closing that obligation was obtained.
The explicit pair in `proof.tex` proves an exact failure even if the pilot
has arbitrarily many observations with a fixed local cap, and even if
subsequent acquisition adapts to every pilot observation.

For K=2 the normalized polynomial is

    u(x) = 1 - (14/3)x^2 + (21/5)x^4.

Set h=a sqrt(rho) and q_plus/minus(d)=(1 plus/minus u(d/h))/2 on d<=h,
zero otherwise. Their masses are 8rho/15 and 7rho/15. Every word of at most
four flips has exactly the same probability under both. Thus a fitted profile
can have a wrong target even when it reproduces **all** permitted pilot and
production distributions. Increasing the number of shallow observations
cannot fix this particular failure.

## Why the general bound is certified on paper

The proof builds u_K from the odd Legendre polynomial P_(2K+1) divided by x
and its derivative at zero. Orthogonality cancels the first K odd moments.
A short differential-equation energy argument proves |u_K|<=1 directly,
without importing an unverified Jacobi-polynomial extremum theorem. Rodrigues'
formula supplies all polynomial identities used in the proof. The transcript
argument explicitly permits arbitrary feedback, independent seeds, and
unbounded numbers of coins; terminal equality assumes almost-sure termination.

`check_exact.py` verifies polynomial identities with rational arithmetic and
checks an explicit feedback policy by full finite transcript enumeration.
The finite checks are not the proof for arbitrary K or arbitrary policies.
See `exact_checks.json` for actual run evidence and source hashes.

Reproduce from the repository root:

    python research/2026-10-27-nonlinear-population/upper/check_exact.py

No candidate uniform-q estimator beating the existing critical upper bound
was accepted in this pass. The next construction needs increasing local
depth and a valid response-weighted calibration guarantee; fixed-depth
empirical profile agreement is insufficient.

## A faithful finite approximation route for the unrestricted problem

`FINITE_APPROXIMATION.tex` gives a separate **PROVED-ON-PAPER** bridge for
arbitrary known gap laws, full cross-coin feedback and expected budgets.
Let V_mu(B)=R_mu,rho(B)^2, cap total flips at N, round gaps within eta, and
round each finite-law allocation coordinate down to a gamma grid. Let G be
the resulting finite-parameter, full-feedback minimax MSE at the same uniform
expected budget B>0. With

    C=N^2(eta+gamma),
    E=rho^2*N*(eta+gamma)+2*rho*gamma,

the proof gives

    |V_mu(B)-G(B)| <= rho^2*B/N + E + rho^2*C/(4*(B+C)).

Independent activation with a known probability, otherwise returning rho/2,
restores the exact expected budget after transfer. Every added error is
accounted for. Choosing eta=gamma=N^(-3) proves convergence for fixed mu,
rho and positive B. The finite experiment retains hidden magnitudes and all
feedback decisions; it does not grant selected-magnitude queries.

The finite problem has an explicit finite-dimensional convex formulation
using action realization weights and quadratic-perspective terminal losses.
This is a justified approximation method, not a solved finite program or a
closed-form rare-event minimax law. Its size can be enormous. For arbitrary
measures the statement declares an exact bin-mass/real-arithmetic oracle;
effective computability does not follow merely from describing mu as known.
No numerical solve or validation of an implementation of this convex program
was performed in this pass.
