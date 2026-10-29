# Reproducing the exact finite-support certificates

This directory is standalone. It contains the new dual solvers, exact
certificate verifiers, all benchmark certificates, and a clearly attributed
copy of the unchanged round-three primal implementation. No import from a
parent research directory is required.

The mathematical experiment is Bernoulli sampling from genuine fresh
units with hidden magnitudes and signs, a rare-positive class
\(0\le q_i\le1,\ \sum_iw_iq_i\le\rho\), and a uniform expected observation
budget \(B\). All first observations are charged.

## Verify the stored results without numerical dependencies

Python 3.12 was used. Verification requires only the standard library.
Run from this directory:

    python self_check_certificates.py

This re-verifies 33 exact lower certificates and 9 exact upper policies.
It also confirms rejection of six deliberate corruptions: rarity,
Bellman work price, claimed lower value, latent-genie terminal reward,
actual policy budget, and claimed upper risk. Checks remain active if
Python is invoked with its optimization flag.

Individual certificates can be checked with:

    python verify_finite_dual.py optimized_genie/three_scales_N8_B1000_lower.json
    python verify_policy_upper.py optimized_genie/three_scales_N8_B1000_upper.json

Each verifier rebuilds the relevant quantities with exact rational
arithmetic. It validates the law, rarity and budget, and all policy or
Bellman conditions. The lower verifier checks every prior against the
rarity polytope. The upper verifier computes exact conditional means,
second moments and observation counts, then maximizes the relevant
linear expressions over the rarity polytope by fractional knapsack.
Stored RMS displays are checked for downward rounding on lower bounds
and upward rounding on upper bounds.

## Re-run the numerical searches

The observed dependency versions are listed in requirements.txt.
A fresh environment can install them with:

    python -m pip install -r requirements.txt

Then run:

    python solve_finite_dual.py
    python compare_genie_certificates.py --caps 8 32
    python solve_genie_bracket.py
    python self_check_certificates.py

The first command independently solves the ordinary four-prior conic
dual on eight small instances and compares exact repaired lower bounds
with a reconstructed primal upper. The second uses fixed selected
quartets to demonstrate midpoint-genie bounds at two caps. The third
optimizes the full four-prior genie dual, reconstructs an observable
primal policy, and checks both bounds exactly.

On the included benchmarks, the third command stops when the exact
rational comparison \(U_N^2\le4L_N^2\) holds. Here \(U_N\) is a feasible
policy upper bound, and \(L_N\) is a feasible genie-dual lower bound.
The theorem gives

\[
 L_N\le P_\infty\le P_N\le U_N,\qquad
 L_N/8\le R_{\mu,\rho}(B)\le U_N.
\]

Consequently the stopping decision certifies a factor-16 bracket for
unrestricted adaptive minimax RMS risk. The output also supplies a
sharper pair-specific lower bound. This does not identify \(P_N\) or
the reported numerical values with the exact minimax risk.

The stored run tried caps 4, 8, 16, 32, except that perfect labels use
cap 1. Seven instances stopped at cap 1 or 4; the three-scale,
budget-1000 instance failed at 4 and passed at 8. There is no claim
that these small caps suffice uniformly over other laws or budgets.

## Files

- **solve_finite_dual.py** contains the independent compact conic dual.
  Its optional genie mode adds two shared latent perspective variables
  per atom. A separate exact backward pass repairs selected priors and
  prices before emitting a certificate.
- **verify_finite_dual.py** verifies ordinary cap certificates,
  midpoint-genie certificates, and full four-prior genie certificates.
  A cap certificate bounds the cap program only. A full genie certificate
  bounds the unrestricted program and also gives an adaptive-risk lower
  bound after the specified midpoint conversion.
- **verify_policy_upper.py** verifies the actual observable Poisson
  policy. Its risk upper uses the sum of the separate worst squared
  bias and worst variance, so their maxima need not be attained by the
  same prior.
- **inherited_flow_primal.py** is copied from
  research_round3/checks/solve_flow_program.py with attribution comments
  added. Its algorithm is unchanged; it is included solely to make the
  reproduction independent of the earlier directory.
- **certificates/** stores the eight ordinary cap certificates.
- **genie_certificates/** stores sixteen fixed-quartet midpoint
  certificates.
- **optimized_genie/** stores nine tested lower/upper pairs, including
  the one cap-4 pair that did not meet the stopping criterion.
- **certificate_self_check.json** records exact re-verification and
  negative-control outcomes.

All stored law inputs are exact finite decimals interpreted as rational
numbers. General calls to the repair functions must supply positive
rational masses summing exactly to one. The numerical optimizer can
return an inaccurate status; neither final feasibility nor the claimed
bounds depend on that status. Re-running a solver may select a different
valid quartet and produce slightly different certified numbers.
