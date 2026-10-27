# Nonlinear upper-route checkpoint

New files were confined to this `upper/` directory. The concurrent
`nonlinear-critical/` task and old paper, theorem meanings and freeze files
were read but not edited.

The constructive search considered learning a positive-gap profile from pilot
coins and then choosing/calibrating gambler survivor filters. The obstacle is
uniform calibration over global q: survivor responses weight q by the gap,
and fitting a finite collection of observable moments does not control the
target residual. No matching uniform-q upper bound was obtained.

A direct two-profile counterexample was then extended to any fixed per-coin
depth. The parent independently supplied the general normalized polynomial
formula and target moment; this agent supplied the elementary differential
energy bound and wrote the full proof and executable identity checks. The
adversarial review agent independently checked both the K=2 pair and the
general energy/integral argument. These are agent checks, not external review.

Actually executed from the repository root:

    python research/2026-10-27-nonlinear-population/upper/check_exact.py

Exit 0, Python 3.12.2. Verified with exact `fractions.Fraction` arithmetic:

* Differential, energy, endpoint and moment identities for K=1,...,16.
* Equality of all 31 local words of lengths zero through four for the explicit
  K=2 profiles, at a=1/4 and rho=1/16.
* Equality of all 1024 terminal transcripts of a ten-flip policy whose choices
  use other coins' histories and respect a four-flip local cap.
* Exact two-point midpoint risk and the risk of a retained failed profile
  selector. The selected example is a diagnostic, not a practical benchmark.

The parent then proposed a necessary local-depth tail for unrestricted
feedback using the common capped experiment. This agent proved the stronger
squared-risk version p_K >= 1-4 epsilon^2/Delta_K^2 by integrating squared
loss against the common no-exit subprobability measure. The source now also
contains the expected-work consequence (2K+1)p_K. The same reproduction
command was rerun successfully after these edits. It additionally enumerates
1024 transcripts for a feedback procedure allowed to cross the comparison
cap, checking equal exit probabilities, the common no-exit mass,
TV <= p_K, and the exact common-submeasure squared-risk inequality.

The JSON contains exact fractions and input-source SHA256 hashes. No numerical
quadrature, floating-point certification, Monte Carlo, external communication,
Lean build, or PDF compilation was performed by this agent. The arbitrary-K
and arbitrary-policy statements rely on the written proof, not extrapolation
from the finite checks. No commit was made.

The parent subsequently proposed a generic finite-approximation bridge.
This agent wrote `FINITE_APPROXIMATION.tex`: total-work truncation,
hidden-magnitude rounding, downward allocation-grid rounding, independent
activation to restore the uniform expected budget, both value inequalities,
and a finite-dimensional convex perspective/realization-flow formulation.
The adversarial review agent was sent the complete source. This is a written
proof; no finite convex program was solved, and the existing polynomial
checks do not verify this separate theorem.
