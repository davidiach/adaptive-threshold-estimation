# Upper-route run log

Work was confined to this new `upper/` directory. No historical freeze or
paper source was edited.

1. Inspected the inherited single-coin critical obstruction, critical upper
   construction, and the new finite-horizon Bayes diagnostic source. Developed
   the exact two-gap moment estimator and the restricted pilot no-gain proof.
2. Wrote `proof.tex`, `RESULT.md`, `two_gap_control.py`, and `check_exact.py`.
3. Attempted `.runtime/python/python.exe .../check_exact.py`. This path does
   not exist; the attempt did not run the verifier. Inspected the installed
   executable and corrected the documented command to `python`.
4. Ran from the repository root:

       python research/2026-10-27-population-step/upper/check_exact.py

   Exit 0. Python 3.12.2. All six rational laws and 18 complete finite
   pilot/production transcript checks passed, along with the observation API
   and flip-accounting check. Raw exact output: `exact_checks.json`.
5. Independently reread all of `lower/population_information.tex` and checked
   the direct-sum proof, finite-prefix total-variation passage, gambler's-ruin
   bounds, integral constants, and finite-cap limit. No blocker found in that
   reviewed version; this is agent review, not external peer review.
6. The separate audit agent read all of `upper/proof.tex`, checked coefficient
   coercivity and the active-slope argument, all moment formulas, endpoint
   `d2=1/2`, and the infinite-MSE case. It reported no blocker and will record
   a hash-pinned review in the parent directory.

No Monte Carlo benchmark, minimax numerical certificate, Lean proof, or
compiled PDF was produced by these commands. Exact transcript enumeration
supports only the displayed finite identities; the saddle theorem is a
written proof. A failed search for terminal TeX executables did not compile
the document. Compilation, integration, commit, and push are handled by the
parent agent.

The arithmetic also exposes poor practical constants: at gaps 1/8 and 1/4
with equal masses and theta=0, the raw three-flip estimator has variance
427/16. Thus this particular polynomial construction is not advanced as a
competitive rare-event method.
