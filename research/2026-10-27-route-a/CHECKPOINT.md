# Research checkpoint — 27 October 2026

**Mathematical change.** The complete power-margin regime alpha>2, previously
open in this repository, now has a paper proof of

    R_mu,rho(B) ~_alpha min(rho, sqrt(rho)/(a sqrt(B)))

for F_mu(d)=(d/a)^alpha, all 0<a<=1/2,0<rho<=1/4,B>=1, and every measurable
q with integral q dmu<=rho. The [complete proof](construction.tex) gives an
observable algorithm and a matching lower bound. The upper also works over
the whole margin-envelope class with known alpha,a,rho, without knowing mu.

The key construction has E Y=theta, E Y²<3rho, and E T<=w_alpha/a² separately.
Negative coins have error rho epsilon; positive coins have error epsilon.
Only positive work pays log(1/rho), and the sharp global-rarity inverse-square
integral absorbs that term for alpha>2. Random-level debiasing and Poisson
replication are established tools, not claimed inventions. The matching lower
imports Lee–Valiant's single-coin inequality/decomposition, with smallness,
large-gap, stopping, RMS conversion, and simulation details supplied in the note.

**Evidence.** Two agents who did not author the proof reviewed it. Both accepted
the exact final TeX SHA256
`ff70296efd76f7b1fd0ac50d12eff1a22361b5bb566dc97c82836833640b3d00`.
See [adversarial review](review.md), [second analytic review](second-review.md),
and [primary-source comparison](sources.md). Model diversity is not guaranteed;
this is not external specialist review or novelty certification. The main
theorem is not Lean-checked. The final TeX compiled successfully through
`compile_latex_document` after one TeX brace correction; an earlier attempted
compile during active editing failed as well. Compilation is not proof checking.

**Supporting Lean result.** `ThresholdHC.ResearchRouteA.separate_moment_bounds`
and `uniform_family_bounds` expose the existing estimator's separate 23I/31I
bounds and the product of separate suprema <=713I² within its conditional
kernel model. The exact specification, complete local definitional closure,
pins and verifier are locked in SPEC_LOCK_v1.json; see [formal audit](formal-audit.md).
This is a foundation repair, not the main discovery, a new constant, or a
fresh-coin realization. Specification SHA256:
`d114a2734cfd0164def475115d0ebb25d1ba49c7f87bb96fa45e441c3eb40dbe`.
Lock SHA256:
`1b8115cf053e978f35d28854544b9ed01d871a5c7bc4eedf936c13ceebe9d4c9`.

**Reproducibility.** From the repository root:

```text
python research/2026-10-27-route-a/check_construction.py
python lean/ThresholdHC/ResearchRouteA/verify.py
python research/2026-10-27-route-a/acceptance_check.py
```

The last command supplies the existing local Lean runtime automatically and
records exact current source hashes, checks pre-existing research/evidence
against the baseline snapshot, and runs both new checks. All new formal roots
must be covered, exit codes must be zero, and only propext, Classical.choice,
Quot.sound are allowed. The broader frozen Tier4 forbidden-syntax guard is also
applied to the additive Lean source. The 18 finite-prefix experiments use exact
rationals, cap80, no seed/sampling/optimization, and explicitly retain unresolved
tails. They are diagnostics, not an infinite-horizon numerical certificate.

[Baseline commands and logs](BASELINE.md) record the existing regression suite:
26 validation tests, all integrity/numerical/constant checks, and the benchmark
implementation replay. A missing numba import in the byte snapshot was resolved
by exposing the existing ignored runtime; the original failure is retained.
Published results were not overwritten. Full historical Lean replays are reused
only for unchanged sources; the new bridge receives a fresh local replay. No
independent external-machine or CI replay of this new checkpoint is available.

**Remaining limitation.** The universal arbitrary-law Psi upper bound and the
critical alpha=2 regime remain open. The constants here diverge as alpha tends
to2. Point masses, endpoints, and both two-atom cutoff regimes are analyzed in
[edge cases](EDGE_CASES.md), without claiming a uniform two-atom algorithm.
Symmetric screening was the strongest failed approach: it unnecessarily charged
rarity confidence on every negative coin. For the critical case, the next
precise task is a cutoff-dependent observable construction whose integrated
work does not introduce an extra log(B). No impossibility for all algorithms
has been established by the failed constructions.

The current report and append-only run log are updated in their original
locations. Imported baseline sources, old locks, and dependency pins remain
unchanged. The checkout and renamed origin were verified. Any checkpoint commit
is local only; no push, publication, remote change, or external contact occurred.
