# Integration review of the certified-selection package

Reviewed 30 October 2026 in the AI session that integrated the package. This
reviewer did not write the delivered proofs or code. The review checked the
delivered archive against the repository at `6ad675e`; the integration fixes
are listed in the [package README](../README.md#integration-record). Like the
package itself, this review is AI work and not an external specialist review.

## Result: the √2 obstruction improves to 1.4604

Write $c^*=\sup Q/\mathcal K$ over all laws, rarities and budgets. The package
proves $c^*\le8/5$ and certifies $c^*>1.42132$ with a rational six-atom law.
An adversarial search found a rational eight-atom law with

$$Q/\mathcal K>1.4604,$$

so $1.4604<c^*\le8/5$.

[certify_obstruction.py](certify_obstruction.py) certifies this with the
package's exact rational interval arithmetic. It compares a rigorous upper bound
on the objective of the feasible selection `[1,1,0,0,0,1,1,1]` (an upper bound
on $\mathcal K$) with a rigorous lower bound on $Q$. This needs neither the
bandwise-suffix theorem nor the 8/5 theorem. The record is
[evidence/obstruction_1_4604.json](evidence/obstruction_1_4604.json), and the law
is in [obstruction_law.json](obstruction_law.json). The supporting exhaustive
certificate (144 bandwise-suffix states) confirms the witness as the best hard
selection, with $\mathcal K\approx3.19173\cdot10^{-4}$ and $Q/\mathcal K\approx1.460450$.

The law has two atoms just below $2^{-10}$, in band 9, and two just above it,
in band 8. The optimum selects the band-9 atoms and leaves the band-8 atoms in
the remainder. The quantile core must keep both, paying entropy for an extra
band. This is the same band-split effect as the package's cross-boundary
rounding example. The package's 20,000 random laws rarely put atoms on both
sides of a boundary, which explains why its float search stopped at 1.42132.

[adversarial_search.py](adversarial_search.py) records how the law was found:
Nelder–Mead from 120 random starts, `python adversarial_search.py 8 7 120`. It
reproduced the identical rounded law with the pinned numpy 2.4.4 and scipy
1.17.1, and also with numpy 2.5.4 and scipy 1.18.1. The same search with
three and six atoms reached about 1.4406 and 1.4599. A four-atom run
moved to gaps near $10^{-160}$, where float64 overflows, and its reported ratio
was discarded. These float runs are exploration only.

**Scale observation.** If every gap exceeds $h$ and neither $\mathcal K$ nor $Q$
is capped at $\rho$, both are $h$ times a quantity independent of $B$. Indeed
$\min\{1,h/d\}=h/d$ on the whole support, so every selection objective is
$h[\sqrt{\rho\Gamma_\sigma}+\int d^{-1}(\mu-\sigma)(dd)]$. In this regime $Q/\mathcal K$
depends only on the law and $\rho$. That explains why the searches drive $h$
below the smallest gap.

## Mathematics checked

The definitions in [NOTE.md](../NOTE.md) were compared with
`paper/v6/finite-comparison.tex` and `paper/v6/entropy-tail-statement.tex`: the
canonical bands, $\mathcal G$, the prefix-supremum $\Gamma$, $\mathcal K$, and the
quantile split agree. Each proof was read line by line:

- **Lemma 1.** The binary-entropy expansion and the bound
  $H_2(p)\le2\log2\sqrt{p(1-p)}$ were re-derived. The derivative of
  $H_2/\sqrt{p(1-p)}$ has the sign of $g(p)=(1-p)\log(1-p)-p\log p$, which is
  concave with zero endpoints on $[0,1/2]$.
- **Lemma 2.** The weights $e^{1-2m_r}$ have total below $0.79$, and
  $d/t\ge m_r$ holds in every offset band. The old factor four lost a factor
  two in the band containing $t$, where the old proof used $d^{-1}\le2/t$
  although $d\ge t$.
- **Lemma 3.** All four polynomial identities were re-derived by hand, including
  the Young step with weights $3/2$ and $2/3$. The cubic bound for $w\ge-3/4$
  holds as stated.
- **Theorem 4.** Each inequality holds. The improvement comes from paying the
  selected tail and core costs separately and combining them only through
  $u^2+v^2\le x^2$. The old proof spends the full selected entropy on both.
- **Theorem 5, Corollary 6.** The ratio $d^2\min\{1,h/d\}$ is strictly
  increasing. The single-band entropy has second derivative
  $1/(A_0+z)-1/z\le0$, so the suffix replacement and the endpoint rounding of
  the quantile's boundary atom are valid. The global-cut counterexample
  reproduces.
- **Theorems 7–8, Corollary 9.** The common-part construction, the lifting
  $\sigma=(f\circ T)\mu$, and the bound $\min\{1,h/(rd)\}\ge r^{-1}\min\{1,h/d\}$
  are correct. The unit total-variation constant is sharp as $h\to0$, as stated.

No error was found. This reading is not a formal verification.

## Independent numerical cross-check

[independent_check.py](independent_check.py) was written from the paper
definitions and does not import the package module. It computes $\mathcal K$ over
all $2^n$ hard subsets, relying on the repository's hard-selection lemma rather
than the package's suffix theorem, in 50-digit mpmath arithmetic. Its record is
[evidence/independent_check.json](evidence/independent_check.json).

| Case | Certified or reported value | Independent value |
|---|---|---|
| √2 counterexample, $Q/\mathcal K$ | $>1.42132$ | $1.42132016705367$ |
| 1.4604 obstruction, $Q/\mathcal K$ | $>1.4604$ | $1.46044971656899$ |
| Global-cut example, $\mathcal K$ / best cut | $2.0001000\cdot10^{-4}$ / $2.0002149\cdot10^{-4}$ | same to 15 digits |
| Cross-boundary rounding ratio | about 1.3064 | $1.30643373950051$ |

A sweep of 1,000 random laws, seed 20261030, found no violation of
$\mathcal K\le V\le Q\le\frac85\mathcal K$ within a $10^{-20}$ relative tolerance.
Its largest $Q/\mathcal K$ was 1.41390. mpmath is high-precision floating point,
not interval arithmetic, so this is a cross-check, not a certificate.

## Code review

The interval arithmetic in `rare_event_functional.py` was checked for
soundness: the integer square-root enclosure, the atanh logarithm series and
its geometric remainder, the binary reduction, `_floor_log2`, the band index at
exact dyadic endpoints, the quantile split, the per-band suffix options, the
global-cut scan, the transfer bound and the rounding helper. No unsound bound
was found. Two problems were fixed at integration:

- Square roots had absolute width $2^{-\text{bits}}$, so small values of
  $\mathcal K$ lost all precision. At $B=10^{50}$ a two-atom enclosure was
  $[0,8.3\cdot10^{-25}]$. The grid is now refined below 1.
- Each certificate carried `base_commit = 6ad675e`, including certificates made
  by later code. Schema v2 removes the field.

`verify_certificate` replays the same implementation, as the package states;
it is not an independent checker.

## Checks run at integration

- **Delivery:** every manifest entry verifies at the delivery commit `5cab645`,
  with the one documented path mapping.
- **Patch and repository:** the companion patch applies to `6ad675e`, and
  `python tools/freeze.py --verify` passes.
- **Delivered code:** the full toolkit suite passed, 93 tests, with numpy and
  scipy installed. The package itself had not run the 64 existing tests.
- **Replays:** `verify_algebra.py` and `reproduce.py` reproduced every
  delivered record byte for byte, apart from the wall-clock field since removed
  from `summary.json`.

The [package README](../README.md#replay) gives the current commands. Results
for the integration commit are reported in its pull request. The PDF was not
rebuilt, and its text was not compared line by line with `NOTE.md`.
