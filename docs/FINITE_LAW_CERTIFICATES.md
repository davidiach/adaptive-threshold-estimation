# Finite-law measure and output certificates

This step of [#85](https://github.com/davidiach/adaptive-threshold-estimation/issues/85)
connects canonical finite rational laws to the original measure definitions and
checks actual `evaluate_selection` and `FiniteGapOracle` outputs. It extends the
[numerical checker](DETERMINISTIC_VERIFICATION.md); it does not close #85.

## Mathematical connection

For positive rational gaps `d_i <= 1/2` and nonnegative rational weights `w_i`,
the [atomic bridge](../lean/ThresholdHC/FiniteLawCertificates/Atomic.lean) defines
`mu = sum_i ofReal(w_i) * dirac(d_i)`. It proves the probability identity when
the weights sum to one, finite integration identities, restrictions, domination,
subtraction, the original dyadic band costs, tail cost and `gamma`.
The [rational data bridge](../lean/ThresholdHC/FiniteLawCertificates/Data.lean)
checks the half-open band convention directly by rational inequalities. The
supremum defining the original `gamma` equals the finite cost entropy on a
distinct list covering the occupied bands.

The [quantile bridge](../lean/ThresholdHC/FiniteLawCertificates/Quantile.lean)
identifies the original `quantileThreshold` and `quantileCore`. If `t` is the
first atom whose cumulative mass reaches `rho`, the removed fraction at that
atom is `(rho - mass_below_t) / mass_at_t`. The core keeps zero below `t`,
one minus this fraction at `t`, and all mass above it. This includes equality
at an exact cumulative-mass boundary.

For any fractions `0 <= s_i <= 1`, the selected measure is feasible. The
[objective bridge](../lean/ThresholdHC/FiniteLawCertificates/Objective.lean)
identifies its rational expression with

`min(rho, selectionObjective(mu, rho, B, sigma))`.

An accepted interval encloses this **capped feasible objective**. Its upper
endpoint also bounds the original `selection(mu,rho,B)` (the functional `K`).
Its lower endpoint is **not** a certified lower bound on `K`: no optimality or
menu-completeness claim follows from evaluating one selection.

## Actual oracle outputs

The [oracle bridge](../lean/ThresholdHC/FiniteLawCertificates/Oracles.lean)
connects the finite sums to integrals over the following original measures:

- `sigma = quantileCore(mu,rho)`;
- `tau = (mu-sigma)` restricted to `B*d^2 >= 1`;
- `zeta = (mu-sigma)` restricted to `B*d^2 < 1`.

The opt-in [adapter](../toolkit/threshold_toolkit/finite_law_certificates.py)
calls the unchanged legacy implementations, then asks Lean to check a closed
theorem about the caller's inputs and the supplied outputs:

| Operation | Checked conclusion |
|---|---|
| `objective` | Probability law, feasible selected measure, enclosure of its capped original objective, and upper bound on original `K` |
| `oracle` | Quantile threshold and fractional core identity; exact core band costs; exact `zeta` mass; exact integral of `d^-1` over `tau`; exact resolved error integral at the requested cap; upper bound on the tail-work integral |
| `prefix` | Enclosure of `integral (1/2-d)^heads (1/2+d)^tails dmu`, with width at most `2^-bits` |

The resolved-error integrand is `min(1, (M*d^2)^-2)` over `sigma+tau`.
The tail-work integrand is `min(M, 17*d^-2*(1+max(0,log(M*d^2))))` over `tau`.
The work result is an upper bound, checked through the proved logarithm
enclosures; the other listed oracle quantities are exact rational equalities.
An oracle certificate applies to its requested cap. It does not certify an
arbitrary callback or all future calls to the Python closure.

## Use and limits

```python
from fractions import Fraction as F
from pathlib import Path
from threshold_toolkit.finite_law_certificates import Request, produce, verify

request = Request(
    "objective",
    ((F(1, 8), F(1, 3)), (F(1, 2), F(2, 3))),
    selected=(F(1, 2), F(1, 4)),
    rho=F(1, 4), budget=F(256), bits=16, log_terms=4,
)
certificate = produce(request)  # untrusted actual legacy output
checked = verify(request, certificate, lean_dir=Path("lean"))
print(checked["output"])
```

Use `operation="oracle"` without `selected` to check the produced quantile
fractions and integrals at `cap`. Use `operation="prefix"` with `heads` and
`tails` for a null-prefix certificate. The required pinned build is:

```text
cd lean
lake build ThresholdHC.FiniteLawCertificates.Oracles
cd ..
python tools/verify_finite_law_certificates.py --no-build
python -m unittest discover -s tools -p test_finite_law_certificates_audit.py -v
```

The adapter accepts 1–16 distinct, increasing rational gaps with strictly
positive masses summing exactly to one. This is a canonical input contract;
it does not prove the legacy duplicate-merging parser. Zero-gap atoms are
outside this interface. `rho` lies in `(0,1/4]`, budget is positive, selected
fractions lie in `[0,1]`, caps are integers in `[1,10^9]`, and each prefix
count is an integer in `[0,128]`. The dyadic band index is at most 256.
Numerical precision is `16 <= bits <= 512`, `4 <= log_terms <= 256`.

Inputs have at most 2,048 numerator/denominator bits; generated rational values
at most 8,192 bits; source at most two million UTF-8 bytes. Proof reduction
has finite recursion/heartbeat limits. Kernel execution defaults to 180 seconds,
configurable up to 600. Invalid data, missing kernels, failed proofs and resource
exhaustion produce no verified result. There is no universal producer-completeness
or polynomial bit-complexity claim.

The expected request is separate from the supplied certificate. Exact recursive
types and every parameter are bound; unknown fields/band labels and raw-code
payloads are rejected. Output data are snapshotted before running Lean. Proofs
use `norm_num`, not `native_decide`. Acceptance requires the named closed theorem
and only the allowed transitive axioms `propext`, `Classical.choice`, `Quot.sound`.

## Evidence and remaining work

The [published verification record](../results/finite-law-certificates-20261117/README.md)
binds the audited sources to commit `8243b72bd4b22beea396bc3f0e8b2d2f92986b06`.
The focused audit restates ten exact types, audits all 52 declared roots, and
independently replays all five new modules. It checks actual output certificates
for empty/full/fractional selections, deterministic endpoint coins, fractional
and exact quantile boundaries, the resolution-threshold equality, and both
tail-work branches. Tampered objectives, prefixes, core fractions, band costs,
unresolved mass, inverse cost, error and work bounds must fail numerically in
Lean; a timeout is not negative-test evidence.

This is output certification, not a refinement proof of CPython. Input binding,
serialization and process execution, Python/Fraction, the pinned compiler and
kernel, the imported compiled cache and the operating system remain execution
boundaries. The source is available for independent inspection and rechecking;
replay of every external Mathlib module is not claimed.

The [envelope/transfer extension](ENVELOPE_TRANSFER_CERTIFICATES.md) now covers
zero-residual `GapEnvelope`, rounding and conditional transfer outputs. Remaining
#85 work includes global menu/DP/approximation certificates, concrete
planner prices/allocations/schedules, and floating calculators. Arbitrary
external-oracle promises remain assumptions. Statistical observation models and
Python/PRNG execution remain separate in #86. The mathematical core and its
published statistical theorems are unchanged.
