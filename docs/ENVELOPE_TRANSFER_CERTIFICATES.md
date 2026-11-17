# Envelope, rounding and transfer output certificates

This #85 milestone extends the [finite-law certificates](FINITE_LAW_CERTIFICATES.md)
to the unchanged `GapEnvelope`, `round_up_within_bands` and `transfer_enclosure`
implementations. The [adapter](../toolkit/threshold_toolkit/envelope_transfer_certificates.py)
emits a closed theorem about the actual output. Only `verify` accepts that output,
after Lean checks the proof and its transitive axioms.

## Residual mass at zero

For CDF bounds `c[0]=1 >= ... >= c[n] >= 0`, the envelope has mass `c[n]`
at zero and mass `c[j]-c[j+1]` at `2^(-j-2)`. Each certificate identifies
the returned atoms and zero mass with the original Lean `envelopeLaw` and
proves that it is a probability measure. Equal adjacent bounds and an empty
positive support are allowed. The null-prefix interval encloses the exact
mixture integral, including the fair-prefix contribution at zero; its width
is at most `2^(-bits)`.

Domination of an actual population remains conditional on nonnegative support
and valid CDF bounds at the probed grid points. Constructor validation alone
does not establish those statistical premises.

When `z < rho`, the certificate checks the returned positive law normalized
by `1-z`, conditional rarity `(rho-z)/(1-z)`, original fractional quantile
threshold/core, and its scaling back to the unnormalized positive measure.
It checks every occupied band's cost, zero mass plus unresolved positive mass,
the inverse-gap tail integral, resolved-error integral and tail-work upper bound
at the requested cap. The finite output proof includes the logarithm evidence
used for work. It does not certify every future callback invocation at once.

When `rho <= z`, the output is explicitly tagged `fallback`. Lean proves the
original `zeroSelection` value equals `rho`, and checks the returned unresolved
mass and placeholder zeros. Those callback zeros are **not** claimed to be the
actual error/work integrals. No positive conditional law is invented when all
mass is at zero. The null-prefix mixture identity is not a proof of physical
zero-gap coin execution.

## Rounding and conditional transfer

A rounding certificate constructs a measurable transport equal to the returned
destination map on every input atom and to the identity elsewhere. It proves
upward rounding, preservation of every dyadic band, and distortion by the
returned factor `r`. It checks that factor against the largest actual ratio and
`r <= 1+1/subdivisions`. Duplicate destinations are grouped by summing their
source weights, so the pushforward equals the returned probability law.
The existing theorem then gives `K(rounded) <= K(input) <= r*K(rounded)`.

This checks the output's mathematical rounding contract. It does not prove
that all Python executions implement the ceiling-grid algorithm or terminate
within a stated bit complexity.

A transfer certificate checks the returned endpoints exactly:

`L' = max(0,L-eta)`, `U' = min(rho,r*U+eta)`.

Its theorem is conditional: if `mu` and `mu0` are probability laws,
`tvDist(mu,mu0)/2 <= eta`, the measurable map preserves bands and has upward
distortion at most `r`, and `[L,U]` encloses original `K(mu0.map T)`, then
`[L',U']` encloses original `K(mu)`. The total-variation convention and division
by two are explicit. The result reports `transfer_premises_verified=False`.
A feasible-objective interval from the previous milestone supplies an upper
bound on `K`; it cannot supply this two-sided input premise by itself.

## Use and limits

```python
from fractions import Fraction as F
from pathlib import Path
from threshold_toolkit.envelope_transfer_certificates import (
    EnvelopeRequest, RoundingRequest, TransferRequest, produce, verify,
)

request = EnvelopeRequest((F(1), F(1, 2), F(1, 8)), heads=2, tails=3)
certificate = produce(request)
result = verify(request, certificate, lean_dir=Path("lean"))
```

Use `RoundingRequest(atoms, subdivisions=16)` for canonical increasing positive
atoms and `TransferRequest(lower, upper, rounding_factor, tv_radius)` for
conditional transfer. All requests bind `rho` and budget explicitly.

Envelope inputs contain 1–17 decreasing exact bounds; rounding inputs contain
1–16 distinct positive atoms with positive weights summing to one. Rarity lies
in `(0,1/4]`, budget is positive, subdivisions in `[1,10^6]`, TV radius in `[0,1]`,
caps in `[1,10^9]`, and prefix counts in `[0,128]`. Precision is
`16 <= bits <= 512`, `4 <= log_terms <= 256`. Inputs are exact integers,
Fractions or integer/fraction strings, with 2,048-bit numerator/denominator
limits; floats and booleans are rejected. Generated rationals have at most
8,192 bits and source at most two million UTF-8 bytes. Lean has finite reduction
limits; execution defaults to 240 seconds, configurable up to 600.

Unknown fields, request substitutions, malformed outputs, failed proofs,
unavailable Lean and exhausted limits produce no verified result. Output data
are snapshotted before execution. Proofs use kernel-checked `norm_num`, with
only `propext`, `Classical.choice` and `Quot.sound` allowed. The current pinned
project build is required; an arbitrary same-named project is not a trust root.
The adapter's input/output binding, Python/Fraction, serialization/processes,
the pinned compiler/kernel, imported compiled cache and OS remain trusted.
There is no CPython refinement, universal producer-completeness or polynomial
bit-complexity claim.

## Reproduction and remaining work

```text
cd lean
lake build ThresholdHC.EnvelopeTransferCertificates.Transfer
cd ..
python tools/verify_envelope_transfer_certificates.py --no-build
python -m unittest discover -s tools -p test_envelope_transfer_certificates_audit.py -v
```

The focused audit restates twelve exact types, checks all declaration roots,
independently replays all three new modules and checks actual-output proofs
plus deliberately false numerical claims. A rejected numerical case must
reduce to `False`; a timeout or missing dependency is not rejection evidence.
Its source snapshot and compiler/artifact hashes are recorded in a fresh
`.runtime/envelope-transfer-certificates/` directory. See the
[published record](../results/envelope-transfer-certificates-20261117/README.md).
CI retains both this output and the earlier finite-law output in the
`lean-verification` artifact.

#85 remains open for global menu/DP/approximation outputs, concrete planner
prices and allocations, schedules and floating calculators. Arbitrary external
oracle promises and the statistical CDF/transfer premises remain assumptions.
Observation models and Python/PRNG execution remain separate in #86.
