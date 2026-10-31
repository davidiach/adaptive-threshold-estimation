# Certified entropy-tail computation: additive contribution

Prepared 30 October 2026 against `davidiach/adaptive-threshold-estimation` commit
`6ad675e04570cc1ef6bece8e26beb81e1a176471`.

## Results

The full research note is `research/2026-10-30-certified-selection/NOTE.pdf`
(and editable `NOTE.md`). It proves a quantile-to-selection factor of **8/5**,
replacing the pinned manuscript's `1 + 2 sqrt(2)`. It also proves a bandwise
suffix reduction for exact finite selection, total-variation stability, and
controlled band-preserving approximation. A rational six-atom certificate
rules out replacing 8/5 by sqrt(2).

These are **paper proofs and exact finite computations, not Lean proofs**.
The code evaluates a deterministic rate functional. It is not an estimator,
a statistical confidence interval, or a new statistical minimax theorem.
No claim of priority over the wider literature is made.

## Files and integration

Only new paths are supplied. Existing baseline, frozen specifications, published
research packages, and result records are not modified. No GitHub push or pull
request was made. `research/2026-10-30-certified-selection/INTEGRATION.md`
contains the integration and validation boundaries.

The main new files are:

- `toolkit/threshold_toolkit/rare_event_functional.py`: standard-library API.
- `toolkit/tests/test_rare_event_functional.py`: 29 unit tests.
- `research/2026-10-30-certified-selection/`: proofs, examples, evidence,
  reproduction scripts, and exact algebra checker.

The companion patch adds the text files. The PDF is supplied in this archive
and separately, rather than embedded as a binary addition in the patch.

## Run

Python 3.10 or newer is supported by the syntax used here; this delivery was
actually tested with Python 3.13. No third-party packages are needed for the
module, tests, exact algebra checker, or rational experiments.

From the archive/repository root:

```sh
python -m unittest discover -s toolkit/tests -p 'test_rare_event_functional.py' -v
python research/2026-10-30-certified-selection/verify_algebra.py
python research/2026-10-30-certified-selection/reproduce.py
```

The last two scripts overwrite **this contribution's own new evidence files**.
To preserve the delivered records byte for byte, reproduce in a disposable copy.
The optional floating-point stress search requires NumPy and is kept separate:

```sh
python research/2026-10-30-certified-selection/explore_float.py
```

To import the new API from the standalone archive:

```sh
PYTHONPATH=toolkit python - <<'PY'
from fractions import Fraction
from threshold_toolkit.rare_event_functional import (
    FiniteGapLaw, exhaustive_certificate, verify_certificate,
)
law = FiniteGapLaw([
    ('1/10000000000', '1/100000000'),
    ('1/4', '99999999/100000000'),
])
cert = exhaustive_certificate(law, rho='1/1000000', budget=10**12)
assert verify_certificate(cert, law, rho='1/1000000', budget=10**12)
print(cert['K_interval'])  # Exact rational endpoints.
print([float(Fraction(cert['K_interval'][key])) for key in ('lower', 'upper')])
PY
```

Float inputs are deliberately rejected. Use integers, exact decimal/rational
strings, or `fractions.Fraction`. Search caps fail explicitly rather than
returning a partial enumeration marked complete.

## Evidence and limitations

29 unit tests passed. Rational regressions checked 128 laws, 9,604 full subsets,
and 5,211 band-suffix candidates with no discrepancies. Four algebraic identities
were verified coefficientwise. A separate 20,000-law floating-point exploration
informed one rationally certified counterexample; it is not proof evidence.

No full upstream toolkit/Lean suite, upstream freeze check, or GitHub CI run was
performed. The container did not have Lean, and a full clone failed; selected
upstream sources were read via the GitHub connector. The certificate checker is
deterministic recomputation with the same implementation, not an independent
formal verifier. Input-law approximation premises must be established separately.

Code is Apache-2.0; the note and explanatory documentation are CC BY 4.0,
matching the source repository's stated split. No font files are distributed.
