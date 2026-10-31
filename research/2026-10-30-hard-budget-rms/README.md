# Hard-budget RMS integration

This focused change extracts the RMS component of the 30 October round-three
contribution. The confidence and optional-stopping component is deliberately
not included; it is integrated separately.

- [Full paper proof and dependency boundaries](NOTE.md)
- [Observation-budget driver](../../toolkit/threshold_toolkit/budget_ladders.py)
  and its [usage guide](../../toolkit/README.md#research-module-hard-observation-caps)
- [Regression tests](../../toolkit/tests/test_budget_ladders.py)
- [Exact finite recurrence and schedule audit](verify.py)
- [Claim scope in the results guide](../../docs/RESULTS.md#hard-observation-caps-for-the-rms-rates)

## Verification status

The new controller and theorem are not Lean-checked. The ordinary and critical
applications inherit formalized premises; the arbitrary-law rare-event
application depends on the paper-only entropy-tail theorem. The Python driver
cannot check the caller's statistical work, error or independence assumptions.
It preserves the most recent successful estimate on timeout and separately
reports reserved allowance and actual observations.

Local integration validation: 24 extracted unit tests pass; the exact verifier
checks 56 recurrence instances (26,232 enumerated independent paths), 224 base
work premises, 112 risk bounds and 10,301 schedules. These checks are finite
evidence, not a universal proof. Validation was run on a disposable additive
checkout, not a full network clone. No new Lean build was run.

GitHub CI then passed on the extraction commit `e552729`: the reproducible
checks (research-evidence, numerical-evidence and lean-kernel), the toolkit
suite on Python 3.10 and 3.12, and the then-separate fallback workflow on
Python 3.10 and 3.12. This records that commit only; later commits are
covered by their own CI runs.

The exact audit now runs as a research-evidence step of
[`checks.yml`](../../.github/workflows/checks.yml) on Python 3.12. The toolkit
workflow runs the extracted tests with the full toolkit suite on Python 3.10
and 3.12. No frozen file, historical manuscript, specification or evidence
record is modified. Replays write under `.runtime/hard-budget-rms/`.

## Reproduction

```sh
python -m unittest discover -s toolkit/tests -p 'test_budget_ladders.py' -v
python research/2026-10-30-hard-budget-rms/verify.py
```

## Priority review questions

Check independence of *complete* stage runs, persistent labels within a stage,
measurability in the original observable experiment, terminal-at-cap semantics,
small-budget normalization, and the distinction between deterministic authorized
budget and a data-selected stopping time. A scalar recursion proof alone does
not formally realize the statistical algorithm. The anytime guarantee is not
part of this PR.

## Provenance

Prepared by ChatGPT at David Iach's request. This is AI-generated research and
integration, not independent external specialist review. It is a scoped
extraction, so historical validation claims are not silently carried forward.
The baseline for integration is `2bc506d62387c511bac8fecbd07ec0e4026b10ce`.
Original round-three archive SHA-256: `1ffd571e2a5cd5ff10f681624cc00fbe535e7723ce65a1390d0b066563823e9f`.
The original archive and its PDF are **not committed to this repository**;
they were delivered to the project owner and are kept outside it. The hash identifies the source of
this extraction, but the extraction cannot be checked against it from the
repository alone. The files here are a scoped extraction and integration, not
byte-for-byte copies of the delivery.
