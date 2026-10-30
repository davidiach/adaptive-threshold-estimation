# Certified selection: a sharper quantile comparison and exact evaluation of K

Status: **paper proofs and exact finite computations, not Lean-checked or
externally specialist-reviewed.** An external contribution delivered on
30 October 2026 against `6ad675e`, integrated with the changes recorded below.

The package concerns the deterministic selection functional $\mathcal K$ and
the closed quantile functional $Q$ of the
[consolidated v6 manuscript](../../paper/v6/README.md), §§13–14. Its proofs do
not assume the statistical characterization $R\asymp\mathcal K$. Interpreting
the values as minimax rates still rests on that separate paper theorem.

## Results

| Result | Where | Status |
|---|---|---|
| $\mathcal K\le Q\le\frac85\mathcal K$ for every law on $(0,1/2]$, replacing $1+2\sqrt2$ | [NOTE.md](NOTE.md) Theorem 4 | Paper proof; four polynomial identities in Lemma 3 checked exactly |
| Finite laws: some optimal hard selection is an upper-gap suffix in every dyadic band, so $\prod_j(n_j+1)$ candidates suffice | Theorem 5 | Paper proof |
| The best of the $n+1$ global upper-gap cuts satisfies $\mathcal K\le V\le Q$; it is not exact in general | Corollary 6 | Paper proof; exact counterexample to exactness |
| $\lvert\mathcal K_\mu-\mathcal K_{\tilde\mu}\rvert\le d_{\rm TV}(\mu,\tilde\mu)$, sharp as $h\to0$ | Theorem 7 | Paper proof |
| Band-preserving upward rounding by at most $r$: $\mathcal K_{T_\#\mu}\le\mathcal K_\mu\le r\mathcal K_{T_\#\mu}$ | Theorem 8 | Paper proof; exact counterexample once bands are crossed |
| Finite-law enclosures transfer to every law | Corollary 9 | Paper proof; the approximation premises must be supplied separately |
| The best constant $c^*=\sup Q/\mathcal K$ satisfies $1.4604<c^*\le8/5$ | §6 and [integration review](integration-review/REVIEW.md) | Exact rational certificates: 1.42132 in the delivery, 1.4604 at integration |

Composed with the v6 corollaries, the new constant gives two further
paper-level consequences:

- the general-law quantile form $\frac58\cdot10^{-17}Q\le R\le33000\,Q$, in place
  of $10^{-17}/(1+2\sqrt2)$. This rests on the general-law theorem.
- the finite-law selection form $R\le30001\cdot\frac85\mathcal K<4.81\cdot10^4\mathcal K$,
  in place of $1.2\cdot10^5$.

The published manuscripts are unchanged and still state $1+2\sqrt2$.

The module `toolkit/threshold_toolkit/rare_event_functional.py` evaluates
$\mathcal K$ and $Q$ for finite rational laws with exact rational enclosures,
using only the standard library. Its methods are:

- `exhaustive_certificate`: complete bandwise-suffix enumeration with an explicit state cap.
- `quantile_certificate`: the inexpensive bound $\frac58Q\le\mathcal K\le Q$.
- `threshold_certificate`: the global-cut upper bound.

It evaluates the rate functional only. It is not an estimator or a statistical
confidence interval. Floats are rejected as inputs, and searches past the cap
fail instead of returning a partial certificate.

## Files

- [NOTE.md](NOTE.md) and [NOTE.pdf](NOTE.pdf): the proofs, examples and trust
  boundary. [build_pdf.sh](build_pdf.sh) generates `NOTE.tex` and the PDF
  from `NOTE.md`.
- [evidence/](evidence): certificates for the examples, the √2 counterexample,
  the regression summary, the exact algebra record and the float exploration.
- [integration-review/](integration-review/REVIEW.md): the integration review,
  the 1.4604 certificate, and a separately written high-precision cross-check.
- Delivery records, unchanged: [CONTRIBUTION_README.md](CONTRIBUTION_README.md),
  [INTEGRATION.md](INTEGRATION.md), [PROVENANCE.json](PROVENANCE.json),
  [DELIVERY_MANIFEST.sha256](DELIVERY_MANIFEST.sha256),
  [evidence/unit_tests.log](evidence/unit_tests.log) and
  [evidence/float_exploration.json](evidence/float_exploration.json).

## Replay

From the repository root:

```sh
python -m unittest discover -s toolkit/tests -p 'test_rare_event_functional.py' -v
python research/2026-10-30-certified-selection/verify_algebra.py
python research/2026-10-30-certified-selection/reproduce.py
python research/2026-10-30-certified-selection/integration-review/certify_obstruction.py
python research/2026-10-30-certified-selection/integration-review/independent_check.py
```

The four scripts write into a new directory under `.runtime/certified-selection/`.
They compare every record with the tracked file byte for byte and exit nonzero
on any difference; tracked evidence is never modified. `--write-evidence`
rewrites the tracked files and is for deliberate regeneration only.

The tests, `verify_algebra.py`, `reproduce.py` and `certify_obstruction.py` need
only the standard library. `independent_check.py` needs mpmath.
`explore_float.py` and `integration-review/adversarial_search.py` are float
explorations that need numpy and scipy. They write only to `.runtime/` and have
no certificate status.

## Integration record

**Delivery.** The archive was `adaptive_threshold_improvements_2026-10-30.zip`,
with SHA-256 `69b35877a6596d9cc56c9dbfe256b2cc7ce993c6713c80a0f66427d73c915efd`.
Commit `5cab645` adds its contents byte for byte. The one layout change moves
the archive-root `CONTRIBUTION_README.md` into this directory. To verify the
delivered bytes:

```sh
git archive 5cab645 research/2026-10-30-certified-selection toolkit/threshold_toolkit/rare_event_functional.py toolkit/tests/test_rare_event_functional.py | (D=$(mktemp -d) && tar -x -C "$D" && cd "$D" && mv research/2026-10-30-certified-selection/CONTRIBUTION_README.md . && sha256sum -c research/2026-10-30-certified-selection/DELIVERY_MANIFEST.sha256)
```

**Changes at integration.**

- Certificate schema `ate-rare-functional-v2` drops the `base_commit` field. In
  v1 it named `6ad675e` even for certificates made by later code.
  `verify_certificate` rejects v1 certificates.
- `sqrt_interval` now has width at most $2^{-\text{bits}}\min\{1,\sqrt x\}$.
  The absolute width $2^{-\text{bits}}$ made small values of $\mathcal K$ vacuous;
  at $B=10^{50}$ the enclosure was $[0,8.3\cdot10^{-25}]$. The soundness
  argument is unchanged.
- The replay scripts now write to `.runtime/` and compare with the tracked
  evidence. `summary.json` no longer records wall-clock time.
- The eight certificate-bearing evidence files were regenerated. Witnesses,
  state counts and decimal displays are unchanged; only interval widths shrank.
- Three regression tests were added, for 32 in total. Each fails on the
  delivered module.
- [integration-review/](integration-review/REVIEW.md) was added.

Some delivery records now describe superseded details: the overwriting
replays, the patch without the PDF, the fixed square-root grid, the 29-test
count, and $1.42132$ as the strongest obstruction. They are kept as records of
the delivery.

## Limitations

- Nothing here is Lean-checked; the v6 comparison with $1+2\sqrt2$ is not
  formalized either. In order, the natural targets are the scalar Lemma 3,
  Lemmas 1–2, Theorem 4, the finite suffix reduction, and Theorems 7–8.
- The proofs were checked by the contributing session and by the integration
  review, both AI. There is no specialist review, consistent with the
  [project's stated preference](../../docs/WORKPLAN.md#current-priorities).
- Certificates rely on the unverified Python implementation, and
  `verify_certificate` recomputes with the same code. The independent check uses
  high-precision floating point, not interval arithmetic.
- Exact evaluation remains exponential in the number of occupied bands. The
  sharp constant $c^*$ is open in $(1.4604,8/5]$.
- Stability of $\mathcal K$ in the law says nothing about estimating the law or
  reusing an estimator designed for another law.

Code is Apache-2.0; the note and documentation are CC BY 4.0.
