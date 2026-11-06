# Entropy perturbation and state-compression audit

Native Lean audit passed on 6 November 2026 for the additive sources on
`research/selection-fptas-20261106`, based on
`68adbf340ec04ddbeae4cab3076066d832076afc`. This records an uncommitted local
checkpoint identified by exact source hashes, not a CI result.

Both requested targets were checked against the unchanged
[advance model](../../lean/ThresholdHC/SelectionApproximation/Model.lean) and
[specification lock](../../lean/ThresholdHC/SelectionApproximation/SPECIFICATION.json):

* `entropy_perturbation`: the existing cost entropy changes by at most
  `(2*L*eta + delta*(1+eta))*A` under the certified summary hypotheses.
* `compression_invariant`: every feasible trace has a retained feasible witness
  with no worse saving and both summaries within factor `c^m`, for certified bins.

The [proof guide](../../lean/ThresholdHC/SelectionApproximation/README.md)
gives the assumptions, zero-case handling, relative entropy consequence and
bin-cell geometry. The full FPTAS, bit complexity, concrete bucket-index
implementation and Python execution remain outside the checked scope.

## Evidence

* [status.json](status.json): successful result, source and object hashes,
  compiler identity, package revisions, exact targets and all axiom reports.
* [Audit.lean](Audit.lean): the exact compiler input for the two target checks,
  two concrete bin checks, and every new declaration's transitive axioms.
* [007.log](007.log): the complete 27-declaration axiom report.
* `001.log` through `006.log`: empty successful build logs; every local module
  was rebuilt from source in this run, with no local project object reuse.
* [SHA256SUMS](SHA256SUMS): hashes of this published record, including this guide.

All seven compiler invocations exited zero without warnings. The 27 new
declarations use only `propext`, `Classical.choice` and `Quot.sound`.
The six local modules comprise three inherited dependencies, the locked model,
and the two proof modules. The compiler is Lean 4.36.0-rc1; Mathlib is pinned at
`9bdd0bc71aaae0fd83889f9aacd70c32fccd1bcd`. External package checkouts were clean
at their pinned revisions; their compiled caches and the Lean distribution
remain trusted inputs. This is not a rebuild of Mathlib.

The six verifier regression tests passed, including rejection of changed locked
definitions, proof escapes, missing or duplicate reports and disallowed axioms.
The project source guard checked 1,150 Lean files without proof escapes, and
the original `FROZEN.sha256` check passed. No independent agent or specialist
review is claimed.

## Reproduce

With the repository's [pinned environment](../../docs/VERIFY.md#setup), run:

```sh
python tools/verify_selection_approximation.py
python -m unittest discover -s tools -p 'test_selection_approximation.py' -v
python tools/verify_lean_sources.py
python tools/freeze.py --verify
```

For an existing installation, pass `--lean-exe PATH_TO_LEAN` and
`--package-cache PATH_TO_PACKAGES`. The actual commands and native paths for
this checkpoint are in `status.json`. Each rerun creates fresh evidence under
`.runtime/selection-lean/`; it does not overwrite this record.
