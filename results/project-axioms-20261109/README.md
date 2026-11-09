# Whole-project build, axiom audit and kernel replay

The per-result audits check hand-registered theorems and build only the
modules they name. This record is from the audit that registers nothing:
`python tools/verify_project_axioms.py --replay-main-theorem`.

At [commit `ed964bf`](https://github.com/davidiach/adaptive-threshold-estimation/commit/ed964bf),
on Linux with Lean `v4.36.0-rc1` and the Mathlib cache for the pinned
revision `9bdd0bc`:

| Check | Result |
|---|---|
| Build | All 1,129 modules under `lean/ThresholdHC` compile from source, including `Proofs/Tier2/ClassifierWorkBridge.lean`, which no result audit imports. No module reports a declaration that uses `sorry`. |
| Axioms | The modules declare 11,406 constants, 9,159 of them theorems. None is an axiom. Every one depends only on `propext`, `Classical.choice` and `Quot.sound`. |
| Kernel replay | The 204 project modules in the import closure of `Tier6/Full.lean` and `BlindUpper/Full.lean`, the two halves of the main RMS law, replay through the toolchain's `leanchecker`. |
| Implicit binders | Separately, every project file also type-checks with `-D autoImplicit=false`, so no statement quantifies over a misspelt name. This check is not part of the tool. |

The [report](report.log) is the tool's output. The audit says nothing about
what a statement means; the exact-type audits and the
[model-fidelity brief](../../docs/MODEL_FIDELITY.md) cover that.

Two scratch modules, not committed, confirmed that the audit fails closed.
A theorem closed with `by stop rfl` elaborates to `sorry`; the textual source
scanner accepts it, and this audit rejects it both at the build and in the
axiom report. A module that declares an axiom is rejected by name.

The replay covers the main theorem only. Replaying every module in one
checker process needed more than 12 GB of memory; one process per module
works and is what the tool does.
