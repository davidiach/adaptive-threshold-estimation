# Whole-project audit with instances and the definition lock

The [whole-project audit](../project-axioms-20261109/README.md) checks that
every module compiles and that every constant depends only on `propext`,
`Classical.choice` and `Quot.sound`. A review of `b471d6b` found two ways a
restated statement could change meaning with every check still passing:

- an instance declared in an audited module, such as a high-priority or
  scoped `LE ℝ`, is used when the audit imports the module and opens its
  namespace, so a restated `≤` can elaborate to a different relation;
- the restated statements refer to project definitions that no lock or audit
  pins, so a definition could change while its proofs were adjusted.

`python tools/verify_project_axioms.py` now also checks, in the same
environment:

| Check | Rule |
|---|---|
| Instances | Every instance a project module exports, scoped ones included, is a named project constant, in the global scope, at the default priority. No data-carrying instance on a type the project does not define is new: the six registered ones put the discrete σ-algebra on `Option` and `List` types, as the models require. |
| Definitions | Every project definition and inductive type reachable from a definition that is not part of a proof has a fingerprint, the hash of its printed type and value with every proof replaced by `True.intro`, equal to its entry in [definition_lock.json](../../tools/definition_lock.json). A changed or removed entry fails. A new definition fails until `--add-definitions` adds it; that option never rewrites an existing entry. |

A proof can change without changing any fingerprint. The lock pins what each
definition is, not what it means; the exact-type audits and the
[model-fidelity brief](../../docs/MODEL_FIDELITY.md) cover meaning.

At [commit `b4a88c4`](https://github.com/davidiach/adaptive-threshold-estimation/commit/b4a88c43a7ad7f4b68dfeb78f69d205102e7e359),
on Linux with Lean `v4.36.0-rc1` and the Mathlib cache for the pinned revision:

| Check | Result |
|---|---|
| Build | All 1,190 modules under `lean/ThresholdHC` and the root compile from source. No module reports a declaration that uses `sorry`. |
| Axioms | The modules declare 12,625 constants, 10,196 of them theorems. None is an axiom. Every one depends only on `propext`, `Classical.choice` and `Quot.sound`. |
| Instances | 123 exported instances: 84 of propositional classes, 33 data-carrying instances on project types and the 6 registered data-carrying instances on other types. None is scoped; all have the default priority and are project constants. |
| Definitions | All 2,318 fingerprints match the lock; none changed, was removed or is new. |
| Kernel replay | The 204 project modules in the import closure of `Tier6/Full.lean` and `BlindUpper/Full.lean`, the two halves of the main RMS law, replay through the toolchain's `leanchecker`. |

The [report](report.log) is the tool's output, with the per-definition
fingerprint lines omitted; they are the lock itself.

Five scratch changes to a throwaway module, not committed, confirmed the checks: a
new definition that is not in the lock, a definition whose constant changes
from 17 to 170, a scoped `LE ℝ` instance at high priority and a plain global
`LE ℝ` instance are each rejected; a change to a proof inside a definition
leaves its fingerprint unchanged.
