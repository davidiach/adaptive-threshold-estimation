# The dominance step of the two-flip feedback advantage: library audit

The nonlinear-population package proves a strict acquisition-feedback
advantage at the two-point gap law $(\delta_{1/4}+\delta_{1/8})/2$ with rarity
$1/4$ and a total cap of two flips
([`feedback.tex`](../../research/2026-10-27-nonlinear-population/lower/feedback.tex),
section `sec:feedback-counterexample`, and Theorem `feedback:full-class` of
[`full_class-body.tex`](../../research/2026-10-27-nonlinear-population/lower/full_class-body.tex)).
Its comparison class is the preselected, independently executed local
designs, and a dominance paragraph reduces that class to two schedules. Lean
checked the bounds against the seed-conditional normal form of the class, not
the dominance reduction
([record](../two-flip-feedback-20261121/README.md)). Lean now checks a
dominance step and states the bounds for a local class itself, in
[`lean/ThresholdHC/TwoFlipDominance`](../../lean/ThresholdHC/TwoFlipDominance/Full.lean).
The package is unchanged. The audit runs below were made at commit
[`371a0c0`](https://github.com/davidiach/adaptive-threshold-estimation/commit/371a0c0).

## Statements

[`Specification.lean`](../../lean/ThresholdHC/TwoFlipDominance/Specification.lean)
defines the class and the minimax of the comparison.

- `ownBits pol c xs` lists the answers of coin $c$ in the history $xs$.
- `LocalAcquisition A`: at every seed there are continuation rules, one per
  coin and reading only that coin's own answers, such that at every finite
  history the policy stops exactly when every rule says stop and flips only a
  coin whose rule asks for a flip. The order among active coins is free.
- `AlmostSureCap A 2`: at most two flips almost surely in the original
  experiment at every sign law of mean at most $1/4$.
- `localMinimax`: the infimum of the worst rare mean squared error over the
  local designs with the almost-sure cap of two.

| Target | Statement |
|---|---|
| `dominance_pathwise` | A local design with a pathwise cap of two is in the seed-conditional normal form `NoninteractiveCapTwo`. |
| `dominance_seed` | For a local design with the almost-sure cap of two, almost every seed stops after two flips and is in the normal form at that seed. |
| `local_class` | The pathwise cap implies the almost-sure cap; the same-coin and fresh-coin schedules are local designs with the pathwise cap; `localMinimax` $\le1/64$. |
| `local_uniform_lower_bound` | Every local design with the almost-sure cap of two has worst MSE at least $1547585/10^8$. |
| `local_lower` | $15475/10^6<$ `localMinimax` $\le1/64$. |
| `local_separation` | The pinned feedback witness obeys both caps, is not a local design, and has worst MSE more than $32/10^6$ below `localMinimax`. |

How the class differs from the paper's:
- The paper's independently executed policies become per-coin rules inside one
  sequential policy. The order among active coins is unrestricted, so
  block-sequential and interleaved runs are both members.
- The condition is imposed at every finite history, reachable or not. A design
  that meets it only on reachable histories is covered once it is redefined on
  the unreachable ones, which does not change its law; that step is not
  formalized.
- The rules may depend on the whole seed and need not be measurable in it, and
  the number of local policies is not bounded.
- The paper's dominating mixture of two schedules and its completion of early
  stops are replaced by the direct six-shape Bayes bound of the two-flip
  feedback group, applied seed by seed. No modified estimator is built on the
  null set of bad seeds.

Theorem `feedback:strict`, the two-point class with its own constants, and any
comparison of expected-budget procedures are not covered.

## How the proofs go

- [`LocalForm.lean`](../../lean/ThresholdHC/TwoFlipDominance/LocalForm.lean):
  at one seed, a policy that meets the class condition and stops after two
  flips is in the normal form, by a case analysis on whether a second coin's
  rule is active before any flip.
- [`PathwiseDepth.lean`](../../lean/ThresholdHC/TwoFlipDominance/PathwiseDepth.lean):
  every two-answer prefix occurs on a valid path, so the pathwise cap stops
  every seed after two flips.
- [`Kernel.lean`](../../lean/ThresholdHC/TwoFlipDominance/Kernel.lean) and
  [`AlmostSureDepth.lean`](../../lean/ThresholdHC/TwoFlipDominance/AlmostSureDepth.lean):
  under the null sign law every two-answer word has positive probability, so
  the almost-sure cap makes the seeds that would request a third flip a null
  set.
- [`AlmostSureLower.lean`](../../lean/ThresholdHC/TwoFlipDominance/AlmostSureLower.lean):
  the Bayes bound of the two-flip feedback group applies on the almost-sure
  normal-form set.
- [`Members.lean`](../../lean/ThresholdHC/TwoFlipDominance/Members.lean): explicit
  continuation rules for the same-coin, fresh-coin and constant estimators;
  the feedback witness is not local, since by the pathwise dominance it would
  otherwise be in the normal form, which it is not.

## Runs

| Command | Outcome | Log |
|---|---|---|
| `python tools/verify_two_flip_dominance.py --replay --jobs 2` | 9 exact statements (the 6 targets and 3 components) and 46 transitive axiom reports over the 8 registered modules, all within `propext`, `Classical.choice` and `Quot.sound`. All 8 modules replayed through the independent kernel checker. | [two-flip-dominance-audit.log](two-flip-dominance-audit.log) |
| `python -m unittest discover -s tools -p 'test_two_flip_dominance.py'` | 11 guard tests pass. | |
| `python tools/verify_project_axioms.py` | 21,687 constants (17,591 theorems) in 1,769 modules, same axioms. 160 exported instances, unchanged; 6 registered orphans, unchanged. 3,938 locked definition fingerprints. | [project-audit.log](project-audit.log) |
| `python tools/verify_lean_sources.py` | 1,770 Lean sources, no proof escapes. | |

The whole-project audit was first run with `--add-definitions`. It added 15
entries to `tools/definition_lock.json`: the six statements, the four class
definitions above, the one-seed predicates `LocalAt`, `NormalAt` and
`StopsAtTwo`, the set of seeds that would request a third flip, and one
private loss used in the lower bound. No existing entry changed. The run
recorded here is a later one without that flag.

## Scope

These audits check that the stated types are proved and which axioms the
proofs use. The specification was written before the proofs, reviewed, and
pinned by hash from this audit onward.

## Review

The item was planned by one agent and criticized by a second, which replaced
the planned block-sequential class by the order-free class above, so that no
execution order has to be modelled, and required the almost-sure cap in the
separation. A third agent wrote the proofs. Before the specification was
pinned, a fourth agent that had not written them:
- rebuilt the modules and printed the axioms of all 46 public declarations;
- restated the targets with their types written out;
- compiled a probe showing that an interleaved schedule meets the class condition, and checked that no per-coin rule can make the witness's second coin active after a tail and inactive after a head.

It found no defect in the Lean. Its two minor points concerned the location of
the implementer's report and a module docstring that claimed a probability
floor of $25/256$ where the lemma states only positivity; the docstring was
corrected before the pin. These were reviews by AI agents, not a specialist
referee report.

[SHA256SUMS](SHA256SUMS) identifies the files of this record.
