# The strict acquisition-feedback advantage at two flips: library audit

Theorem `feedback:full-class` of the nonlinear-population lower note
([`research/2026-10-27-nonlinear-population/lower/full_class-body.tex`](../../research/2026-10-27-nonlinear-population/lower/full_class-body.tex),
with the comparison class and its dominance argument in
[`lower/feedback.tex`](../../research/2026-10-27-nonlinear-population/lower/feedback.tex)
and the exact coefficients in `lower/full_class_certificate.json`) compares
policies at the gap law $\mu=(\delta_{1/4}+\delta_{1/8})/2$, rarity $1/4$
and a deterministic total cap of two flips. A feedback policy, which flips coin
0 and then a fresh coin after a tail or coin 0 again after a head, has worst
mean squared error below $0.015443$ over every measurable sign law with
$\int q\,d\mu\le1/4$; every preselected independent local-acquisition design
has worst mean squared error above $0.015475$, including shared seeds and
nonlinear terminal estimation. The secondary-claims guide retained this as a
paper proof
([`docs/SECONDARY_CLAIMS.md`](../../docs/SECONDARY_CLAIMS.md#5-nonlinear-feedback-depth-and-finite-approximation)).

Lean now checks the upper bound, and the lower bound and the separation
against the seed-conditional normal form under a pathwise cap of two, in
[`lean/ThresholdHC/TwoFlipFeedback`](../../lean/ThresholdHC/TwoFlipFeedback/Full.lean).
The paper's dominance step, which reduces preselected independently executed
local designs to that normal form, is not formalized, so the lower bound is
Lean-checked for the normal-form class, not for the paper's class as stated.
The research package is unchanged. The audit runs below were made at commit
[`eef9ad4`](https://github.com/davidiach/adaptive-threshold-estimation/commit/eef9ad4).

## Statements

[`Specification.lean`](../../lean/ThresholdHC/TwoFlipFeedback/Specification.lean)
defines the gap law `twoGapLaw`, the worst risk `rareSquaredRisk` (the
supremum of `squaredRisk` at the target `signMean` over every rare sign law,
in the original population experiment of `Tier6`), the comparison class
`NoninteractiveCapTwo` with its infimum `noninteractiveMinimax`, the feedback
labelling and the output table in the word order TT, TH, HT, HH. In the class,
after the first flip of coin $c$, either the second action stays on $c$ or
stops, or it never revisits $c$ and whether a second flip happens does not
depend on the first answer; fresh labels may differ between the branches.

| Target | Statement |
|---|---|
| `feedback_upper_bound` | Some estimator with the pinned feedback policy and output table, pathwise cap two and outside the class has worst MSE below $15443/10^6$. |
| `noninteractive_class` | The class contains the same-coin and the two-fresh-coin two-flip schedules, and its minimax is at most $1/64$ (the zero-flip estimator $1/8$). |
| `uniform_lower_bound` | Every member of the class under a pathwise cap of two has worst MSE at least $1547585/10^8$. |
| `noninteractive_lower` | $15475/10^6<$ `noninteractiveMinimax` $\le1/64$. |
| `feedback_separation` | The pinned witness beats the noninteractive minimax by more than $32/10^6$. |

The cap holds on every valid path of every seed, not almost surely. Expected
budgets, asymptotic advantages and the optional block-sequential semantics
are not stated. The witness's output table gives $0$ on words it never
produces.

## How the proofs go

- [`TwoStep.lean`](../../lean/ThresholdHC/TwoFlipFeedback/TwoStep.lean) and
  [`TwoGapLaw.lean`](../../lean/ThresholdHC/TwoFlipFeedback/TwoGapLaw.lean):
  word weights for the six cap-two shapes, and the one- and two-bit
  probabilities at the two-point law, which depend on $q$ only through the
  drift $q(1/4)/4+q(1/8)/8$.
- [`Risk.lean`](../../lean/ThresholdHC/TwoFlipFeedback/Risk.lean): the
  original-experiment MSE as a seed average of a finite sum over words, and,
  for a target in $[0,1/4]$, the risk of a capped estimator bounded below by
  its clipped two-prefix output.
- [`UpperPoly.lean`](../../lean/ThresholdHC/TwoFlipFeedback/UpperPoly.lean)
  and [`Upper.lean`](../../lean/ThresholdHC/TwoFlipFeedback/Upper.lean): the
  risk polynomial of the table on the feasible triangle is at most
  $15442587/10^9$, by convexity in the target, the three vertex values and a
  convex factorization on each edge checked by `ring`; the edge factors were
  derived from the certificate's coefficients.
- [`LowerBayes.lean`](../../lean/ThresholdHC/TwoFlipFeedback/LowerBayes.lean)
  and [`Lower.lean`](../../lean/ThresholdHC/TwoFlipFeedback/Lower.lean): a
  two-point Bayes bound (null law and the hard law $(0,1/2)$ with prior
  $1074499095/2^{31}$), proved for each of the six shapes directly.
- [`Members.lean`](../../lean/ThresholdHC/TwoFlipFeedback/Members.lean): the
  class members and the bound $1/64$.

## Runs

| Command | Outcome | Log |
|---|---|---|
| `python tools/verify_two_flip_feedback.py --replay --jobs 2` | 8 exact statements (the 5 targets and 3 components) and 123 transitive axiom reports over the 10 registered modules, all within `propext`, `Classical.choice` and `Quot.sound`. All 10 modules replayed through the independent kernel checker. No `decide +kernel` is used. | [two-flip-feedback-audit.log](two-flip-feedback-audit.log) |
| `python -m unittest discover -s tools -p 'test_two_flip_feedback.py'` | 11 guard tests pass. | |
| `python tools/verify_project_axioms.py` | 19,627 constants (15,820 theorems) in 1,648 modules, same axioms. 154 exported instances (one new, above); 6 registered orphans, unchanged. 3,661 locked definition fingerprints. | [project-audit.log](project-audit.log) |
| `python tools/verify_lean_sources.py` | 1,649 Lean sources, no proof escapes. | |

The whole-project audit was first run with `--add-definitions`. It added 53
entries to `tools/definition_lock.json`: the five statements, the model
definitions above, the risk polynomial, the Bayes objects, the class members
and their helpers. No existing entry changed. The group adds one exported
instance, `twoGapLaw_probability`, named, global and Prop-valued. The run
recorded here is a later one without that flag.

## Scope

These audits check that the stated types are proved and which axioms the
proofs use. The specification was written before the proofs, reviewed, and
pinned by hash from this audit onward. The result is a comparison at one
deterministic cap; it is not an expected-budget comparison or an asymptotic
advantage, as the guide already says.

## Review

The item was planned by one agent and criticized by a second, which relaxed
the class to a normal form invariant under relabeling of fresh coins, added
the class members and the finite minimax so that the infimum cannot be that
of an empty class, and pinned the witness's policy and output in the
separation. A third agent wrote the proofs. Before the specification was
pinned, a fourth agent that had not written them rebuilt the modules, printed
the axioms, recomputed the vertex values and the six Bayes values in exact
arithmetic (largest vertex $0.0154425865882$, smallest Bayes value
$0.0154758547$), and checked that the relabeled two-fresh design is in the
class and the feedback witness is not. It found no defect in the Lean; its
three minor points concerned docstrings (the origin of the edge factors and
the target range of the clipping bound), corrected before the pin, and the
implementer's notes. These were reviews by AI agents, not a specialist
referee report.

[SHA256SUMS](SHA256SUMS) identifies the files of this record.
