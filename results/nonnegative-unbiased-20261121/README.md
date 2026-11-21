# Nonnegative unbiased outputs: library audit

The first sentence of Proposition `prop:bounded` (v6 §6) had a paper proof
only. Lean now checks it, in
[`lean/ThresholdHC/NonnegativeUnbiased`](../../lean/ThresholdHC/NonnegativeUnbiased/Full.lean).
Its second sentence, about the endpoint gap $1/2$, is checked as
`half_gap_one_flip` in the [paper statements](../paper-statements-20261120/README.md).
The audit runs below were made at commit
[`4a64b683402c07d5866f0d0328699febb22d5e9c`](https://github.com/davidiach/adaptive-threshold-estimation/commit/4a64b683402c07d5866f0d0328699febb22d5e9c).

## Statement

[`Specification.lean`](../../lean/ThresholdHC/NonnegativeUnbiased/Specification.lean)
states one target, `nonnegative_unbiased_impossible`. If $\mu((0,1/2))>0$, no
algorithm in the Tier 6 observable experiment, where the algorithm sees only
its seed and the flips, that, under every measurable
sign law, stops almost surely and has almost surely nonnegative output is
unbiased for every measurable sign law. The paper asks for output that is
always nonnegative; the Lean hypothesis asks only for almost surely
nonnegative output under each sign law, so the theorem is slightly stronger.
Stopping means that at some step the policy returns no coin; on a realized
path the tape then stays empty.

## How the proof goes

The proof is in [`Support.lean`](../../lean/ThresholdHC/NonnegativeUnbiased/Support.lean).

- Under the all-negative sign law the target is zero, so a nonnegative
  unbiased output vanishes almost surely.
- Under the law $q_1(d)=\mathbf 1\{d<1/2\}$, every finite transcript with
  positive probability also has positive probability under the all-negative
  law (`support_compare`). By the factorization of the transcript law, each
  coin contributes either the likelihood of a gap $d<1/2$, which is positive
  for both signs, or that of the endpoint gap, which is negative under both
  laws.
- Once the policy returns no coin, a valid tape stays empty
  (`stopped_tail`), so the output is a function of a finite prefix
  (`pad_prefix`).
- For every $n$, the event that the policy has stopped by step $n$ with
  nonzero output is a prefix event of probability zero under the all-negative
  law, hence of probability zero under $q_1$, by the realization of creation
  prefixes. The algorithm stops almost surely, so its output vanishes almost
  surely under $q_1$, while its target is $\mu((0,1/2))>0$.

## Runs

| Command | Outcome | Log |
|---|---|---|
| `python tools/verify_nonnegative_unbiased.py --replay --jobs 3` | 4 exact statements (the target and 3 components) and 14 transitive axiom reports over the 3 registered modules, all within `propext`, `Classical.choice` and `Quot.sound`. All 3 modules replayed through the independent kernel checker. | [nonnegative-unbiased-audit.log](nonnegative-unbiased-audit.log) |
| `python -m unittest discover -s tools -p 'test_nonnegative_unbiased.py'` | 11 guard tests pass. | |
| `python tools/verify_project_axioms.py` | 17,021 constants (13,664 theorems) in 1,454 modules, same axioms. 147 exported instances. 3,217 locked definition fingerprints. | [project-audit.log](../explicit-constants-20261121/project-audit.log) of the explicit-constants record, the same run |
| `python tools/verify_lean_sources.py` | 1,455 Lean sources, no proof escapes. | |

The whole-project audit was first run with `--add-definitions`. It added nine
entries to `tools/definition_lock.json`: the five statements of
`ExplicitConstants`, and the statement and the helpers `pad`, `hist` and
`stopEvent` of `NonnegativeUnbiased`. No existing entry changed. The run
recorded here is a later one without that flag; it covers both groups.

## Scope

These audits check that the stated type is proved and which axioms the proof
uses. The specification was written after the proof; it is pinned by hash from
this audit onward. The theorem concerns unbiasedness over the whole sign class
at a fixed gap law; it says nothing about a single sign law or a structured
subfamily. It is stated in the hidden-magnitude model; the paper's remark that
the argument also covers revealed magnitudes is not checked. The helpers `pad`
and `hist` duplicate `Tier4.padPrefix` and `Proofs.fullHist`, and
`stopped_tail` and `pad_prefix` restate existing reconstruction lemmas.

## Review

Before the specification was pinned, a reviewer that had not written the proof
compared the statement with the paper and read the proof. It found the
statement faithful and not vacuous: the immediately stopping zero estimator
meets both hypotheses and is correctly not unbiased, the one-flip estimator
shows the nonnegativity hypothesis is needed, and the stop predicate cannot be
met by a policy that would continue at a longer history, because a valid tape
stays empty after the policy stops. It found the proof sound as read, with no
blocking problem; its wording fixes were applied. This was a review by an AI
agent, not a specialist referee report.

[SHA256SUMS](SHA256SUMS) identifies the files of this record.
