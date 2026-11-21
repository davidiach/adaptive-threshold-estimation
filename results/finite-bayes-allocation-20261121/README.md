# The horizon-eight finite-prior Bayes allocation example: library audit

The population-step research package solves locked finite-prior Bayes
allocation problems exactly
([`RESEARCH_NOTE.tex`](../../research/2026-10-27-population-step/RESEARCH_NOTE.tex),
section Exact finite-horizon evidence;
[`FINAL_REPORT.md`](../../research/2026-10-27-population-step/FINAL_REPORT.md);
the laws and priors of
[`FINITE_LOCK.json`](../../research/2026-10-27-population-step/FINITE_LOCK.json),
the values of
[`FINITE_RESULTS.json`](../../research/2026-10-27-population-step/FINITE_RESULTS.json)
and the program
[`finite_bayes.py`](../../research/2026-10-27-population-step/finite_bayes.py)).
At horizon eight it reports that adaptive allocation improves squared Bayes
error by $1.5917\%$ and $5.0307\%$ over the better of the fresh-only and
single-coin designs. These were exact Fraction computations, not Lean
statements; the secondary-claims guide kept them as finite examples
([`docs/SECONDARY_CLAIMS.md`](../../docs/SECONDARY_CLAIMS.md)). Lean now checks
the comparison for an explicit adaptive witness, in
[`lean/ThresholdHC/FiniteBayesAllocation`](../../lean/ThresholdHC/FiniteBayesAllocation/Full.lean).
The package is unchanged. The audit runs below were made at commit
[`b4d9993`](https://github.com/davidiach/adaptive-threshold-estimation/commit/b4d9993).

## Statements

[`Specification.lean`](../../lean/ThresholdHC/FiniteBayesAllocation/Specification.lean)
works in the original population experiment (private seed, iid hidden gaps,
iid hidden signs, every flip charged). It defines:
- the two atomic gap laws: masses $1/8,7/8$ at gaps $1/32,1/4$ (two scales) and $1/16,3/16,3/4$ at $1/32,1/8,1/2$ (three scales);
- the six and seven locked sign laws, given by their values at the atoms and $0$ off the atoms (a null set), with target $\sum_jm_jq_j$;
- `bayesRisk`, the uniform prior average of the mean squared error;
- `FreshDesign` (coins $0,\dots,7$ in order) and `SingleDesign` (eight flips of coin $0$), each with exactly eight flips, any private seed and any measurable output;
- the two ordered label tables of 256 entries that transcribe the stored horizon-eight policies (`two_scales_policy.json`, `three_scales_policy.json`), inlined so that the pin covers them.

| Target | Statement |
|---|---|
| `two_scales_upper`, `three_scales_upper` | Some estimator with the table policy and a pathwise cap of eight has Bayes squared error at most $2111783001239/10^{15}$ (two scales) or $1706729084112/10^{15}$ (three scales). |
| `restricted_lower` | Every estimator with the fresh design has Bayes error at least $2149143352671/10^{15}$ and $1797138065871/10^{15}$; with the single-coin design, at least $2145940859276/10^{15}$ and $1868722055075/10^{15}$. |
| `two_scales_restricted_tight`, `three_scales_restricted_tight` | Both classes are inhabited, and some member of each has error within $10^{-15}$ of its lower constant. |
| `two_scales_gain`, `three_scales_gain` | Some estimator with a deterministic eight-flip policy has Bayes error at most $1-15917/10^6$ (two scales) or $1-50307/10^6$ (three scales) times that of every estimator with the fresh or the single-coin design. |
| `two_scales_pinned_gain`, `three_scales_pinned_gain` | The same with the witness's policy pinned to the table and a pathwise cap of eight. |

Every upper value is the exact stored fraction rounded up at $10^{-15}$ and
every lower value rounded down. The stored adaptive value is the
dynamic-program minimum; here it is only the risk of the explicit witness, so
the statements do not say that the witness is optimal among adaptive policies,
nor that randomization or earlier stopping cannot help. Horizons one to seven,
other fresh labelings, early stopping and randomized schedules of the
comparison designs are not covered.

## How the proofs go

- [`Weight.lean`](../../lean/ThresholdHC/FiniteBayesAllocation/Weight.lean),
  [`Risk.lean`](../../lean/ThresholdHC/FiniteBayesAllocation/Risk.lean) and
  [`Atoms.lean`](../../lean/ThresholdHC/FiniteBayesAllocation/Atoms.lean): under
  an eight-flip policy a full answer word has, under each sign law, a weight
  that is a product over labels of $a^{\rm heads}(1-a)^{\rm tails}$ integrated
  over the gap law; at the atomic laws it is an explicit rational.
- [`Kernel.lean`](../../lean/ThresholdHC/FiniteBayesAllocation/Kernel.lean) and
  [`Posterior.lean`](../../lean/ThresholdHC/FiniteBayesAllocation/Posterior.lean):
  integer moment sums per word give its evidence-weighted posterior variance,
  and `certify` returns its floor and ceiling sums at precision $10^{20}$.
- [`CertTwo.lean`](../../lean/ThresholdHC/FiniteBayesAllocation/CertTwo.lean) and
  [`CertThree.lean`](../../lean/ThresholdHC/FiniteBayesAllocation/CertThree.lean):
  six `decide +kernel` certificates, for the table, fresh and single designs at
  each law, over all 256 words.
- [`Bayes.lean`](../../lean/ThresholdHC/FiniteBayesAllocation/Bayes.lean),
  [`Cases.lean`](../../lean/ThresholdHC/FiniteBayesAllocation/Cases.lean) and
  [`Full.lean`](../../lean/ThresholdHC/FiniteBayesAllocation/Full.lean): the
  posterior-mean estimator attains the ceiling sums; every estimator with a
  fixed design, after clipping its output to $[0,1/8]$, is at least the floor
  sums, seed by seed.

## Runs

| Command | Outcome | Log |
|---|---|---|
| `python tools/verify_finite_bayes_allocation.py --replay --jobs 2` | 12 exact statements (the 9 targets and 3 components) and 135 transitive axiom reports over the 11 registered modules, all within `propext`, `Classical.choice` and `Quot.sound`. All 11 modules replayed through the independent kernel checker. | [finite-bayes-allocation-audit.log](finite-bayes-allocation-audit.log) |
| `python -m unittest discover -s tools -p 'test_finite_bayes_allocation.py'` | 11 guard tests pass. | |
| `python tools/verify_project_axioms.py` | 21,959 constants (17,778 theorems) in 1,780 modules, same axioms. 163 exported instances, the three new ones the global, Prop-valued probability instances of the two gap laws and the `SizeOf` instance Lean generates for the proof's structure `Code`; 6 registered orphans, unchanged. 4,019 locked definition fingerprints. | [project-audit.log](project-audit.log) |
| `python tools/verify_lean_sources.py` | 1,781 Lean sources, no proof escapes. | |

The two certificate modules each take about a minute to compile here, with at
most 2.6 GB of memory beyond the mapped imports.

The whole-project audit was first run with `--add-definitions`. It added 81
entries to `tools/definition_lock.json`: the nine statements, the laws, sign
laws, designs and tables above, and the word enumeration, moment and
certificate definitions of the proof. No existing entry changed. The run
recorded here is a later one without that flag.

## Scope

These audits check that the stated types are proved and which axioms the
proofs use. The specification was written before the proofs, reviewed, and
pinned by hash from this audit onward.

## Review

The item was planned by one agent and criticized by a second. The critic
re-derived the constants from the stored fractions, replayed the planned
translation of both policy files over all 256 words in exact fractions (it
reproduces the stored adaptive, fresh and single values), and required:
- the tables inlined in the specification, so that the pin covers them;
- the gain stated without the table, with the pinned form kept beside it;
- an inhabitation and tightness statement for each comparison class.

A third agent wrote the proofs. Before the specification was pinned, a fourth
agent that had not written them:
- rebuilt the modules and printed the axioms of the targets;
- checked the masses, gaps and sign laws against the lock file, and the constants against the stored fractions;
- checked both inlined tables entry by entry against a fresh transcription of the policy files, and replayed them in exact fractions.

It found no defect in the Lean. Its minor points were docstrings that said
more than the statements (the table policy "has" an error where the statement
is existential, "every fresh-only design" where the class is the one fixed
labeling, a sign-law formula that holds for distinct atoms), an internal
docstring that called an evidence-weighted sum the posterior variance, and the
location of the implementer's report. The docstrings were corrected before
the pin. These were reviews by AI agents, not a specialist referee report.

[SHA256SUMS](SHA256SUMS) identifies the files of this record.
