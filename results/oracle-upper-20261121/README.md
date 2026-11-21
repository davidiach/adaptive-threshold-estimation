# The magnitude-oracle upper bound with coefficient one half: library audit

The second review of the rms-constants package
([`adaptive-threshold-second-review.tex`](../../research/2026-11-17-rms-constants/adaptive-threshold-second-review.tex),
paragraphs "An estimator for both oracles" and "Finite budgets, every gap
law") states that for every gap law $\mu$ and every budget $B\ge1$ both
magnitude-oracle minimax RMS risks are at most $\omega_\mu(B^{-1/2})/2$. With
the sharpness paragraph, which Lean checks in
[`OracleSharpness`](../oracle-sharpness-20261121/README.md), this makes $1/2$
exactly the best universal coefficient for either oracle. Lean had lower
bounds only, and the equality $1/6$ at $\mu=\delta_{1/2}$, $B=4$. Lean now
checks the upper bound, in
[`lean/ThresholdHC/OracleUpper`](../../lean/ThresholdHC/OracleUpper/Full.lean).
The research package and the `OracleLower`, `SharpRMS` and `OracleSharpness`
groups are unchanged. The audit runs below were made at commit
[`b538f0b`](https://github.com/davidiach/adaptive-threshold-estimation/commit/b538f0b).

## Statements

[`Specification.lean`](../../lean/ThresholdHC/OracleUpper/Specification.lean)
states three targets, against the existing `revealedMinimaxRisk`,
`selectedMinimaxRisk` and `modulus` of `OracleLower`.

| Target | Statement |
|---|---|
| `oracle_upper` | For every probability law of gaps and every $B\ge1$: both oracle minimax risks are at most $\omega_\mu(B^{-1/2})/2$. |
| `oracle_floor_upper` | The same at the smaller scale: both are at most $\omega_\mu(1/(2\sqrt n))/2$ with $n=\lfloor B\rfloor$. |
| `oracle_upper_coefficient` | For every real $c$ and each oracle separately: the bound $R\le c\,\omega_\mu(B^{-1/2})$ holds at every gap law and every $B\ge1$ if and only if $c\ge1/2$. |

The lower direction of `oracle_upper_coefficient` comes from the checked
`oracle_upper_sharpness` at $B=1$; the sharpness statement is not restated.

## How the proofs go

With $n=\lfloor B\rfloor$, $t=1/(2\sqrt n)$ and $A=\int_{d\ge t}d^{-1}\,d\mu$,
the source draws $n$ fresh magnitudes from $\mathbf 1_{\{d\ge t\}}\mu(dd)/(Ad)$,
buys one flip from each and returns $\tfrac12+\tfrac A4\bar Y$. The proof uses
an equivalent thinning that both oracles can simulate.

- [`FreshProduct.lean`](../../lean/ThresholdHC/OracleUpper/FreshProduct.lean)
  and [`FreshOracle.lean`](../../lean/ThresholdHC/OracleUpper/FreshOracle.lean):
  a policy that creates one fresh coin per step up to a seed-dependent length
  has a product transcript law; this gives the squared risk and the expected
  work of any oracle estimator of that form. Coin names separate history
  lengths only below the stopping length, and the work bound is applied seed
  by seed.
- [`SeedMoments.lean`](../../lean/ThresholdHC/OracleUpper/SeedMoments.lean):
  the exact second moment of a sum of independent bounded terms, and a
  two-stage Fubini argument over the uniforms and the magnitude array.
- [`Thinning.lean`](../../lean/ThresholdHC/OracleUpper/Thinning.lean): a
  window of $m=\lceil n/(tA)\rceil$ array entries is thinned independently,
  entry $i$ kept with probability $r/a_i$ for $a_i\ge t$, $r=n/(mA)\le t$. One
  fresh flip is bought from each kept entry, so the expected number of flips
  is $n$. The revealed oracle reads the array; the selected oracle requests
  each kept magnitude as a fresh coin.
- [`Upper.lean`](../../lean/ThresholdHC/OracleUpper/Upper.lean): the bias is
  at most $\mu(d<t)/2$ and the variance at most $A^2/(16n)$, so the squared
  error is at most $(\mu(d<t)/2)^2+(tA/2)^2\le(\omega_\mu(t)/2)^2$. At $A=0$ the
  output is $1/2$ and $\omega\ge1$. Since $t\le B^{-1/2}$ and the modulus is
  monotone, the floor form gives the stated one.

## Runs

| Command | Outcome | Log |
|---|---|---|
| `python tools/verify_oracle_upper.py --replay --jobs 3` | 6 exact statements (the 3 targets and 3 components) and 97 transitive axiom reports over the 7 registered modules, all within `propext`, `Classical.choice` and `Quot.sound`. All 7 modules replayed through the independent kernel checker. | [oracle-upper-audit.log](oracle-upper-audit.log) |
| `python -m unittest discover -s tools -p 'test_oracle_upper.py'` | 11 guard tests pass. | |
| `python tools/verify_project_axioms.py` | 17,932 constants (14,429 theorems) in 1,528 modules, same axioms. 150 exported instances, two of them the group's named, global, Prop-valued seed-law instances; 6 registered orphans, unchanged. 3,363 locked definition fingerprints. | [project-audit.log](project-audit.log) |
| `python tools/verify_lean_sources.py` | 1,529 Lean sources, no proof escapes. | |

The whole-project audit was first run with `--add-definitions`. It added 39
entries to `tools/definition_lock.json`: the three statements and the
definitions of the estimator, its seed laws and its parameters. No existing
entry changed. The run recorded here is a later one without that flag.

## Scope

These audits check that the stated types are proved and which axioms the
proofs use. The specification was written after the proofs; it is pinned by
hash from this audit onward. The source's large-budget oracle asymptotics are
not targets. The [sharp RMS record](../sharp-rms-20261117/README.md), which
lists the oracle constant $1/2$ as a paper result, describes its own
checkpoint and is unchanged.

## Review

The item was planned by one agent and criticized by a second, which split it
into the sharpness half and this upper half and named three fixes: coin
names that separate history lengths only below the stopping length, a
seed-by-seed work bound, and a two-stage Fubini argument. A third agent wrote
this half against the audited sharpness group. Before the specification was
pinned, a fourth agent that had not written the proofs rebuilt the modules,
replayed them through the kernel checker, restated the targets, printed the
axioms of all 97 public declarations, ran the audit's scans and probed
non-vacuity: the bound lies above the checked lower bound $\omega/6$, at
$\delta_{1/2}$ with $B=100$ both risks are at most $1/10$, below the
zero-work constant estimator's $1/2$, and the floor form applies at the
non-integer budget $7/2$. It found three minor points: two docstrings that
did not match their statements and a local definition equal to
`SharpRMS.bitValue`. The docstrings were reworded and the duplicate is now
documented before this audit. These were reviews by AI agents, not a
specialist referee report.

[SHA256SUMS](SHA256SUMS) identifies the files of this record.
