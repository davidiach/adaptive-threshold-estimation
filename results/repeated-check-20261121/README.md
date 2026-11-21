# Repeatedly inspecting a fixed-time interval is not valid: library audit

The confidence-transfer package
([`ANYTIME.md`](../../research/2026-10-30-confidence-transfer/ANYTIME.md),
section *Repeatedly inspecting fixed-time intervals is not valid*) takes iid
Bernoulli$(1/4)$ coins with head count $H_n$ and states

$$P\{(4H_n-n)^2>12n\}\le1/4\quad\text{for every fixed }n, \tag{28}$$

so the interval $H_n/n\pm\sqrt{3/(4n)}$ has fixed-time coverage at least
$3/4$ for every $\theta\in[0,1/4]$, and, by exact integer path counting,

$$P\{\exists n\le512:(4H_n-n)^2>12n\}=0.42809100970105135\ldots>1/4. \tag{29}$$

The package checks (29) with a Python path count. Lean now checks both
displays, in
[`lean/ThresholdHC/RepeatedCheck`](../../lean/ThresholdHC/RepeatedCheck/Full.lean).
The research package is unchanged. The audit runs below were made at commit
[`651935f`](https://github.com/davidiach/adaptive-threshold-estimation/commit/651935f).

## Statements

[`Specification.lean`](../../lean/ThresholdHC/RepeatedCheck/Specification.lean)
uses the project's coin model, the product of Bernoulli$(\theta)$ laws on
$\omega:\mathbb N\to\{0,1\}$ (definitionally `Tier2.tapeMeasure θ`), with
$H_n$ the number of heads among the first $n$ flips.

| Target | Statement |
|---|---|
| `fixed_time` | For every $\theta\le1/4$ and every $n$, $P\{3n<4(H_n-n\theta)^2\}\le1/4$: the miss event of the interval, in polynomial form. Display (28), uniformly in $\theta$. |
| `repeated_check` | At $\theta=1/4$, $0.4280910097010513<P\{\exists n\le512:12n<(4H_n-n)^2\}<0.4280910097010514$. Display (29). |
| `repeated_check_invalid` | At $\theta=1/4$, each fixed-time check fails with probability at most $1/4$ and the repeated check with probability more than $1/4$. |

The polynomial miss event is empty at $n=0$, so no conventional value of
$\sqrt{3/(4n)}$ enters; at $\theta=1/4$ it is the source's
$(4H_n-n)^2>12n$. The exact value of (29) is $1-S/4^{512}$ for an integer
survivor weight $S$ (the component `repeated_check_exact`), which is
$0.4280910097010513377\ldots$. The source's display
$0.42809100970105135$ is a floating-point rendering slightly above it, so a
bracket built from all its digits would be false; the bracket here keeps 16
correct digits. The stopped form, with the first crossing or $512$ as an
observable stopping time, is the component `stopped_check`. The hidden-coin
embedding remarked after (29), with $\mu=\delta_{1/2}$, is not formalized;
the targets cover the iid Bernoulli$(1/4)$ model.

## How the proofs go

- [`FixedTime.lean`](../../lean/ThresholdHC/RepeatedCheck/FixedTime.lean):
  Chebyshev's inequality with the exact variance $n\theta(1-\theta)$ gives
  the miss probability $4\theta(1-\theta)/3\le1/4$.
- [`Row.lean`](../../lean/ThresholdHC/RepeatedCheck/Row.lean) and
  [`Certificate.lean`](../../lean/ThresholdHC/RepeatedCheck/Certificate.lean):
  the survivor rows of the path count, computed in one pass, and a
  `decide +kernel` evaluation of all 512 rows with the bounds on $S$.
- [`PathCount.lean`](../../lean/ThresholdHC/RepeatedCheck/PathCount.lean)
  and [`Exact.lean`](../../lean/ThresholdHC/RepeatedCheck/Exact.lean): a
  prefix induction shows the surviving mass of words of length $n$ with $k$
  heads is $\mathrm{survivor}(n,k)/4^n$, and the prefix-integral bridge gives
  $P=1-S/4^{512}$.
- [`StopRule.lean`](../../lean/ThresholdHC/RepeatedCheck/StopRule.lean): the
  first-crossing rule is observable, and its stopped miss event is the
  existential event of (29).

## Runs

| Command | Outcome | Log |
|---|---|---|
| `python tools/verify_repeated_check.py --replay --jobs 3` | 6 exact statements (the 3 targets and 3 components) and 71 transitive axiom reports over the 8 registered modules, all within `propext`, `Classical.choice` and `Quot.sound`. All 8 modules replayed through the independent kernel checker, which re-evaluates the certificate. | [repeated-check-audit.log](repeated-check-audit.log) |
| `python -m unittest discover -s tools -p 'test_repeated_check.py'` | 11 guard tests pass. | |
| `python tools/verify_project_axioms.py` | 18,619 constants (15,007 theorems) in 1,574 modules, same axioms. 151 exported instances; 6 registered orphans, unchanged. 3,471 locked definition fingerprints. | [project-audit.log](project-audit.log) |
| `python tools/verify_lean_sources.py` | 1,575 Lean sources, no proof escapes. | |

The whole-project audit was first run with `--add-definitions`. It added 23
entries to `tools/definition_lock.json`: the three statements, the survivor
rows and weight, the head count, the stopping time, and their auxiliary
definitions. No existing entry changed. The run recorded here is a later one
without that flag.

## Scope

These audits check that the stated types are proved and which axioms the
proofs use. The specification was written after the proofs; it is pinned by
hash from this audit onward. The certificate step peaked at about 4.6 GB of
memory in the review's rebuild. The research package, whose (29) shows the
floating-point digits, describes its own checkpoint and is unchanged.

## Review

The item was planned by one agent, criticized by a second, which rewrote (28)
in polynomial form, fixed the bracket and suggested the stopping-rule
component, and written by a third. Before the specification was pinned, a
fourth agent that had not written the proofs rebuilt the modules, checked the
statements with explicit numeric types, recomputed the survivor weight with
the package's own recursion and found it equal to the certificate's, printed
the axioms and ran the audit's scans, and probed non-vacuity at the
instantiated bracket. It found three minor points: two docstrings that did
not match their declarations and one unused lemma. The docstrings were
reworded and the lemma removed before this audit. These were reviews by AI
agents, not a specialist referee report.

[SHA256SUMS](SHA256SUMS) identifies the files of this record.
