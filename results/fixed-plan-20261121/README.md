# The fixed-plan majority bound: library audit

The toolkit compares the blind algorithm with a fixed plan: buy an odd number
$m$ of flips from each of $n$ fresh coins and output the share of coins with a
majority of heads. The [results guide](../../docs/RESULTS.md#practical-comparison-with-a-fixed-plan)
and item 7 of the [secondary-claims list](../../docs/SECONDARY_CLAIMS.md)
state that, over every sign law at a known gap law, the plan's bias is at most
the mean misclassification probability $e_m$ and its variance at most
$1/(4n)$, so its RMS error is at most $\sqrt{e_m^2+1/(4n)}$; and that for
success rates uniform on $[0,1]$, with $a=(m+1)/2$,
$e_m=2\int_0^{1/2}I_p(a,a)\,dp=\binom{2a}{a}/2^{2a+1}=1/(2a\,\mathrm B(a,1/2))$.
Both guides called this elementary bound paper-only. Lean now checks it, in
[`lean/ThresholdHC/FixedPlan`](../../lean/ThresholdHC/FixedPlan/Full.lean),
for the plan run in the original adaptive experiment. The toolkit's
floating-point evaluation is not covered. The audit runs below were made at
commit
[`d186a91`](https://github.com/davidiach/adaptive-threshold-estimation/commit/d186a91).

## Statements

[`Specification.lean`](../../lean/ThresholdHC/FixedPlan/Specification.lean)
writes $m=2k+1$, so $a=k+1$. It defines the binomial tail
$T_k(p)=P(\mathrm{Bin}(2k+1,p)\ge k+1)$ (`majorityTail`), the miss probability
$T_k(1/2-d)$ of a coin with gap $d$ (`majorityMiss`), its mean $e_m$ over the
gap law (`meanMajorityMiss`), and the plan itself as the checked observable
finite-plan controller with trivial seed (`majorityEstimator`). It states
eleven targets; all but the first assume $n>0$.

| Target | Statement |
|---|---|
| `majorityWork` | The expected work is exactly $n(2k+1)$, for every gap law and sign law. |
| `majorityMissProbability` | The majority vote of $2k+1$ flips of a coin with gap $d$ differs from the coin's sign with probability exactly $T_k(1/2-d)$, for either sign. |
| `majorityMean` | The exact mean of the output: $\int[q(1-\text{miss})+(1-q)\,\text{miss}]\,d\mu$. |
| `majorityBias` | The bias with respect to $\theta=\int q\,d\mu$ is at most $e_m$ in absolute value. |
| `majorityVariance` | The extended variance is at most $1/(4n)$. |
| `majorityMSE` | The mean squared error is at most $e_m^2+1/(4n)$. |
| `majorityRMS` | The plan is in the uniform budget class $n(2k+1)$ and its worst RMS risk over all sign laws is at most $\sqrt{e_m^2+1/(4n)}$. |
| `majorityMinimax` | Hence the minimax risk at any budget $B\ge n(2k+1)$ is at most $\sqrt{e_m^2+1/(4n)}$. |
| `uniformTailIntegral` | $2\int_0^{1/2}T_k(p)\,dp=\binom{2a}{a}/2^{2a+1}$. |
| `uniformMeanMiss` | At the uniform law of gaps, $e_m=\binom{2a}{a}/2^{2a+1}$. |
| `uniformBeta` | $\binom{2a}{a}/2^{2a+1}=1/(2a\,\mathrm B(a,1/2))$ with Mathlib's real beta function. |

Success rates uniform on $[0,1]$ become the uniform law of gaps on $(0,1/2]$,
since a rate $r$ has gap $|r-1/2|$ and the miss probability depends on the gap
only. The source writes $T_k$ as the regularized incomplete beta
$I_p(a,a)$; that classical identity is not stated, so the integral is
checked in binomial-tail form. The exact work, the uniform budget, the mean
squared error and the minimax corollary go beyond the source.

## How the proofs go

- [`Tail.lean`](../../lean/ThresholdHC/FixedPlan/Tail.lean): words of
  $2k+1$ flips counted by heads give the one-coin mean of the vote, the
  symmetry $T_k(p)+T_k(1-p)=1$ by the reflection $j\mapsto2k+1-j$, and the
  tape miss probability under both signs.
- [`Output.lean`](../../lean/ThresholdHC/FixedPlan/Output.lean): the law of
  the output in the experiment is the law of the average of $n$ independent
  votes, which gives the mean, the extended variance and the squared risk.
- [`Risk.lean`](../../lean/ThresholdHC/FixedPlan/Risk.lean): the bias bound
  from the population mixture, the variance bound $1/(4n)$ by Popoviciu's
  inequality for $[0,1]$-valued votes, then the risk, budget and minimax
  statements.
- [`Integral.lean`](../../lean/ThresholdHC/FixedPlan/Integral.lean): the
  derivative of $T_k$ telescopes through Bernstein polynomials to
  $(2k+1)\binom{2k}{k}(p(1-p))^k$, and an explicit antiderivative gives the
  integral; Gamma at half-integers gives the beta form.

## Runs

| Command | Outcome | Log |
|---|---|---|
| `python tools/verify_fixed_plan.py --replay --jobs 3` | 14 exact statements (the 11 targets and 3 components) and 85 transitive axiom reports over the 6 registered modules, all within `propext`, `Classical.choice` and `Quot.sound`. All 6 modules replayed through the independent kernel checker. | [fixed-plan-audit.log](fixed-plan-audit.log) |
| `python -m unittest discover -s tools -p 'test_fixed_plan.py'` | 11 guard tests pass. | |
| `python tools/verify_project_axioms.py` | 17,634 constants (14,188 theorems) in 1,509 modules, same axioms. 147 exported instances. 3,306 locked definition fingerprints. | [project-audit.log](project-audit.log) |
| `python tools/verify_lean_sources.py` | 1,510 Lean sources, no proof escapes. | |

The whole-project audit was first run with `--add-definitions`. It added
seventeen entries to `tools/definition_lock.json`: the six definitions of the
plan (the four above, the vote and the call) and the eleven statements. No existing entry changed. The run recorded here
is a later one without that flag.

## Scope

These audits check that the stated types are proved and which axioms the
proofs use. The specification was written after the proofs; it is pinned by
hash from this audit onward. The toolkit's numerical evaluation of these
formulas, its grid search over $m$ and its simulations are not covered; they
remain with #85 and #86.

## Review

The group was planned by one agent, criticized by a second, which moved the
variance bound to the repository's extended-variance form and added the exact
mean, and written by a third. Before the specification was pinned, a fourth
agent that had not written the proofs rebuilt the modules, checked that each
target elaborates to the intended qualified statement (in particular the
project's `minimaxRisk`, not Mathlib's), printed the axioms, ran the audit's
scans and probed non-vacuity at the uniform law with $k=0$ ($e_m=1/4$, exact
mean $3/4$ under all-positive signs). It found three docstring points: the
reason for the hypothesis $n>0$, a work docstring that described a pathwise
count where the statement is about expected work, and docstrings that called
the binomial tail the incomplete beta without a statement to that effect. All
three were reworded before this audit. These were reviews by AI agents, not a
specialist referee report.

[SHA256SUMS](SHA256SUMS) identifies the files of this record.
