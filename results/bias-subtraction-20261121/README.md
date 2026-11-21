# Bias subtraction in Proposition psi-null: library audit

Proposition `prop:psi-null` of v6 Appendix H bounds the variance–null-work
constant by $\mathfrak J_0(b)\ge\sup_h(\Psi_{\mu,\rho}(h)-4b)_+^2/(192h^2)$ for
$0\le b\le\rho/64$. The remark after it, "The bias subtraction cannot be
uniformly reduced", says the coefficient $4$ cannot be lowered, whatever the
denominator constant. That remark had a paper proof only. Lean now checks it,
in [`lean/ThresholdHC/BiasSubtraction`](../../lean/ThresholdHC/BiasSubtraction/Full.lean).
Proposition `prop:psi-null` itself is not Lean-checked, and the remark does
not need it. The audit runs below were made at commit
[`e9e45a1`](https://github.com/davidiach/adaptive-threshold-estimation/commit/e9e45a1).

## Statement

[`Specification.lean`](../../lean/ThresholdHC/BiasSubtraction/Specification.lean)
states one target, `bias_subtraction`. Take $\rho=1/8$, $\varepsilon=2^{-10}$,
$\mu_d=(1-\varepsilon)\delta_{1/2}+\varepsilon\delta_d$ and
$b_d=\varepsilon(1-2d)/4$. Then $0\le b_d\le\rho/64$ for every gap $d$, and
for every $c<4$ and $K>0$ there is $\delta>0$ such that for every gap $d<\delta$
the bound
$$\mathfrak J_0(b_d)\ge\frac{(\Psi_{\mu_d,\rho}(d)-cb_d)_+^2}{Kd^2}$$
fails. "$\mathfrak J_0(b)\ge J$" is Lean's
[`NullVarianceObstruction`](../../lean/ThresholdHC/ConfidenceLocalization/Obstruction.lean),
the form in which the obstruction enters the RMS and confidence transfers:
for every capped one-coin procedure with bounded output, variance bound $V$
and bias at most $b$ on the half-prior class, $J\le V\cdot W_0$, with $W_0$ the
all-negative work. $\Psi$ is `rarePsi`.

The remark asserts that the right side diverges as $d\downarrow0$; the target
states the consequence, failure for all small $d$, and refutes the bound at
the single resolution $h=d$, which is stronger than refuting the supremum
over $h$. Every $c<4$ is covered, negative $c$ included.

## How the proof goes

The proof is in [`Witness.lean`](../../lean/ThresholdHC/BiasSubtraction/Witness.lean).
The procedure `oneFlipProcedure` ignores its seed, reads one flip $X$ and
returns $X-b_d$. Its output lies in $[-b_d,1-b_d]$, so Popoviciu's inequality
bounds its variance by $1/4$ under every prior, and its work is one. Given the
sign, its mean is $p-b_d$, so under a prior $q\le1/2$ its bias on $\mu_d$ is
$\varepsilon(1/2-d)(1-2q(d))-b_d\in[-b_d,b_d]$ (`oneFlip_bias`). So every valid
constant is at most $1/4$ (`not_obstruction_of_gt`). The allocation equal to
one at the atom $d$ gives $\Psi(d)\ge\varepsilon$ (`remark_psi_lower`), so the
right side is at least $\varepsilon^2(1-c^+/4)^2/(Kd^2)$, which exceeds $1/4$
for small $d$.

## Runs

| Command | Outcome | Log |
|---|---|---|
| `python tools/verify_bias_subtraction.py --replay --jobs 3` | 5 exact statements (the target and 4 components, among them that the law is a probability law) and 24 transitive axiom reports over the 3 registered modules, all within `propext`, `Classical.choice` and `Quot.sound`. All 3 modules replayed through the independent kernel checker. | [bias-subtraction-audit.log](bias-subtraction-audit.log) |
| `python -m unittest discover -s tools -p 'test_bias_subtraction.py'` | 11 guard tests pass. | |
| `python tools/verify_project_axioms.py` | 17,139 constants (13,766 theorems) in 1,474 modules, same axioms. 147 exported instances. 3,233 locked definition fingerprints. | [project-audit.log](project-audit.log) |
| `python tools/verify_lean_sources.py` | 1,475 Lean sources, no proof escapes. | |

The whole-project audit was first run with `--add-definitions`. It added six
entries to `tools/definition_lock.json`: the statement and the helpers
`remarkLaw`, `remarkBias` and `oneFlipProcedure` of `BiasSubtraction`, and the
two statements of `CriticalPairRMS`. No existing entry changed. The run
recorded here is a later one without that flag; it covers both groups.

## Scope

This audit checks that the stated type is proved and which axioms the proof
uses. The specification was written after the proof; it is pinned by hash
from this audit onward. The target says nothing about Proposition
`prop:psi-null` itself or its constant $192$; it shows only that the bias
term $4b$ cannot be replaced by $cb$ with $c<4$ in a bound of that form.

## Review

Before the specification was pinned, a reviewer that had not written the proof
checked that `NullVarianceObstruction` is equivalent to the paper's
$\mathfrak J_0(b)\ge J$, that `CappedPrior` is the half-prior class $X_\rho$
and `rarePsi` the paper's $\Psi$, that the one-flip procedure is a legitimate
capped procedure with bounded output, that the predicate is refuted for real
(it holds at $J=0$), and that every $c<4$ is covered. It found no blocking
problem; its wording fixes were applied and the probability-law lemma is now
pinned. This was a review by an AI agent, not a specialist referee report.

[SHA256SUMS](SHA256SUMS) identifies the files of this record.
