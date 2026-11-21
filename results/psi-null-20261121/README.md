# Proposition psi-null and the budget bound $\Psi/8192$: library audit

Proposition `prop:psi-null` of the v6 transfer appendix
([`appendix-transfer-foundations.tex`](../../paper/v6/appendix-transfer-foundations.tex))
bounds the null-work obstruction:

$$\mathfrak J_0(b)\ge\sup_{h>0}\frac{(\Psi_{\mu,\rho}(h)-4b)_+^2}{192h^2}$$

for every probability law $\mu$ of gaps and every $0\le b\le\rho/64$. Its
corollary `eq:psi-budget-lower`
([`appendix-entropy-tail-lower.tex`](../../paper/v6/appendix-entropy-tail-lower.tex))
is $R_{\mu,\rho}(B)\ge\Psi_{\mu,\rho}(B^{-1/2})/8192$. Both had a paper proof
only. In Lean, $\mathfrak J_0(b)\ge J$ is
[`NullVarianceObstruction`](../../lean/ThresholdHC/ConfidenceLocalization/Obstruction.lean),
the premise of the checked common-pair and RMS transfer theorems, and until
now Lean proved it for no gap law. Lean now checks both statements, in
[`lean/ThresholdHC/PsiNull`](../../lean/ThresholdHC/PsiNull/Full.lean). The
audit runs below were made at commit
[`be3cb53`](https://github.com/davidiach/adaptive-threshold-estimation/commit/be3cb53).

## Statements

[`Specification.lean`](../../lean/ThresholdHC/PsiNull/Specification.lean)
states two targets.

| Target | Statement |
|---|---|
| `psi_null` | For every probability law $\mu$ of gaps, $0<\rho\le1/4$, $0\le b\le\rho/64$ and $h>0$: `NullVarianceObstruction` holds for the original coin parameters $1/2\mp d$ with $J=\max(\Psi_{\mu,\rho}(h)-4b,0)^2/(192h^2)$. |
| `psi_budget_lower` | For every probability law $\mu$ of gaps, $0<\rho\le1/4$ and $B>0$: $\Psi_{\mu,\rho}(B^{-1/2})/8192\le R_{\mu,\rho}(B)$. |

`NullVarianceObstruction` quantifies over every seed space and seed law, and
every one-coin stopped procedure with a deterministic cap on its stopping time
and a bounded output, whose extended variance is at most $V$ and whose bias is
at most $b$ under every capped sign prior ($q\le1/2$, $\int q\,d\mu\le\rho$).
It asserts $J\le V\cdot W_0$, where $W_0$ is the expected work at the
all-negative population. The supremum over $h$ is stated pointwise, which is
equivalent. The rarity range $0<\rho\le1/4$ is the paper's standing
assumption. $\Psi$ is [`rarePsi`](../../lean/ThresholdHC/RareAboveTwo/Model.lean)
and $R_{\mu,\rho}(B)$ is `rareMinimaxRisk`, the minimax RMS risk under an
expected budget $B$ in the original experiment.

## How the proofs go

The proofs follow the paper. They are split into five modules.

- [`StoppedKL.lean`](../../lean/ThresholdHC/PsiNull/StoppedKL.lean): the
  stopped KL chain rule. For a capped procedure the transcript law under the
  coin parameter $p$ has the Bernoulli word probability as density, and the
  per-seed bounded Wald identity gives
  $\mathrm{KL}(P_p\,\|\,P_q)=\mathbb E_pT\cdot\mathrm{kl}(p,q)$ exactly.
- [`OneSided.lean`](../../lean/ThresholdHC/PsiNull/OneSided.lean): for a
  square-integrable statistic and $\mathrm{KL}(P\|Q)<\infty$,
  $(\mathbb E_Pf-\mathbb E_Qf)^2\le2\,\mathrm{KL}(P\|Q)(\mathbb E_Pf^2+\mathbb E_Qf^2)$.
  Only the forward divergence is assumed finite.
- [`Response.lean`](../../lean/ThresholdHC/PsiNull/Response.lean): the
  per-gap response bound `eq:conditional-response-cost`,
  $f(d)^2\le64d^2w_-(d)[A_-(d)+A_+(d)]$. For $d\le1/4$ it combines the two
  steps above; for $d>1/4$, including $d=1/2$, seeds that request no flip
  contribute equally under both signs, and Cauchy–Schwarz on the active seeds
  gives the coefficient twice the activation probability, at most $2w_-(d)$,
  which is below $64d^2w_-(d)$.
- [`Population.lean`](../../lean/ThresholdHC/PsiNull/Population.lean): for
  every feasible allocation $v$ of $\Psi$,
  $\int\min\{v,h\sqrt v/d\}\,d\mu\le4b+h\sqrt{192\,V\,W_0}$
  (`psi_objective_bound`). The allocation is clamped into $[0,1]$, which
  changes it only on a null set. The constant priors $0$ and $\rho$ give the
  variance floor $2\rho/3\le V$, so the second moment at $q=w/2$ is at most
  $3V/2$. The bias bounds at $q=v_h/2$ and at the null prior give
  $\int v_hf\,d\mu\ge\int v_h\,d\mu-4b$, and Cauchy–Schwarz against
  $\int w_-\,d\mu=W_0$ finishes. Bounded output and the cap make every
  conditional function bounded, so the paper's quotient $wf^2/(d^2w_-)$ and
  its truncation step are not needed.
- [`Full.lean`](../../lean/ThresholdHC/PsiNull/Full.lean): `psi_null` takes
  the supremum over allocations and squares. `psi_budget_lower` applies it at
  $h=B^{-1/2}$ and $b=\Psi/64$, where $J=(15\Psi/16)^2B/192$, so
  $\min\{b,\sqrt{J/B}\}=\Psi/64$; the checked RMS transfer
  `minimax_rms_of_obstruction` then gives $R\ge\Psi/(64\cdot128)$. The case
  $\Psi=0$ is trivial.

## Runs

| Command | Outcome | Log |
|---|---|---|
| `python tools/verify_psi_null.py --replay --jobs 3` | 6 exact statements (the 2 targets and 4 components) and 29 transitive axiom reports over the 6 registered modules, all within `propext`, `Classical.choice` and `Quot.sound`. All 6 modules replayed through the independent kernel checker. | [psi-null-audit.log](psi-null-audit.log) |
| `python -m unittest discover -s tools -p 'test_psi_null.py'` | 11 guard tests pass. | |
| `python tools/verify_project_axioms.py` | 17,314 constants (13,916 theorems) in 1,489 modules, same axioms. 147 exported instances. 3,258 locked definition fingerprints. | [project-audit.log](project-audit.log) |
| `python tools/verify_lean_sources.py` | 1,490 Lean sources, no proof escapes. | |

The whole-project audit was first run with `--add-definitions`. It added two
entries to `tools/definition_lock.json`, the two statements. No existing
entry changed. The run recorded here is a later one without that flag.

## Scope

These audits check that the stated types are proved and which axioms the
proofs use. The specification was written after the proofs; it is pinned by
hash from this audit onward. The four components restated in the audit are
`psi_objective_bound`, `gap_response_bound`, `capped_transcript_kl` and
`kl_mean_one_sided`. The confidence-radius consequences of the proposition,
through the common-pair transfer, are not separate targets. The existing
records that call the obstruction unproved describe their own checkpoints and
are unchanged.

## Review

Before the specification was pinned, five reviewers that had not written the
proofs read the group, each with one lens: the fidelity of each target to the
paper, non-vacuity, the proofs and their docstrings, and the guides. The
fidelity and non-vacuity readers found no problem. The proof reader found
three docstring imprecisions: stray working labels, a KL identity stated
without its range $0<p,q<1$, and the coefficient of the activation step. All
three were fixed before this audit; one was judged a misreading by a second
reader but was reworded anyway. The guide reader listed the current guides
that called the obstruction unproved; they are updated with this record. These
were reviews by AI agents, not a specialist referee report.

[SHA256SUMS](SHA256SUMS) identifies the files of this record.
