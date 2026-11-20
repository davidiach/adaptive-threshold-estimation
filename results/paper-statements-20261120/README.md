# Paper statements: library audit

Lean now checks fifteen targets in
[`lean/ThresholdHC/PaperStatements`](../../lean/ThresholdHC/PaperStatements/Full.lean).
Twelve are paper or guide claims that had only a written proof, a numerical
check or an existential constant. Two are bridging statements that make the
critical law's place among the power laws explicit, and one is a new
stability corollary. The $\Psi$ sequence restates, in the critical theorem's own
model, a sequence already checked in the rare-event experiment.
The audit runs below were made at commit
[`c4a1696fa8ec0817b4a20f86a10e6533cfd4da01`](https://github.com/davidiach/adaptive-threshold-estimation/commit/c4a1696fa8ec0817b4a20f86a10e6533cfd4da01),
which applies the review fixes to the first version,
[`be0ea18460c1bdb6d6ca8cb368d3314b3aaeee85`](https://github.com/davidiach/adaptive-threshold-estimation/commit/be0ea18460c1bdb6d6ca8cb368d3314b3aaeee85).

## Statements

[`Specification.lean`](../../lean/ThresholdHC/PaperStatements/Specification.lean)
states fifteen targets. Write $I_\mu=\int d^{-1}\,\mu(dd)$, $L=1+\log(1/\rho)$
and $H=1+\log L$.

| Target | Statement | Before |
|---|---|---|
| `critical_power_law_exact` | The critical density $32d$ on $(0,1/4]$ is the exact power law $F(d)=(4d)^2$. | Implicit in the model. |
| `critical_model` | The critical theorem's minimax risk equals the rare-event minimax risk of that law. | Lean had the budget and risk transport for each algorithm. |
| `critical_explicit_constants` | For $0<\rho\le1/4$ and $B>0$: $10^{-18}\min\{\rho,\sqrt{\rho LH/B}\}\le R_{\mu,\rho}(B)\le100000\min\{\rho,\sqrt{\rho LH/B}\}$. | The lower constant of the critical theorem (v6 `thm:v5-critical`) was existential; $100000$ was already the formal upper constant. |
| `critical_slow_divergence` | The arithmetic of the slow-divergence remark: $\sqrt H<2.54$ for $10^{-100}\le\rho\le1/4$. | Paper remark (v6 `rare-events.tex`). |
| `critical_psi_divergence` | Along $\rho_n=\exp(-e^n)$, $B_n=\rho_n^{-2}$, $n\ge3$, in the critical theorem's own model: $\Psi(B_n^{-1/2})>0$, $R\ge(10^{-18}/16)\sqrt{1+\log(1+\log(1/\rho_n))}\,\Psi(B_n^{-1/2})$, and the factor is at least $\sqrt{1+n}$. | The [paper corollaries](../paper-corollaries-20261120/README.md) check the same sequence in the rare-event experiment, with `rarePsi` and the constant $7\cdot10^{-20}$. |
| `one_flip` | At a fixed gap $d$ some estimator is unbiased for every sign law, with expected work at most one and largest variance exactly $1/(16d^2)$ (`eq:fixed-gap-sharp`). | Paper. |
| `unbiased_fixed_gap_equality` | At every fixed gap, the infimum of $VW$ over unbiased estimators with uniform variance bound $V$ and uniform work bound $W$ is $I_\mu^2/16$. | Paper. |
| `unbiased_sharp_coefficient` | A bound $VW\ge cI_\mu^2$ holds for every law with $I_\mu<\infty$ exactly when $c\le1/16$. | Paper. |
| `half_gap_one_flip` | At the gap $1/2$ some estimator is unbiased, $[0,1]$-valued and has expected work at most one (second sentence of Proposition `prop:bounded`). | Paper. |
| `point_mass_half` | For $B\ge1$, with the law known, a point mass has $R_{\delta_d}(B)\le\omega_{\delta_d}(B^{-1/2})/2$. | Elementary proof in a [numerical study](../../research/2026-11-18-upper-constant/README.md). |
| `observable_second_moment` | One algorithm, chosen before the law, is unbiased with $\sup_q\mathbb E Y^2\le23I_\mu$ and $\sup_q\mathbb E T\le31I_\mu$ for every law with $I_\mu<\infty$ (the moment sentence of Theorem 2.2). | Lean stated the variance bound $23I_\mu$; the second moment was proved only inside its proof. |
| `quantile_root_lower` | The sharp quantile factor satisfies $c_*>1.462554551279$. | The decimal bracket had a rational certificate outside Lean. |
| `quantile_finite_ratio` | Some finitely supported law has $Q>1.462554551279\,\mathcal K$ for some $0<\rho\le1/4$ and $B>0$. | Lean had finite counterexamples for every factor below $c_*$ (`QuantileOptimality.finite_sharpness`); the six-atom certificate of [`verify_optimal_quantile_factor.py`](../../tools/verify_optimal_quantile_factor.py) checked this ratio outside Lean, and a Python verifier a five-atom example with $1.46255$. |
| `selection_stability_quantile` | Selection stability (Corollary 9): for $\mu$ within total variation $2\eta$ of $\mu_0$ and a band-preserving rounding by a factor $r\ge1$, with $Q$ the quantile value of the rounded law, $\max(0,20Q/31-\eta)\le\mathcal K(\mu)\le\min(\rho,rQ+\eta)$. | Lean had $L=5Q/8$; the guide stated $20Q/31$ without a Lean target. |
| `selection_stability_sharp` | The same with $Q/c_*$ in place of $20Q/31$, from the sharp comparison factor. | New. |

`unbiasedVarianceWork` is the infimum, in $[0,\infty]$, of $VW$ over every
measurable seed space and estimator that is unbiased for every measurable sign
law, with $V\ge0$ a uniform bound on the extended variance and $W\ge0$ a
uniform bound on the expected work. It is $\infty$ when no such estimator
exists. The statements that assert an estimator are existential; the proofs
name it.

## How the proofs go

- **Critical law** ([`Critical.lean`](../../lean/ThresholdHC/PaperStatements/Critical.lean)).
  The distribution function of the critical law is $16x^2$ on $[0,1/4]$, so it
  is the exact power law with $\alpha=2$, $a=1/4$. The transport theorems of
  [`HardBudget`](../../lean/ThresholdHC/HardBudget/CriticalTransport.lean)
  identify the two budget classes and risks, so the two minimax risks agree.
  The quadratic-law target of the
  [critical window](../critical-window-20261120/README.md) then gives the
  lower constant, and the critical upper estimator of
  [`CriticalUpper`](../../lean/ThresholdHC/CriticalUpper/Full.lean) gives
  $100000$. For the sequence, $\rho=e^{-\ell}$ with $\ell=e^n\ge20$ gives
  $\sqrt{\rho LH/B}=\rho\sqrt{\rho LH}\le\rho$, and the closed form of
  [`CriticalPsi`](../../lean/ThresholdHC/CriticalPsi/Full.lean) gives
  $0<\Psi\le16\rho\sqrt{\rho L}$. For the remark, $10^{31}<2^{103}$ gives
  $\log10<2.30304$, so $L<231.31$ and $\log L\le8\log2+L/256-1<5.4516$.
- **One flip and the point mass** ([`OneFlip.lean`](../../lean/ThresholdHC/PaperStatements/OneFlip.lean)).
  $N+1$ fresh flips with an affine output $aX+c$ of the number of heads $X$ have
  the binomial mean and second moment, by induction on the number of flips.
  At one flip the output $(X-1/2+d)/(2d)$ has mean $q(d)$ and variance
  $b(1-b)/(4d^2)$, with $b=1/2+(2q(d)-1)d$, which is $1/(16d^2)$ at
  $q\equiv1/2$. The unbiased converse gives the matching lower bound. For the
  point mass, $\lfloor B\rfloor$ flips give squared risk at most
  $1/(16d^2\lfloor B\rfloor)\le1/(4d^2B)$ when $d\sqrt B\ge1$; otherwise the
  constant $1/2$ has risk at most $1/2$ with no work.
- **713** ([`Observable.lean`](../../lean/ThresholdHC/PaperStatements/Observable.lean)).
  The output law is the law of the call value, whose second moment is at most
  $23I_\mu$.
- **Quantile constants** ([`Quantile.lean`](../../lean/ThresholdHC/PaperStatements/Quantile.lean)).
  At $k=1.462554551279$ and $u=1.2591049$, five exponential terms of the
  partition series sum to more than one, with margin about $3\cdot10^{-12}$.
  Each term is bounded below by $1/r^{2^m}$, where $r$ is a rational upper bound
  for $\exp$ at a point of $[0,1]$ from a Taylor sum of up to 18 terms. The
  scalar peak is the maximum of the series over $u\in[1,31/20]$, so it exceeds
  one at $k$; for $k\ge\sqrt2$ the peak is at most one exactly when the root is
  at most $k$, so the root exceeds $k$. `quantile_finite_ratio` is
  `finite_sharpness` applied to this bound. Selection stability transfers any comparison
  $\mathcal K\le Q\le c\mathcal K$ at the rounded law to the lower endpoint
  $Q/c$.

## Runs

| Command | Outcome | Log |
|---|---|---|
| `python tools/verify_paper_statements.py --replay --jobs 3` | 20 exact statements (15 targets and 5 components) and 63 transitive axiom reports over the 6 registered modules, all within `propext`, `Classical.choice` and `Quot.sound`. All 6 modules replayed through the independent kernel checker. | [paper-statements-audit.log](paper-statements-audit.log) |
| `python tools/verify_project_axioms.py` | 16,574 constants (13,382 theorems) in 1,431 modules, same axioms. 142 exported instances. 3,056 locked definition fingerprints. | [project-audit.log](project-audit.log) |
| `python -m unittest discover -s tools -p 'test_paper_statements.py'` | 11 guard tests pass. | |
| `python tools/verify_lean_sources.py` | 1,432 Lean sources, no proof escapes. | |

The whole-project audit was first run with `--add-definitions`. It added
twenty entries to `tools/definition_lock.json`: the fifteen statement
definitions, `unbiasedVarianceWork`, and the estimators `freshFlips`,
`oneFlip`, `pointMassFlips` and the sign law `halfLaw` of the proofs. No
existing entry changed. The run recorded here is a later one without that
flag.

## Scope

These audits check that the stated types are proved and which axioms the
proofs use. The specification was written after the proofs; it is pinned by
hash from this audit onward.

- The critical constants are explicit but conservative. No explicit hard pair
  is claimed. The statement covers $B>0$, wider than the paper's $B\ge1$.
- `one_flip` bounds the expected work by one; that the work is exactly one flip
  is not a target. The unbiased equality is for point masses only; the
  optimum for other laws is not claimed.
- The first sentence of Proposition `prop:bounded`, that no nonnegative
  unbiased output exists when $\mu((0,1/2))>0$, is not a target.
- `point_mass_half` is for a known point mass. The universal constant for a
  known general law is open.
- `quantile_root_lower` is the lower end of the decimal bracket. The upper end
  $c_*<1.462554551280$ keeps its separate rational certificate in
  [`verify_optimal_quantile_factor.py`](../../tools/verify_optimal_quantile_factor.py).
- `critical_slow_divergence` is the arithmetic of the remark; the practical
  reading in the paper is not a formal statement.
- The [numerical study](../../research/2026-11-18-upper-constant/README.md) and
  the earlier records keep their own scopes and are unchanged.

## Review

Before these runs, two reviewers that had not written the proofs read the
fifteen statements against their sources, one for faithfulness and one for
hypotheses, vacuity and Lean conventions. Neither found a statement false to
its source, vacuous or trivially true. The faithfulness reviewer rated two
points important, and both were fixed before the specification was pinned:
the critical upper constant, first taken from the window route as
$1.36\cdot10^6$, is now the existing formal $100000$; and the $\Psi$ sequence
is described as a restatement in the critical model of the sequence the paper
corollaries already check. The minor points were also applied: the sequence
states $\Psi>0$, so it bounds the ratio; the docstrings of existential
statements mention the witness only as what the proof uses; and the point-mass, slow-divergence,
infimum and sharp-stability docstrings give their hypotheses. A second pair
of reviewers then read this record and the guide changes; they found no
blocking problem, and their corrections to the count, the earlier state of the
finite-law ratio and the stated hypotheses are included. These were reviews
by AI agents, not a specialist referee report.

[SHA256SUMS](SHA256SUMS) identifies the files of this record.
