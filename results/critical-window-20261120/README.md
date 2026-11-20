# The critical window: library audit

Corollary 14.14 and Remark 14.15 of the v6 paper (§14.8,
[psi-window.tex](../../paper/v6/psi-window.tex)) were the only tracked v6
results with a paper proof only. Lean now checks both, on top of the
uniform power-law theorem of
[`PowerWindow`](../../lean/ThresholdHC/PowerWindow/Full.lean)
([record](../power-window-complete-20261116/README.md)). The audit runs below
were made at commit
[`44df4ed414c9c7d3ccacb47d27816628d7726121`](https://github.com/davidiach/adaptive-threshold-estimation/commit/44df4ed414c9c7d3ccacb47d27816628d7726121),
which adds the audit tool to the Lean commit
[`4fbb4fcc5a14a45ff652e1226888d71398ddc281`](https://github.com/davidiach/adaptive-threshold-estimation/commit/4fbb4fcc5a14a45ff652e1226888d71398ddc281).

## Statements

[`lean/ThresholdHC/CriticalWindow/Specification.lean`](../../lean/ThresholdHC/CriticalWindow/Specification.lean)
states ten targets. They use only the definitions of `PowerWindow` (the
uniform rate $\mathcal R_\alpha$ of (W7) as `uniformRate`, $\Phi_\alpha$ as
`powerPhi`, $N_\alpha$ as `effectiveScales`), the rare-event minimax risk, the
variational modulus $\Psi$ and the critical log factor $LH$, with
$L=1+\log(1/\rho)$ and $H=1+\log L$. Write $x=(a\sqrt B)^{-1}$,
$Y=x\sqrt{\rho\,\Phi_\alpha(\rho)[1+\log N_\alpha(\rho)]}$,
$Y^0=x\sqrt{\rho\,\Phi_\alpha(\rho)}$ and $\varepsilon=|\alpha-2|$. Every
target assumes $0<\rho\le1/4$; those about a law assume an exact power law
$F(d)=(d/a)^\alpha$ with $0<a\le1/2$ and a budget $B>0$.

| Target | Paper | Statement |
|---|---|---|
| `critical_window_rate` | Cor. 14.14 | For $3/2\le\alpha\le3$: $\min\{\rho,Y\}\le\mathcal R_\alpha(x,\rho)\le5.13\min\{\rho,Y\}$. |
| `critical_window_risk` | Cor. 14.14, (W9) | $10^{-18}\min\{\rho,Y\}\le R_{\mu,\rho}(B)\le3.4\cdot10^5\min\{\rho,Y\}$, the paper's constants. |
| `critical_window_psi` | Cor. 14.14 | $\min\{\rho,Y^0\}/\sqrt2\le\Psi_{\mu,\rho}(B^{-1/2})\le5.13\min\{\rho,Y^0\}$. |
| `critical_window_ratio` | Cor. 14.14 | If $Y\le\rho$: $10^{-19}\sqrt{1+\log N}\,\Psi\le R\le5\cdot10^5\sqrt{1+\log N}\,\Psi$. |
| `window_quadratic_rate` | Rem. 14.15 | At $\alpha=2$, $a=1/4$: $\Phi_2(\rho)=\log(1/\rho)$, $N_2(\rho)=1+\tfrac12\log_2(1/\rho)$ and $2\sqrt{\rho LH/B}\le Y\le4\sqrt{\rho LH/B}$. |
| `window_quadratic_risk` | Rem. 14.15 | For $F(d)=(4d)^2$: $10^{-18}\min\{\rho,\sqrt{\rho LH/B}\}\le R\le1.36\cdot10^6\min\{\rho,\sqrt{\rho LH/B}\}$. |
| `window_away_scales` | Rem. 14.15 | If $\alpha\ne2$ and $u=|1-2/\alpha|\log(1/\rho)\ge1$: $N_\alpha(\rho)=1/\varepsilon$. |
| `window_away_phi` | Rem. 14.15 | If $u\ge1$: $\Phi_\alpha(\rho)$ lies between $1-e^{-1}$ and $1$ times $\alpha/(\alpha-2)$ for $\alpha>2$, and times $\alpha\rho^{1-2/\alpha}/(2-\alpha)$ for $\alpha<2$. |
| `window_away_risk` | Rem. 14.15 | If $\alpha\ne2$ and $u\ge1$: $R$ lies between $5\cdot10^{-19}$ and $7\cdot10^5$ times $\min\{\rho,\ x\rho^{\min\{1/2,1-1/\alpha\}}\sqrt{(1+\log(1/\varepsilon))/\varepsilon}\}$. |
| `window_near_two` | Rem. 14.15 | If $\varepsilon\log(1/\rho)\le1$: $\tfrac12\log(1/\rho)\le\Phi_\alpha(\rho)\le2\log(1/\rho)$ and $\tfrac13\log(1/\rho)\le N_\alpha(\rho)\le2\log(1/\rho)$. |

The corollary's last sentence and the remark state their comparisons "within
universal constants" or "of order"; the targets give explicit constants. The
remark's sentence that the constants stop growing once
$\varepsilon\log(1/\rho)\le1$ is the last target: there $\Phi_\alpha$ and
$N_\alpha$ are of order $\log(1/\rho)$, as for the quadratic law. The paper
assumes $3/2\le\alpha\le3$ throughout; `window_away_phi` keeps that
hypothesis in its statement but does not use $\alpha\le3$.

## How the proof goes

**Rate** ([`Rate.lean`](../../lean/ThresholdHC/CriticalWindow/Rate.lean)).
On the window $\rho\,\Phi_\alpha(\rho)\ge0.53\,\rho^{2-2/\alpha}$
(`rho_phi_lower`), by the paper's two cases: for $\alpha\le2$ the integral of
$s^{\alpha-3}$ over $[s_\rho,2s_\rho]$, and for $\alpha\ge2$ the bound
$s^{\alpha-3}\ge1$ with $s_\rho\le4^{-1/3}\le0.63$. Hence
$\sqrt{\rho\Phi_\alpha}\ge0.728\,\rho^{1-1/\alpha}$. Below the quantile scale
the tail is $T_\alpha(x,\rho)\le3x\rho^{1-1/\alpha}$ (`power_tail_upper`),
so $T_\alpha\le4.13\,Y$. Above it, $Y\ge0.728\rho$. This gives
$\min\{\rho,Y\}\le\mathcal R_\alpha\le5.13\min\{\rho,Y\}$ for every entropy
factor $K\ge1$ in place of $1+\log N_\alpha$ (`window_rate_bounds`).

**Risk, $\Psi$ and the ratio**
([`Measures.lean`](../../lean/ThresholdHC/CriticalWindow/Measures.lean)).
`PowerWindow` checks $10^{-17}\mathcal R_\alpha/\sqrt2\le R\le60002\,\mathcal R_\alpha$,
which gives (W9) with the paper's $10^{-18}$ and $3.4\cdot10^5$, since
$60002\cdot5.13<3.4\cdot10^5$. For an exact power law the entropy-free
quantile functional $\mathcal Q^0$ is the rate with $K=1$
(`power_quantileZero`). With $\mathcal Q^0/\sqrt2\le\Psi\le\mathcal Q^0$ from
[`PsiClosedForm`](../../lean/ThresholdHC/PsiClosedForm/Full.lean) this gives
the $\Psi$ bounds, and the ratio statement follows from both.

**The remark**
([`Remark.lean`](../../lean/ThresholdHC/CriticalWindow/Remark.lean)).
- *At exponent two.* $\log(1/\rho)$ lies between $L/2$ and $L$, and
  $1+\log N_2$ between $H/2$ and $H$, because $N_2\le L\le N_2^2$.
- *Away from two.* $\rho^{1-2/\alpha}=e^{-u}$ for $\alpha>2$, and
  $\rho^{2/\alpha-1}=e^{-u}$ for $\alpha<2$. With $u\ge1$ this gives the
  bounds on $\Phi_\alpha$. These put $Y$ within the factor $2$ of the
  displayed rate (`away_rate_bounds`).
- *Near two.* $\Phi_\alpha=\log(1/\rho)\,(1-e^{-u})/u$ above two and
  $\log(1/\rho)\,(e^{u}-1)/u$ below two, with $u\le2/3$. Elementary
  exponential bounds then give the two-sided estimates.

## Runs

| Command | Outcome | Log |
|---|---|---|
| `python tools/verify_critical_window.py --replay --jobs 3` | 15 exact statements (10 targets and 5 components) and 49 transitive axiom reports over the 5 registered modules, all within `propext`, `Classical.choice` and `Quot.sound`. All 5 modules replayed through the independent kernel checker. | [critical-window-audit.log](critical-window-audit.log) |
| `python tools/verify_project_axioms.py` | 16,456 constants (13,289 theorems) in 1,421 modules, same axioms. 142 exported instances. 3,031 locked definition fingerprints. | [project-audit.log](project-audit.log) |
| `python -m unittest discover -s tools -p 'test_critical_window.py'` | 11 guard tests pass. | |
| `python tools/verify_lean_sources.py` | 1,422 Lean sources, no proof escapes. | |

The whole-project audit was first run with `--add-definitions`. It added
eleven entries to `tools/definition_lock.json`: the ten statement definitions
and the helper `windowRate`, the window rate with a general entropy factor.
No existing entry changed. The run recorded here is a later one without that
flag.

## Scope

These audits check that the stated types are proved and which axioms the
proofs use. The specification was written after the proofs; it is pinned by
hash from this audit onward. `window_quadratic_risk` concerns the
rare-event experiment of `RareAboveTwo` for an exact power law with
$\alpha=2$, $a=1/4$. It gives that law explicit constants. It does not
restate the critical theorem of
[`CriticalEntropy`](../../lean/ThresholdHC/CriticalEntropy/CriticalMinimax.lean),
whose separate model and existential constants are unchanged.

The v6 paper, its status table and
[`paper/v6/status.json`](../../paper/v6/status.json) still list Corollary 14.14
and Remark 14.15 as paper results. They change with the next manuscript
update, not in this record. The floating-point script of the
[closed-form study](../../research/2026-11-09-psi-closed-form/README.md)
remains numerical evidence only.

[SHA256SUMS](SHA256SUMS) identifies the files of this record.
