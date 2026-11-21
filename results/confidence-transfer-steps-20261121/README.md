# Residual steps of the confidence-transfer note: library audit

The confidence-transfer note
([`NOTE.md`](../../research/2026-10-30-confidence-transfer/NOTE.md), round 2)
derives two confidence-radius bounds with a written proof only. Write
$\ell=\log(1/\delta)$ and $r^{\rm exp}(B,\delta)$ for the smallest radius with
failure probability at most $\delta$ under a uniform expected budget $B$.

- Its equation (17): Proposition `prop:psi-null` at $h=\sqrt{\ell/B}$ with
  $b=\Psi(h)/64$, through the common-pair confidence transfer, gives
  $r^{\rm exp}(B,\delta)\ge\Psi(\sqrt{\ell/B})/8192$.
- Its equation (22): for an exact power law $F(d)=(d/a)^\alpha$ on $(0,a]$
  with fixed $\alpha>2$,
  $r(B,\delta)\asymp_\alpha\min\{\rho,\sqrt{\rho\ell}/(a\sqrt B)\}$, and the
  remark after it says that the power-envelope RMS upper constructions can be
  amplified without knowing the exact law.

Lean now checks both equations and the remark, in
[`lean/ThresholdHC/ConfidenceTransferSteps`](../../lean/ThresholdHC/ConfidenceTransferSteps/Full.lean).
The research package and the groups it builds on are unchanged. The audit
runs below were made at commit
[`c1dc062`](https://github.com/davidiach/adaptive-threshold-estimation/commit/c1dc062).

## Statements

[`Specification.lean`](../../lean/ThresholdHC/ConfidenceTransferSteps/Specification.lean)
states three targets for $0<\rho\le1/4$, $B>0$ and $0<\delta\le1/4$, against
the existing `rarePsi`, `confidenceScale`, `rareConfidenceRadius`
($r^{\rm exp}$), `hardConfidenceRadius` ($r^{\rm hard}$, a cap of
$\lfloor B\rfloor$ flips on every valid observable path), `ExactPowerLaw`
and `PowerMargin`. Let $z=\min\{\rho,\sqrt{\rho\ell}/(a\sqrt B)\}$.

| Target | Statement |
|---|---|
| `psi_confidence_null` | For every probability law of gaps, $\Psi_{\mu,\rho}(\sqrt{\ell/B})/8192\le r^{\rm exp}_{\mu,\rho}(B,\delta)$. Equation (17). |
| `above_two_confidence_family` | For every $\alpha>2$ there is $C>0$ such that for all $0<a\le1/2$ and the ranges above one procedure with a pathwise cap of $\lfloor B\rfloor$ flips, chosen before the law, has expected budget $B$ and failure probability at most $\delta$ at radius $Cz$ for every law in the power-margin class with exponent $\alpha$ and scale $a$. The remark after (22). |
| `above_two_confidence` | For every $\alpha>2$ there is $C>0$ such that every exact power law with exponent $\alpha$ and scale $0<a\le1/2$ satisfies $z/8192\le r^{\rm exp}\le r^{\rm hard}\le Cz$. Equation (22) under both budget conventions. |

The note gives no ranges in (22); the ranges here are its standing
hypotheses, and $a>1/2$ is impossible for an exact power law on gaps in
$(0,1/2]$. The lower constant $1/8192$ is universal and does not use
$\alpha>2$; the upper constant depends only on $\alpha$, as $\asymp_\alpha$
allows, and is not explicit.

## How the proofs go

- [`Lower.lean`](../../lean/ThresholdHC/ConfidenceTransferSteps/Lower.lean)
  repeats the arithmetic of `PsiNull.psi_budget_lower` at the confidence
  resolution $h=\sqrt{\ell/B}$: Proposition `prop:psi-null` with $b=\Psi/64$
  gives the null-work obstruction with $J=(15\Psi/16)^2B/(192\ell)$, so
  $\min\{b,\sqrt{J\ell/B}\}=\Psi/64$, and the common-pair confidence transfer
  with constant $1/128$ gives $\Psi/8192$. The power-law lower half uses only
  the support $(0,a]$ of the exact law.
- [`Upper.lean`](../../lean/ThresholdHC/ConfidenceTransferSteps/Upper.lean)
  amplifies the checked above-two RMS family by the capped median
  (`ShiftedPower.amplify_margin`) at the effective budget $B/\ell$; a constant
  estimator covers effective budgets below one. The note says (22) follows
  from its equation (20) by evaluating $\mathcal K$ for the power law; the
  Lean route does not evaluate $\mathcal K$.
- [`Full.lean`](../../lean/ThresholdHC/ConfidenceTransferSteps/Full.lean)
  joins the two halves with $r^{\rm exp}\le r^{\rm hard}$.

## Runs

| Command | Outcome | Log |
|---|---|---|
| `python tools/verify_confidence_transfer_steps.py --replay --jobs 3` | 6 exact statements (the 3 targets and 3 components) and 14 transitive axiom reports over the 4 registered modules, all within `propext`, `Classical.choice` and `Quot.sound`. All 4 modules replayed through the independent kernel checker. | [confidence-transfer-steps-audit.log](confidence-transfer-steps-audit.log) |
| `python -m unittest discover -s tools -p 'test_confidence_transfer_steps.py'` | 11 guard tests pass. | |
| `python tools/verify_project_axioms.py` | 17,985 constants (14,475 theorems) in 1,535 modules, same axioms. 150 exported instances; 6 registered orphans, unchanged. 3,370 locked definition fingerprints. | [project-audit.log](project-audit.log) |
| `python tools/verify_lean_sources.py` | 1,536 Lean sources, no proof escapes. | |

The whole-project audit was first run with `--add-definitions`. It added
three entries to `tools/definition_lock.json`, the three statements. No
existing entry changed. The run recorded here is a later one without that
flag.

## Scope

These audits check that the stated types are proved and which axioms the
proofs use. The specification was written after the proofs; it is pinned by
hash from this audit onward. The note's own lower route for its Theorem 6,
which re-runs the entropy packing at $B/\ell$, is not formalized. For
$2<\alpha\le4$ the `PowerWindow` group already gives the rate in another
form; the new content is $\alpha>4$, the explicit minimum and the constant
$1/8192$ in (17). The research package, whose README calls these steps paper
proofs, describes its own checkpoint and is unchanged.

## Review

The item was planned by one agent, criticized by a second, which replaced
an existential above-two lower bound in the power-law step by the direct
support bound, named a private rewrite to re-prove and flagged the stale
sentence of the results guide, and written by a third. Before the specification was pinned, a fourth agent that
had not written the proofs rebuilt the modules, restated the targets,
printed the axioms of all targets and helpers, ran the audit's scans and
probed non-vacuity: for an exact power law with $\alpha=3$, $a=1/4$ the
expected-budget radius is positive and the hard-cap radius finite, (17)
gives a positive radius for every law, and the family radius at large $B$
falls below the zero-work radius $\rho/2$. It found two minor points: the
specification placed the proofs in `Full.lean`, which only assembles them,
and the `Lower.lean` docstring named the target theorem instead of its proof.
Both were reworded before this audit. These were reviews by AI agents, not a
specialist referee report.

[SHA256SUMS](SHA256SUMS) identifies the files of this record.
