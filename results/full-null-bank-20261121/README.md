# The full-null bank of the zero-atom planner: library audit

For a reference law $\alpha=z_0\delta_0+(1-z_0)\eta$ with mass at the zero
gap, the toolkit's robust-continuation planner
([`toolkit/threshold_toolkit/gap_envelope.py`](../../toolkit/threshold_toolkit/gap_envelope.py))
tests positive coins against the full null law: a fair coin with probability
$z_0$ mixed with the all-negative law of $\eta$. The Lean-checked level
certificates of the robust planner use a different bank, whose null law is
$\eta$ alone with allowance $\rho\varepsilon/(1-z_0)$. The guides state that
the bank with the exact null mixture is not the one checked
([`docs/ARBITRARY_LAW_ADAPTATION.md`](../../docs/ARBITRARY_LAW_ADAPTATION.md),
[`docs/ARBITRARY_LAW_FORMALIZATION.md`](../../docs/ARBITRARY_LAW_FORMALIZATION.md)).
Lean now checks that bank and its level certificates, in
[`lean/ThresholdHC/FullNullBank`](../../lean/ThresholdHC/FullNullBank/Full.lean).
This is the first part of the scoped item; the plan and the planner rate built
on this bank are not stated. The toolkit is unchanged. The audit runs below
were made at commit
[`d912af8`](https://github.com/davidiach/adaptive-threshold-estimation/commit/d912af8).

## Statements

[`Specification.lean`](../../lean/ThresholdHC/FullNullBank/Specification.lean)
defines the fair success parameter, the full null law
`fullNullLaw z₀ η` $=z_0\cdot$(fair-coin tape) $+(1-z_0)\cdot$`allNegativeLaw η`,
and the test `fullNullBankTest z₀ η weights u`, which fires on a prefix when
its full-null probability is at most $u$ times its positive-bank probability.

| Target | Statement |
|---|---|
| `full_null_bank` | For $0\le z_0<1$, a probability law $\eta$ and summable weights with total one: the test is upward for every $u$; Ville's bound holds under the full null; the integrated false positives on the positive part are at most $u$; and for a design $\sigma+\tau+\zeta=(1-z_0)\eta$ the race on a positive coin of gap at least $d_0$ in band $j$ has work at most $12\,$`positiveAllowance ε (weights j) ρ (z₀ + threePieceEnvelope σ τ ζ d₀)`$/d_0^2$, where `positiveAllowance ε w ρ V` $=1+\log\varepsilon^{-1}+\log w^{-1}+\max\{0,\log(V/\rho)\}$, and on a negative coin at most $\frac{3}{2d_0^2}(1+\log(\varepsilon w_j)^{-1})$. |
| `full_null_level` | Under a coupling of the reference with the true law and a rare prior: the level error of the race with parameter $L=2k$ (cap $4^k$) with the full-null bank at $u=\rho\varepsilon_l$ is at most the level accuracy, and the level work is at most $128(l+1)\Gamma+6H^2/\rho+2O_\tau+2\,\mathrm{cap}\,L\,(\zeta(\text{all})+\mu_0(\text{all}))$ under $z_0+\zeta(\text{all})\le\rho$. |

The constants and hypotheses are those of the robust planner's
`robust_level_error` and `robust_three_piece_level_work` with $c=1-z_0$; the
changes are the bank, the work premise $z_0+\zeta(\text{all})\le\rho$ and the
per-coin envelope $z_0+$`threePieceEnvelope`. The experiment has positive gaps
only, so there is no physical coin of gap zero: the fair coin enters through
the null likelihood. The coupling is a hypothesis; the work weights are
`referenceWeights σ`, not the toolkit's normalized enclosure costs; and the
toolkit's rational arithmetic and interval oracle are not modelled. The third
conjunct of the bank statement follows from the second.

## How the proofs go

- [`Bank.lean`](../../lean/ThresholdHC/FullNullBank/Bank.lean): the prefix law
  of the full null, the test's monotonicity, Ville's bound, and
  $(1-z_0)\,$`allNegativeLaw η` $\le$ `fullNullLaw`, which gives the integrated
  false positives and the false-positive term of the level error.
- [`CoinWork.lean`](../../lean/ThresholdHC/FullNullBank/CoinWork.lean): survival
  and round bounds for every positive test that fires above the allowance,
  instantiated for the full-null bank, and the negative-coin work.
- [`Level.lean`](../../lean/ThresholdHC/FullNullBank/Level.lean): the level
  error and the coupled level work, following the robust planner's proofs.

## Runs

| Command | Outcome | Log |
|---|---|---|
| `python tools/verify_full_null_bank.py --replay --jobs 2` | 5 exact statements (the 2 targets and 3 components) and 29 transitive axiom reports over the 5 registered modules, all within `propext`, `Classical.choice` and `Quot.sound`. All 5 modules replayed through the independent kernel checker. | [full-null-bank-audit.log](full-null-bank-audit.log) |
| `python -m unittest discover -s tools -p 'test_full_null_bank.py'` | 11 guard tests pass. | |
| `python tools/verify_project_axioms.py` | 21,276 constants (17,281 theorems) in 1,738 modules, same axioms. 156 exported instances; 6 registered orphans, unchanged. 3,842 locked definition fingerprints. | [project-audit.log](project-audit.log) |
| `python tools/verify_lean_sources.py` | 1,739 Lean sources, no proof escapes. | |

The whole-project audit was first run with `--add-definitions`. It added 5
entries to `tools/definition_lock.json`: the two statements, the fair
parameter, the full null law and the test. No existing entry changed. The
run recorded here is a later one without that flag.

## Scope

These audits check that the stated types are proved and which axioms the
proofs use. The specification was written before the proofs, reviewed, and
pinned by hash from this audit onward.

## Review

The item was planned by one agent and criticized by a second, which split
off the plan and planner statements as a later item and fixed the fair
parameter's definition. A third agent wrote the proofs. Before the
specification was pinned, a fourth agent that had not written them:
- rebuilt the modules and printed the axioms;
- checked with full names that every constant resolves as intended, and compared the constants and hypotheses with the robust planner's theorems and the toolkit's `GapEnvelope.null_prefix`;
- checked that the hypotheses can be met, for example with a point mass and the diagonal coupling.

It found no defect in the Lean. Its one minor point concerned the
implementer's notes, which called $2k$ the cap where it is the race parameter.
These were reviews by AI agents, not a specialist referee report.

[SHA256SUMS](SHA256SUMS) identifies the files of this record.
