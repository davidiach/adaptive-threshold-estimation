# The Hoeffding count of the finite-cell observable-state bound: library audit

Proposition `prop:outer` of the v6 paper
([`paper/v6/core.tex`](../../paper/v6/core.tex), *Finite-cell
observable-state lower bound*) replicates each rounded magnitude $d_j$ of
weight $w_j$ in $M$ cells of length $w_j/M$ with unknown fixed signs. The sum
of squared target weights is $\sum_jw_j^2/M\le1/M$, so weighted Hoeffding
gives $P_\pm(|\theta(s)-E_\pm\theta(s)|>\Delta/8)\le2\exp(-M\Delta^2/32)$, and
the proof takes an integer $M\ge32\Delta^{-2}\log(2/\delta)$. The checked
construction, `ObservedState.finite_observed_state_lower`, uses the
second-moment condition $M^{-1}\le\delta\Delta^2/16$ instead, and
Appendix `app:finite-observed` records the Hoeffding count as a paper bound.
Lean now checks that count, in
[`lean/ThresholdHC/ObservedHoeffding`](../../lean/ThresholdHC/ObservedHoeffding/Full.lean).
The `ObservedState` group and the paper are unchanged. The audit runs below
were made at commit
[`a4b2e33`](https://github.com/davidiach/adaptive-threshold-estimation/commit/a4b2e33).

## Statements

[`Specification.lean`](../../lean/ThresholdHC/ObservedHoeffding/Specification.lean)
states five targets against the existing `ObservedState` model: the sign
prior `signLaw`, the target `target`, finite-cell estimators, cell designs
with `cellWeight` and separation `cellDelta`, and selected-state estimators
with `stateLaw`.

| Target | Statement |
|---|---|
| `weighted_hoeffding_target` | For nonnegative weights with $\sum_iw_i^2\le v$, $v>0$ and $r\ge0$, every product sign prior gives $P(|\theta(s)-E\theta(s)|>r)\le2\exp(-2r^2/v)$. |
| `replication_tail_target` | $\sum w^2\le1/M$ gives the tail $2\exp(-M\Delta^2/32)$ at radius $\Delta/8$, and $M\ge32\Delta^{-2}\log(2/\delta)$ makes it at most $\delta$. The display of the proof. |
| `hoeffding_confidence_lower_target` | The finite-cell testing lower bound `finite_confidence_lower` with $w_i\ge0$ and the Hoeffding condition $32\log(2/\delta)\sum w^2\le\Delta^2$ in place of $\sum w^2\le\delta\Delta^2/16$. |
| `hoeffding_design_lower_target` | Every finite measurable cell design meeting the Hoeffding condition with $\Delta$ its separation forces $225\,\mathrm{kl}(1-2\delta,2\delta)/(128h^2)\le B$ for every selected-state estimator with expected work at most $B$ that attains radius $\Delta/4$ at failure probability $\delta\le1/8$. |
| `hoeffding_finite_observed` | The proposition with the paper's construction: for every gap law, $h$ and $0<\delta\le1/8$ there are $N$ labels with distinct caps and weights summing to one, $M$ replicas per label with $M=\lceil32\Delta^{-2}\log(2/\delta)\rceil$, the envelope, $\Delta\ge\omega_\mu(h)/8$, the tail bound and the lower bound. |

The rounding is the checked `finite_upward_rounding` (raise to $h$, then a
finite grid with distortion two) rather than the literal grid
$h,2h,4h,\dots$, as for the existing construction. The headline fixes the
least admissible $M$; the design-level target covers every admissible one.
The distinct caps keep one magnitude from being split over several labels.

## How the proofs go

- [`Hoeffding.lean`](../../lean/ThresholdHC/ObservedHoeffding/Hoeffding.lean)
  derives weighted Hoeffding for the sign target from Mathlib's sub-Gaussian
  moment bounds and Hoeffding's lemma, coordinate by coordinate, and the
  replication tail from it.
- [`Lower.lean`](../../lean/ThresholdHC/ObservedHoeffding/Lower.lean)
  repeats the testing argument of `finite_confidence_lower` and the
  design-level argument with the Hoeffding concentration step in place of
  Chebyshev's; the rest of the copied proof is unchanged.
- [`Construction.lean`](../../lean/ThresholdHC/ObservedHoeffding/Construction.lean)
  builds the replicated design with distinct label caps, and
  [`Full.lean`](../../lean/ThresholdHC/ObservedHoeffding/Full.lean) assembles
  the five targets.

## Runs

| Command | Outcome | Log |
|---|---|---|
| `python tools/verify_observed_hoeffding.py --replay --jobs 3` | 8 exact statements (the 5 targets and 3 components) and 26 transitive axiom reports over the 5 registered modules, all within `propext`, `Classical.choice` and `Quot.sound`. All 5 modules replayed through the independent kernel checker. | [observed-hoeffding-audit.log](observed-hoeffding-audit.log) |
| `python -m unittest discover -s tools -p 'test_observed_hoeffding.py'` | 11 guard tests pass. | |
| `python tools/verify_project_axioms.py` | 18,147 constants (14,606 theorems) in 1,548 modules, same axioms. 150 exported instances; 6 registered orphans, unchanged. 3,400 locked definition fingerprints. | [project-audit.log](project-audit.log) |
| `python tools/verify_lean_sources.py` | 1,549 Lean sources, no proof escapes. | |

The whole-project audit was first run with `--add-definitions`. It added six
entries to `tools/definition_lock.json`: the five statements and the centred
cell variable `centeredCell`. No existing entry changed. The run recorded
here is a later one without that flag.

## Scope

These audits check that the stated types are proved and which axioms the
proofs use. The specification was written after the proofs; it is pinned by
hash from this audit onward. Proposition `prop:continuous` uses the same
Hoeffding step; its checked construction (`ContinuousObserved`) still uses
the second-moment count, which is not changed here. The paper's status
sentence in Appendix `app:finite-observed` describes its own build and is
unchanged; a later manuscript update can cite this record.

## Review

The item was planned by one agent, criticized by a second, which asked for
the binding design-level bound and for distinct label caps, and written by a
third. Before the specification was pinned, a fourth agent that had not
written the proofs rebuilt the modules, also with automatic implicits off,
printed the axioms, ran the audit's scans, confirmed with fully qualified
names that every constant resolves as intended, and probed non-vacuity: the
headline construction meets the design-level Hoeffding hypothesis, a
one-cell design never does, and the headline's count is binding: a design
with the second-moment count $M>16/(\delta\Delta^2)$ cannot witness it,
since $16/\delta>32\log(2/\delta)$ for $\delta\le1/8$. It found one minor point:
docstrings left out the nonnegative-weight hypothesis that the statements
add. They were reworded before this audit. These were reviews by AI agents,
not a specialist referee report.

[SHA256SUMS](SHA256SUMS) identifies the files of this record.
