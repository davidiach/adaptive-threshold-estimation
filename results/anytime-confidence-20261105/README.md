# Observable time-uniform confidence for known gap laws

For every known positive-gap law and $0<\rho,\delta\le1/4$, the
[checked controller](../../lean/ThresholdHC/Anytime/Full.lean) returns nested
intervals with simultaneous coverage at least $1-\delta$ under every rare
sign prior. At each budget it uses at most that many purchased flips.
The interval remains valid at a data-dependent stopping budget.

For $B\ge1$, its half-width is at most
$1500002\mathcal K_{\mu,\rho}(B/\Lambda)$, where
$\Lambda=\log(1/\delta)+2\log(2+\log(1+B)/\log2)$.
This improves the paper's earlier coefficient $1700000$.
The original estimator may know the law, rarity and confidence level.
Both interval endpoints use the same seed and observation history.
[Manuscript Appendix V](../../paper/v6/appendix-anytime.tex)

| Component | Checked scope |
|---|---|
| [History compatibility](../../lean/ThresholdHC/Anytime/Compatibility.lean) | A larger budget preserves every earlier action and observation prefix. |
| [Interval realization](../../lean/ThresholdHC/Anytime/Intervals.lean) | The observable controller computes the running intersection and respects the physical cap on every valid path. It accepts a decision on the last allowed flip and discards filler observations after an early internal stop. |
| [Coverage](../../lean/ThresholdHC/Anytime/Coverage.lean) | All stages share one population experiment. Summable failure allocations give simultaneous coverage and validity at a data-chosen stage. |
| [Width](../../lean/ThresholdHC/Anytime/Width.lean) | The bound holds between stage completions, including the initial zero-observation interval. |

The [native record](status.json) at the [proof checkpoint](https://github.com/davidiach/adaptive-threshold-estimation/commit/ffc0c5eb436ff31706d6f46fc135d1831b5a4e61)
covers 634 modules. All ten new modules compiled without warnings.
Every one of the 624 inherited object hashes matches a published record.
[Nine exact statements](anytime_confidence.lean) and
[29 transitive axiom reports](anytime_confidence.log) passed using only
the standard allowed axioms. Run `python tools/verify_anytime_confidence.py`.

The matching general law-dependent time-uniform lower bound and adaptation
to an unknown law remain open research questions.
