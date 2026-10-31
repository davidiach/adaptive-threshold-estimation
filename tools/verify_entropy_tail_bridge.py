"""Audit compatibility with main's unchanged frozen entropy-tail interface."""
from __future__ import annotations
from pathlib import Path

import verify_entropy_tail as canonical
from verify_blind_upper_components import DECLARATION, FORBIDDEN, strip_comments
from verify_entropy_tail_components import validate_sources as validate_quantile

ROOT = Path(__file__).resolve().parents[1]
LEAN = ROOT / "lean"
PREFIX = "ThresholdHC.EntropyTailBridge."
MODULES = ("Compatibility", "Upper")
TARGETS = dict(canonical.exact_targets())
TARGETS[PREFIX + "canonical_entropy_tail_upper"] = "ThresholdHC.EntropyTail.EntropyTailUpperStatement"
EXACT = r"""
open MeasureTheory
open scoped ENNReal
open ThresholdHC.Tier6 ThresholdHC.EntropyTailQuantile
example : ∀ (μ : Measure Gap) [IsFiniteMeasure μ] (ρ B : ℝ),
    ThresholdHC.EntropyTail.selection μ ρ B = selectionValue μ ρ B :=
  ThresholdHC.EntropyTailBridge.canonical_selection_eq
example : ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] (ρ B : ℝ),
    0 < ρ → ρ ≤ 1/4 → 0 < B →
    ThresholdHC.EntropyTail.selection μ ρ B ≤ closedQuantileValue μ ρ B ∧
    closedQuantileValue μ ρ B ≤ ENNReal.ofReal (1+2*Real.sqrt 2) *
      ThresholdHC.EntropyTail.selection μ ρ B :=
  ThresholdHC.EntropyTailBridge.canonical_quantile_comparison
"""


def validate_sources():
    paths, roots = canonical.validate_sources()
    validate_quantile()
    directory = LEAN / "ThresholdHC/EntropyTailBridge"
    additions = [directory / (name + ".lean") for name in MODULES]
    if set(additions) != set(directory.glob("*.lean")):
        raise ValueError("Missing or unregistered entropy-tail bridge module")
    for path in additions:
        source = strip_comments(path.read_text(encoding="utf-8"))
        if FORBIDDEN.search(source):
            raise ValueError("Forbidden proof escape in " + str(path))
        for name in DECLARATION.findall(source):
            root = PREFIX + name
            if root in roots:
                raise ValueError("Duplicate bridge declaration")
            roots.add(root)
    if not set(TARGETS) <= roots:
        raise ValueError("Missing exact bridge target")
    return paths + additions, roots
