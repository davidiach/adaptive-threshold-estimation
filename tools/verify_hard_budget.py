"""Verify the locked fallback target and its observable execution lemmas."""

from hashlib import sha256
import subprocess

from verify_blind_upper_components import LEAN, validate_reports

LOCK = "857f74f1685705b3d016d1577aaeaf501588a239a4d59241398d8825c46e2d88"


def check_lock():
    path = LEAN / "ThresholdHC/HardBudget/Specification.lean"
    record = path.with_name("SPECIFICATION.sha256").read_text().split()
    if record != [LOCK, "lean/ThresholdHC/HardBudget/Specification.lean"] or sha256(path.read_bytes()).hexdigest() != LOCK:
        raise ValueError("The observable fallback statement changed since the advance checkpoint")


def audit_input():
    check_lock()
    src = """
import ThresholdHC.HardBudget.Ordinary
import ThresholdHC.HardBudget.Rare
import ThresholdHC.HardBudget.Critical
noncomputable section
open ThresholdHC.HardBudget ThresholdHC.Tier6 ThresholdHC.ObservableSimulation
open scoped ENNReal
example {R : Type} [MeasurableSpace R] (A : AdaptiveEstimator R) (r : R) (n : ℕ) (M : ℝ) (s : Table) :
    stageOutput A M r (readBlock n (fun h => (A.policy r h).getD 0) s).1 = stageResult A n M r s :=
  stageOutput_correct A M n r s
example {R : ℕ → Type} [∀ j, MeasurableSpace (R j)] (A : ∀ j, AdaptiveEstimator (R j))
    (r : ∀ j, R j) (s : Table) (k j : ℕ) :
    (readBlock (paid k) (planReader A r k) s).2 (Nat.pair k j) = s (Nat.pair k j) :=
  next_stage_fresh A r k s j
example {R : ℕ → Type} [∀ j, MeasurableSpace (R j)] (A : ∀ j, AdaptiveEstimator (R j))
    (M : ℝ) (r : ∀ j, R j) (s : Table) (k : ℕ) :
    planOutput A M r k (readBlock (paid k) (planReader A r k) s).1 = idealFallback A M r s k :=
  planOutput_readBlock A M r s k
example {R : ℕ → Type} [∀ j, MeasurableSpace (R j)] (A : ∀ j, AdaptiveEstimator (R j))
    (M : ℝ) (k : ℕ) : PathwiseCap (estimator A M k) (paid k) := estimator_cap A M k
example {R : ℕ → Type} [∀ j, MeasurableSpace (R j)] (A : ∀ j, AdaptiveEstimator (R j))
    (M : ℝ) (k : ℕ) (μ : MeasureTheory.Measure Gap) [MeasureTheory.IsProbabilityMeasure μ] (q : SignLaw) :
    MeasureTheory.MeasurePreserving stageInputs (originalSimulationLaw μ (estimator A M k) q)
      (MeasureTheory.Measure.infinitePi (fun i => originalSimulationLaw μ (A i) q)) :=
  stageInputs_preserving A M k μ q
example : ObservableFallbackStatement := observable_fallback
example (μ : MeasureTheory.Measure Gap) [MeasureTheory.IsProbabilityMeasure μ] {B : ℝ} (hB : 1 ≤ B) :
    ENNReal.ofReal (modulus μ (1/Real.sqrt B)/64) ≤ hardMinimaxRisk μ B ∧
      hardMinimaxRisk μ B ≤ ENNReal.ofReal (3000*modulus μ (1/Real.sqrt B)) := ordinary_hard_minimax μ hB
example : ∃ rule : ℝ → AdaptiveEstimator (ℕ → ThresholdHC.BlindUpper.BatchSeed),
    (∀ B : ℝ, 0 ≤ B → PathwiseCap (rule B) ⌊B⌋₊) ∧
    ∀ (B : ℝ), 0 < B → ∀ (μ : MeasureTheory.Measure Gap) [MeasureTheory.IsProbabilityMeasure μ],
      maximalRMSRisk μ (rule B) ≤ ENNReal.ofReal (3000*modulus μ (1/Real.sqrt B)) := ordinary_hard_family
example (μ : MeasureTheory.Measure Gap) [MeasureTheory.IsProbabilityMeasure μ] {ρ B : ℝ}
    (hr : 0 < ρ) (hu : ρ ≤ 1/4) (hb : 0 < B) :
    ENNReal.ofReal ((10:ℝ)⁻¹^17)*ThresholdHC.EntropyTail.selection μ ρ B ≤ hardRareMinimaxRisk μ ρ B ∧
      hardRareMinimaxRisk μ ρ B ≤ 160000*ThresholdHC.EntropyTail.selection μ ρ B := rare_hard_minimax μ hr hu hb
open ThresholdHC.ConfidenceTransfer ThresholdHC.CriticalEntropy
example : ∃ c : ℝ, 0 < c ∧ ∀ {ρ B : ℝ}, 0 < ρ → ρ ≤ 1/4 → 0 < B →
    ENNReal.ofReal (c*min ρ (Real.sqrt (ρ*criticalLogFactor ρ/B))) ≤ hardRareMinimaxRisk criticalPositiveLaw ρ B ∧
    hardRareMinimaxRisk criticalPositiveLaw ρ B ≤ ENNReal.ofReal (570000*min ρ (Real.sqrt (ρ*criticalLogFactor ρ/B))) :=
  critical_hard_minimax
""".lstrip()
    roots = {"ThresholdHC.HardBudget." + name for name in [
        "readBlock_length", "readBlock_append", "readBlock_untouched", "readBlock_relabel",
        "block_path", "decode_correct", "stageOutput_correct", "next_stage_fresh", "planOutput_readBlock",
        "paid_fits", "count_at_checkpoint", "count_zero_of_small", "estimator", "estimator_output",
        "estimator_cap", "stageInputs_preserving", "clip_loss_le", "stage_loss_le", "timeout_quarter",
        "expected_loss_step", "fallback_rate", "estimator_squared_loss", "observable_fallback",
        "pathwise_expected", "rms_family", "ordinary_budget_scale", "ordinary_hard_family", "ordinary_hard_minimax",
        "selection_budget_scale", "selection_saturates", "rare_hard_family", "rare_hard_minimax",
        "critical_observable_transport", "critical_budget_equivalence", "critical_risk_equivalence",
        "critical_rate_small", "critical_rate_scale", "critical_hard_family", "critical_hard_minimax",
    ]}
    return src + "".join("#print axioms " + n + "\n" for n in sorted(roots)), roots


def main():
    src, roots = audit_input()
    subprocess.run(["lake", "build", "ThresholdHC.HardBudget.Ordinary", "ThresholdHC.HardBudget.Rare",
                    "ThresholdHC.HardBudget.Critical"], cwd=LEAN, check=True)
    run = subprocess.run(["lake", "env", "lean", "--stdin"], cwd=LEAN, input=src, text=True,
                         encoding="utf-8", capture_output=True)
    output = run.stdout + run.stderr
    print(output, end="")
    validate_reports(output, run.returncode, roots)
    print(f"Verified {len(roots)} transitive axiom reports")


if __name__ == "__main__":
    main()
