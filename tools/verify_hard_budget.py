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
import ThresholdHC.HardBudget.Full
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
""".lstrip()
    roots = {"ThresholdHC.HardBudget." + name for name in [
        "readBlock_length", "readBlock_append", "readBlock_untouched", "readBlock_relabel",
        "block_path", "decode_correct", "stageOutput_correct", "next_stage_fresh", "planOutput_readBlock",
        "paid_fits", "count_at_checkpoint", "count_zero_of_small", "estimator", "estimator_output",
        "estimator_cap", "stageInputs_preserving", "clip_loss_le", "stage_loss_le", "timeout_quarter",
        "expected_loss_step", "fallback_rate", "estimator_squared_loss", "observable_fallback",
    ]}
    return src + "".join("#print axioms " + n + "\n" for n in sorted(roots)), roots


def main():
    src, roots = audit_input()
    subprocess.run(["lake", "build", "ThresholdHC.HardBudget.Full"], cwd=LEAN, check=True)
    run = subprocess.run(["lake", "env", "lean", "--stdin"], cwd=LEAN, input=src, text=True,
                         encoding="utf-8", capture_output=True)
    output = run.stdout + run.stderr
    print(output, end="")
    validate_reports(output, run.returncode, roots)
    print(f"Verified {len(roots)} transitive axiom reports")


if __name__ == "__main__":
    main()
