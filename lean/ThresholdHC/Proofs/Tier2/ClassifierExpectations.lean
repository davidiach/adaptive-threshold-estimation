import ThresholdHC.Proofs.Tier2.ClassifierPrefix

noncomputable section
open MeasureTheory ProbabilityTheory Real
namespace ThresholdHC.Tier2
open Uniform713

def coinParameter (d : ℝ) (S : Bool) (hd : 0 < d) (hdmax : d ≤ 1/2) : unitInterval :=
  ⟨coinP d S, by cases S <;> simp only [coinP, Bool.false_eq_true, ↓reduceIte] <;>
    constructor <;> linarith⟩

@[simp] theorem coinParameter_val (d : ℝ) (S : Bool) (hd : 0 < d) (hdmax : d ≤ 1/2) :
    (coinParameter d S hd hdmax : ℝ) = coinP d S := rfl

theorem errProbK_eq_measure (L : ℕ) (d : ℝ) (S : Bool) (hd : 0 < d) (hdmax : d ≤ 1/2) :
    errProbK 1 1 L d S = (tapeMeasure (coinParameter d S hd hdmax)).real
      {ω | Model.decision (fun j => dyadicMean observations j ω) L ≠ bit S} := by
  classical
  let p := coinParameter d S hd hdmax
  have heq : (fun ω => if (classifyK 1 1 L (tapePrefix (2^L) ω)).1 = S then (0:ℝ) else 1) =
      {ω | Model.decision (fun j => dyadicMean observations j ω) L ≠ bit S}.indicator
        (fun _ => (1:ℝ)) := by
    funext ω
    simp only [Set.indicator, Set.mem_ofPred_eq]
    rw [← zK_prefix L le_rfl ω]
    cases h : (classifyK 1 1 L (tapePrefix (2^L) ω)).1 <;> cases S <;>
      simp [h, zK, bit]
  have hs : MeasurableSet {ω | Model.decision (fun j => dyadicMean observations j ω) L ≠ bit S} :=
    (measurableSet_eq_fun
      (Model.measurable_decision _ (tape_mean_tails p).measurable L) measurable_const).compl
  change (∑ x : Fin (2^L) → Bool, streamProb (p : ℝ) x *
    (if (classifyK 1 1 L x).1 = S then 0 else 1)) = _
  rw [← integral_prefix, heq, integral_indicator_const (1:ℝ) hs]
  simp [p]

theorem workK_eq_integral (L : ℕ) (d : ℝ) (S : Bool) (hd : 0 < d) (hdmax : d ≤ 1/2) :
    workK 1 1 L d S = ∫ ω, Model.work (fun j => dyadicMean observations j ω) L
      ∂tapeMeasure (coinParameter d S hd hdmax) := by
  change (∑ x : Fin (2^L) → Bool, streamProb (coinParameter d S hd hdmax : ℝ) x *
    ((classifyK 1 1 L x).2 : ℝ)) = _
  rw [← integral_prefix (coinParameter d S hd hdmax)]
  apply integral_congr_ae
  filter_upwards [] with ω
  exact classifyK_work_prefix L le_rfl ω

theorem deltaK_prefix (l : ℕ) {M : ℕ} (hM : 2^l ≤ M) (ω : ℕ → Bool) :
    deltaK 1 1 l (tapePrefix M ω) =
      increment (fun j => Model.decision (fun k => dyadicMean observations k ω) j) l := by
  cases l with
  | zero => simpa [deltaK, increment] using zK_prefix 0 hM ω
  | succ l =>
    have hm : 2^l ≤ M := (Nat.pow_le_pow_right (by omega : 0 < 2) (Nat.le_succ l)).trans hM
    simp only [deltaK, Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, ↓reduceIte,
      Nat.add_sub_cancel, increment, zK_prefix (l+1) hM ω, zK_prefix l hm ω]

theorem levelWork_prefix (l : ℕ) {M : ℕ} (hM : 2^l ≤ M) (ω : ℕ → Bool) :
    levelWork 1 1 l (tapePrefix M ω) =
      Model.work (fun k => dyadicMean observations k ω) l := by
  cases l with
  | zero => simpa [levelWork] using classifyK_work_prefix 0 hM ω
  | succ l =>
    have hm : 2^l ≤ M := (Nat.pow_le_pow_right (by omega : 0 < 2) (Nat.le_succ l)).trans hM
    simp only [levelWork, Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, ↓reduceIte,
      Nat.add_sub_cancel, classifyK_work_prefix (l+1) hM ω,
      classifyK_work_prefix l hm ω]
    exact max_eq_left (Model.work_mono _ (Nat.le_succ l))

theorem deltaK_secondMoment_eq_integral (L l : ℕ) (hl : l ≤ L) (p : unitInterval) :
    (∑ x : Fin (2^L) → Bool, streamProb (p : ℝ) x * (deltaK 1 1 l x)^2) =
      ∫ ω, (increment (fun j => Model.decision (fun k => dyadicMean observations k ω) j) l)^2
        ∂tapeMeasure p := by
  rw [← integral_prefix]
  apply integral_congr_ae
  filter_upwards [] with ω
  rw [deltaK_prefix l (Nat.pow_le_pow_right (by omega : 0 < 2) hl)]

theorem levelWork_eq_integral (L l : ℕ) (hl : l ≤ L) (p : unitInterval) :
    (∑ x : Fin (2^L) → Bool, streamProb (p : ℝ) x * levelWork 1 1 l x) =
      ∫ ω, Model.work (fun k => dyadicMean observations k ω) l ∂tapeMeasure p := by
  rw [← integral_prefix]
  apply integral_congr_ae
  filter_upwards [] with ω
  exact levelWork_prefix l (Nat.pow_le_pow_right (by omega : 0 < 2) hl) ω

end ThresholdHC.Tier2
