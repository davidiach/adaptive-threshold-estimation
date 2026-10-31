import ThresholdHC.StoppingProgram.Model
import ThresholdHC.RareAboveTwo.Nonvacuity

/-! Root charges, coefficient positivity, and a finite constant certificate. -/

noncomputable section
open MeasureTheory Set Real
open scoped ENNReal BigOperators

namespace ThresholdHC.StoppingProgram
open ThresholdHC.Tier6 ThresholdHC.RareAboveTwo

theorem prefixLikelihood_nonneg (s : Bool) (n k : ℕ) (d : Gap) : 0 ≤ prefixLikelihood s n k d := by
  have hm : 0 ≤ 1/2-(d:ℝ) := sub_nonneg.mpr d.property.2
  have hp : 0 ≤ 1/2+(d:ℝ) := by linarith [d.property.1]
  cases s <;> simp only [prefixLikelihood,Bool.false_eq_true,ite_false,ite_true] <;> positivity

theorem countCoefficient_nonneg {N : ℕ} (μ : Measure Gap) (q : SignLaw) (s : CountState N) :
    0 ≤ countCoefficient μ q s := by
  apply mul_nonneg (Nat.cast_nonneg _)
  apply integral_nonneg
  intro d
  exact add_nonneg (mul_nonneg (q.property.2 d).1 (prefixLikelihood_nonneg true _ _ d))
    (mul_nonneg (sub_nonneg.mpr (q.property.2 d).2) (prefixLikelihood_nonneg false _ _ d))

theorem countCoefficient_root (N : ℕ) (μ : Measure Gap) [IsProbabilityMeasure μ] (q : SignLaw) :
    countCoefficient μ q (rootState N) = 1 := by
  simp [countCoefficient,rootState,prefixLikelihood]

theorem countMean_nonneg {N : ℕ} (μ : Measure Gap) (q : SignLaw) (u : CountState N → ℝ)
    (hu : ∀ s, 0 ≤ u s) : 0 ≤ countMean μ q u :=
  Finset.sum_nonneg (fun s _ => mul_nonneg (countCoefficient_nonneg μ q s) (hu s))

theorem countMean_ge_root {N : ℕ} (μ : Measure Gap) [IsProbabilityMeasure μ]
    (q : SignLaw) (u : CountState N → ℝ) (hu : ∀ s, 0 ≤ u s) :
    u (rootState N) ≤ countMean μ q u := by
  calc
    u (rootState N) = countCoefficient μ q (rootState N)*u (rootState N) := by
      rw [countCoefficient_root,one_mul]
    _ ≤ countMean μ q u := Finset.single_le_sum (s := Finset.univ)
      (f := fun s : CountState N => countCoefficient μ q s*u s)
      (fun s _ => mul_nonneg (countCoefficient_nonneg μ q s) (hu s)) (Finset.mem_univ _)

theorem flow_work_ge_intensity {N : ℕ} (μ : Measure Gap) [IsProbabilityMeasure μ]
    (q : SignLaw) (f : Flow N) (hf : FlowCone f) : intensity f ≤ countMean μ q f.continueWeight :=
  countMean_ge_root μ q f.continueWeight hf.continue_nonneg

def zeroFlow (N : ℕ) : Flow N := ⟨fun _ => 0,fun _ => 0,fun _ => 0,fun _ => 0⟩

theorem arrayAt_zero (N n k : ℕ) : arrayAt (N := N) (fun _ => 0) n k = 0 := by
  unfold arrayAt
  split_ifs <;> rfl

theorem zeroFlow_cone (N : ℕ) : FlowCone (zeroFlow N) := by
  constructor
  · exact fun _ => le_rfl
  · exact fun _ => le_rfl
  · exact fun _ => le_rfl
  · rfl
  · rfl
  · rfl
  · exact fun _ _ => rfl
  · intro s _
    simp [zeroFlow,arrayAt_zero]
  · intro s
    simp [zeroFlow]

def constantCertificate (N : ℕ) (ρ : ℝ) : Certificate N :=
  ⟨zeroFlow N,ρ/2,ρ/2,0⟩

theorem constantCertificate_feasible (μ : Measure Gap) [IsProbabilityMeasure μ]
    {ρ B : ℝ} (hρ : 0 ≤ ρ) (hB : 0 ≤ B) (N : ℕ) : Feasible μ ρ B (constantCertificate N ρ) := by
  refine ⟨zeroFlow_cone N, by dsimp [constantCertificate]; positivity, le_rfl, ?_, ?_, ?_⟩
  · intro q hq
    have hmean := (signMean_bounds μ q).1
    change signMean μ q.val ≤ ρ at hq
    simp only [constantCertificate,zeroFlow,countMean,mul_zero,Finset.sum_const_zero,add_zero]
    exact abs_le.mpr (by constructor <;> linarith)
  · intro q _
    simp [constantCertificate,zeroFlow,countMean]
  · intro q _
    simpa [constantCertificate,zeroFlow,countMean] using hB

theorem programSquared_le_constant (μ : Measure Gap) [IsProbabilityMeasure μ]
    {ρ B : ℝ} (hρ : 0 ≤ ρ) (hB : 0 ≤ B) (N : ℕ) :
    programSquared μ ρ B N ≤ ENNReal.ofReal ((ρ/2)^2) := by
  have h : programSquared μ ρ B N ≤ certificateSquared (constantCertificate N ρ) :=
    sInf_le ⟨constantCertificate N ρ,constantCertificate_feasible μ hρ hB N,rfl⟩
  simpa only [certificateSquared,constantCertificate,add_zero] using h

theorem programSquared_finite (μ : Measure Gap) [IsProbabilityMeasure μ]
    {ρ B : ℝ} (hρ : 0 ≤ ρ) (hB : 0 ≤ B) (N : ℕ) : programSquared μ ρ B N < ⊤ :=
  (programSquared_le_constant μ hρ hB N).trans_lt ENNReal.ofReal_lt_top

end ThresholdHC.StoppingProgram
