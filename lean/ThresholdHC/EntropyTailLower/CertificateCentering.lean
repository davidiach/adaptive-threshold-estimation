import ThresholdHC.StoppingProgram.FlowConservation
import ThresholdHC.StoppingProgram.FlowBounds
import ThresholdHC.CapIdentification.TerminalMoments

/-! Centering feasible finite certificates at their null mean preserves work,
doubles the bias allowance, and quadruples the variance allowance. The
zero-intensity case forces bias at least half the rarity. -/

noncomputable section
open MeasureTheory Real
open scoped BigOperators
namespace ThresholdHC.EntropyTailLower
open ThresholdHC.Tier6 ThresholdHC.RareAboveTwo ThresholdHC.StoppingProgram
open ThresholdHC.CapIdentification

theorem flow_countMean_square {N : ℕ} (μ : Measure Gap) [IsProbabilityMeasure μ]
    (q : SignLaw) (f : Flow N) (hf : FlowCone f) :
    (countMean μ q f.outputWeight)^2 ≤ intensity f*countMean μ q f.momentWeight := by
  have h := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul Finset.univ
    (r := fun s => countCoefficient μ q s*f.outputWeight s)
    (f := fun s => countCoefficient μ q s*f.stopWeight s)
    (g := fun s => countCoefficient μ q s*f.momentWeight s)
    (fun s _ => mul_nonneg (countCoefficient_nonneg μ q s) (hf.stop_nonneg s))
    (fun s _ => mul_nonneg (countCoefficient_nonneg μ q s) (hf.moment_nonneg s))
    (fun s _ => by
      have hh := mul_le_mul_of_nonneg_left (hf.perspective s) (sq_nonneg (countCoefficient μ q s))
      nlinarith only [hh])
  change (countMean μ q f.outputWeight)^2 ≤ countMean μ q f.stopWeight*countMean μ q f.momentWeight at h
  rwa [countMean_stop_eq_intensity μ q f hf] at h

def centeredFlow {N : ℕ} (f : Flow N) (c : ℝ) : Flow N where
  stopWeight := f.stopWeight
  continueWeight := f.continueWeight
  outputWeight := fun s => f.outputWeight s-c*f.stopWeight s
  momentWeight := fun s => 2*f.momentWeight s+2*c^2*f.stopWeight s

theorem centeredFlow_cone {N : ℕ} (f : Flow N) (hf : FlowCone f) (c : ℝ) :
    FlowCone (centeredFlow f c) := by
  refine ⟨hf.stop_nonneg,hf.continue_nonneg,?_,hf.root_stop,?_,?_,hf.terminal,hf.recursion,?_⟩
  · intro s
    exact add_nonneg (mul_nonneg (by norm_num) (hf.moment_nonneg s))
      (mul_nonneg (by positivity) (hf.stop_nonneg s))
  · simp [centeredFlow,hf.root_output,hf.root_stop]
  · simp [centeredFlow,hf.root_moment,hf.root_stop]
  · intro s
    change (f.outputWeight s-c*f.stopWeight s)^2 ≤
      f.stopWeight s*(2*f.momentWeight s+2*c^2*f.stopWeight s)
    nlinarith [hf.perspective s,sq_nonneg (f.outputWeight s+c*f.stopWeight s)]

theorem centeredFlow_mean {N : ℕ} (μ : Measure Gap) [IsProbabilityMeasure μ]
    (q : SignLaw) (f : Flow N) (hf : FlowCone f) (c : ℝ) :
    countMean μ q (centeredFlow f c).outputWeight = countMean μ q f.outputWeight-c*intensity f := by
  rw [← countMean_stop_eq_intensity μ q f hf]
  simp only [countMean,centeredFlow,Finset.mul_sum,← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl (fun _ _ => by ring)

theorem centeredFlow_moment {N : ℕ} (μ : Measure Gap) [IsProbabilityMeasure μ]
    (q : SignLaw) (f : Flow N) (hf : FlowCone f) (c : ℝ) :
    countMean μ q (centeredFlow f c).momentWeight = 2*countMean μ q f.momentWeight+2*c^2*intensity f := by
  rw [← countMean_stop_eq_intensity μ q f hf]
  simp only [countMean,centeredFlow,Finset.mul_sum,← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun _ _ => by ring)

def centeredCertificate {N : ℕ} (μ : Measure Gap) (C : Certificate N) : Certificate N where
  flow := centeredFlow C.flow (countMean μ nullSignLaw C.flow.outputWeight/intensity C.flow)
  offset := 0
  bias := 2*C.bias
  variance := 4*C.variance

theorem centeredCertificate_feasible {N : ℕ} (μ : Measure Gap) [IsProbabilityMeasure μ]
    (ρ B : ℝ) (hρ : 0 ≤ ρ) (C : Certificate N) (hC : Feasible μ ρ B C)
    (hi : 0 < intensity C.flow) : Feasible μ ρ B (centeredCertificate μ C) := by
  have hnull : RarePrior μ ρ nullSignLaw := by simpa [RarePrior,signMean,nullSignLaw] using hρ
  let c := countMean μ nullSignLaw C.flow.outputWeight/intensity C.flow
  have he : c*intensity C.flow = countMean μ nullSignLaw C.flow.outputWeight := div_mul_cancel₀ _ hi.ne'
  have hsq : c^2*intensity C.flow ≤ C.variance := by
    have hs := (flow_countMean_square μ nullSignLaw C.flow hC.cone).trans
      (mul_le_mul_of_nonneg_left (hC.variance_bound nullSignLaw hnull) hi.le)
    rw [← he] at hs
    apply (mul_le_mul_iff_right₀ hi).mp
    nlinarith only [hs]
  refine ⟨centeredFlow_cone C.flow hC.cone c,by change 0 ≤ 2*C.bias; exact mul_nonneg (by norm_num) hC.bias_nonneg,
    by change 0 ≤ 4*C.variance; exact mul_nonneg (by norm_num) hC.variance_nonneg,?_,?_,hC.work_bound⟩
  · intro q hq
    change |0+countMean μ q (centeredFlow C.flow c).outputWeight-signMean μ q.val| ≤ 2*C.bias
    rw [centeredFlow_mean μ q C.flow hC.cone c,he,zero_add]
    have hb := hC.bias_bound q hq
    have hb0 := hC.bias_bound nullSignLaw hnull
    have hz : signMean μ nullSignLaw.val = 0 := by simp [signMean,nullSignLaw]
    rw [hz,sub_zero] at hb0
    have he' : countMean μ q C.flow.outputWeight-countMean μ nullSignLaw C.flow.outputWeight-signMean μ q.val =
        (C.offset+countMean μ q C.flow.outputWeight-signMean μ q.val)-
          (C.offset+countMean μ nullSignLaw C.flow.outputWeight) := by ring
    rw [he']
    exact (abs_sub _ _).trans (by linarith)
  · intro q hq
    change countMean μ q (centeredFlow C.flow c).momentWeight ≤ 4*C.variance
    rw [centeredFlow_moment μ q C.flow hC.cone c]
    linarith [hC.variance_bound q hq]

theorem centeredCertificate_null_mean {N : ℕ} (μ : Measure Gap) [IsProbabilityMeasure μ]
    (C : Certificate N) (hf : FlowCone C.flow) (hi : 0 < intensity C.flow) :
    countMean μ nullSignLaw (centeredCertificate μ C).flow.outputWeight = 0 := by
  rw [centeredCertificate,centeredFlow_mean μ nullSignLaw C.flow hf,div_mul_cancel₀ _ hi.ne',sub_self]

theorem centeredCertificate_squared {N : ℕ} (μ : Measure Gap) (C : Certificate N) :
    certificateSquared (centeredCertificate μ C) = 4*certificateSquared C := by
  change ENNReal.ofReal ((2*C.bias)^2+4*C.variance) = 4*ENNReal.ofReal (C.bias^2+C.variance)
  have he : (2*C.bias)^2+4*C.variance = 4*(C.bias^2+C.variance) := by ring
  rw [he,ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 4)]
  norm_num

theorem certificate_large_bias_or_positive_intensity {N : ℕ}
    (μ : Measure Gap) [IsProbabilityMeasure μ] (ρ B : ℝ) (hρ : 0 ≤ ρ) (hρ1 : ρ ≤ 1)
    (C : Certificate N) (hC : Feasible μ ρ B C) :
    ρ/2 ≤ C.bias ∨ 0 < intensity C.flow := by
  by_cases hi : 0 < intensity C.flow
  · exact Or.inr hi
  left
  have hi0 : intensity C.flow = 0 := le_antisymm (not_lt.mp hi) (hC.cone.continue_nonneg _)
  have hout : C.flow.outputWeight = fun _ => 0 :=
    funext (fun s => (flow_zero_intensity C.flow hC.cone hi0 s).2.2)
  let q : SignLaw := ⟨fun _ => ρ,measurable_const,fun _ => ⟨hρ,hρ1⟩⟩
  have hq : RarePrior μ ρ q := by simp [RarePrior,signMean,q]
  have hnull : RarePrior μ ρ nullSignLaw := by simpa [RarePrior,signMean,nullSignLaw] using hρ
  have hb := hC.bias_bound q hq
  have hb0 := hC.bias_bound nullSignLaw hnull
  simp [hout,countMean,signMean,q] at hb
  simp [hout,countMean,signMean,nullSignLaw] at hb0
  have h1 := (abs_le.mp hb).1
  have h2 := (abs_le.mp hb0).2
  linarith

end ThresholdHC.EntropyTailLower
