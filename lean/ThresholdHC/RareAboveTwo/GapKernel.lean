import ThresholdHC.RareAboveTwo.SignDistance
import ThresholdHC.RareAboveTwo.Model

noncomputable section
namespace ThresholdHC.RareAboveTwo
open ThresholdHC.Tier6
open MeasureTheory ThresholdHC.Proofs ThresholdHC.Proofs.Transcript ThresholdHC.CriticalEntropy

def gapKernel {m n : ℕ} (pol : List Bool → Option (Fin m)) (q : Fin m → ℝ)
    (x : Fin m → Gap) (w : Fin n → Option Bool) : ℝ := transcriptLaw pol (fun i => (x i : ℝ)) q w

def gapMixture {m n : ℕ} (μ : Measure Gap) (pol : List Bool → Option (Fin m))
    (q : Fin m → ℝ) (w : Fin n → Option Bool) : ℝ :=
  finitePopulationWeight μ pol (fun d => (d : ℝ)) (fun i _ => q i) w

theorem gapKernel_measurable {m n : ℕ} (pol : List Bool → Option (Fin m)) (q : Fin m → ℝ)
    (w : Fin n → Option Bool) : Measurable (fun x => gapKernel pol q x w) := by
  apply Tier5.measurable_variable_transcriptLaw (fun _ : Fin m → Gap => pol)
  · intro xs a; by_cases h : pol xs=a <;> simp [h]
  · intro i; exact measurable_subtype_coe.comp (measurable_pi_apply i)
  · intro i; exact measurable_const

theorem gapKernel_total {m n : ℕ} (pol : List Bool → Option (Fin m)) (q : Fin m → ℝ)
    (hq : ∀ i, 0 ≤ q i ∧ q i ≤ 1) (x : Fin m → Gap) :
    (∀ w : Fin n → Option Bool, 0 ≤ gapKernel pol q x w) ∧ (∑ w : Fin n → Option Bool, gapKernel pol q x w)=1 :=
  transcript_law_total m n pol _ q (fun i => ⟨(x i).property.1.le,(x i).property.2⟩) hq

theorem gapKernel_integrable {m n : ℕ} (μ : Measure Gap) [IsProbabilityMeasure μ]
    (pol : List Bool → Option (Fin m)) (q : Fin m → ℝ) (hq : ∀ i, 0 ≤ q i ∧ q i ≤ 1)
    (w : Fin n → Option Bool) :
    Integrable (fun x => gapKernel pol q x w) (Measure.pi (fun _ : Fin m => μ)) :=
  probability_kernel_integrable _ (gapKernel pol q) (gapKernel_measurable pol q)
    (fun x => (gapKernel_total pol q hq x).1) (fun x => (gapKernel_total pol q hq x).2) w

theorem gapMixture_total {m n : ℕ} (μ : Measure Gap) [IsProbabilityMeasure μ]
    (pol : List Bool → Option (Fin m)) (q : Fin m → ℝ) (hq : ∀ i, 0 ≤ q i ∧ q i ≤ 1) :
    (∀ w : Fin n → Option Bool, 0 ≤ gapMixture μ pol q w) ∧ (∑ w : Fin n → Option Bool, gapMixture μ pol q w)=1 :=
  finite_population_total μ pol _ _ measurable_subtype_coe (fun _ => measurable_const)
    (fun x => ⟨x.property.1.le,x.property.2⟩) (fun i _ => hq i)

theorem update_range {m : ℕ} (q : Fin m → ℝ) (hq : ∀ j, 0 ≤ q j ∧ q j ≤ 1)
    (i : Fin m) (v : ℝ) (hv : 0 ≤ v ∧ v ≤ 1) (j : Fin m) :
    0 ≤ Function.update q i v j ∧ Function.update q i v j ≤ 1 := by
  classical
  by_cases h : j=i
  · subst j; simpa using hv
  · simpa [Function.update_of_ne h] using hq j

theorem gapMixture_mix_update {m n : ℕ} (μ : Measure Gap) [IsProbabilityMeasure μ]
    (pol : List Bool → Option (Fin m)) (q : Fin m → ℝ) (hq : ∀ j, 0 ≤ q j ∧ q j ≤ 1)
    (i : Fin m) (v : ℝ) (w : Fin n → Option Bool) :
    gapMixture μ pol (Function.update q i v) w =
      priorMix v (gapMixture μ pol (Function.update q i 0) w)
        (gapMixture μ pol (Function.update q i 1) w) := by
  have hi₀ := gapKernel_integrable μ pol _ (update_range q hq i 0 (by norm_num)) w
  have hi₁ := gapKernel_integrable μ pol _ (update_range q hq i 1 (by norm_num)) w
  change (∫ x, transcriptLaw pol (fun i => (x i : ℝ)) (Function.update q i v) w
    ∂Measure.pi (fun _ : Fin m => μ)) = _
  simp_rw [transcript_mix_update pol _ q i v w]
  rw [show (fun x : Fin m → Gap => priorMix v
      (transcriptLaw pol (fun i => (x i : ℝ)) (Function.update q i 0) w)
      (transcriptLaw pol (fun i => (x i : ℝ)) (Function.update q i 1) w)) =
      fun x => (1-v)*gapKernel pol (Function.update q i 0) x w+v*gapKernel pol (Function.update q i 1) x w from rfl,
    integral_add (hi₀.const_mul _) (hi₁.const_mul _),integral_const_mul,integral_const_mul]
  rfl

end ThresholdHC.RareAboveTwo
