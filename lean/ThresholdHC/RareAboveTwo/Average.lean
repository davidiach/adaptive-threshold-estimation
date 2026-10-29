import ThresholdHC.RareAboveTwo.UnbiasedWork
import ThresholdHC.BlindUpper.ProductionAverage
import ThresholdHC.BlindUpper.InfiniteArrays

/-! Independent calls: exact seed pairing, averaging error and summed actual work. -/

noncomputable section
namespace ThresholdHC.RareAboveTwo
open MeasureTheory ProbabilityTheory ThresholdHC.CriticalEntropy ThresholdHC.Uniform713
open ThresholdHC.Tier6 ThresholdHC.ObservableSimulation
open scoped ENNReal

abbrev RareSeed := ℕ → ℕ

def rareSeedLaw : Measure RareSeed := Measure.infinitePi (fun _ : ℕ => levelMeasure)

instance rareSeedLaw_probability : IsProbabilityMeasure rareSeedLaw := by
  unfold rareSeedLaw
  infer_instance

def rareCalls (z : RareSeed × (ℕ → ℕ → Bool)) : ℕ → ℕ × (ℕ → Bool) :=
  fun i => (z.1 i,z.2 i)

theorem measurable_rareCalls : Measurable rareCalls := by
  exact Measurable.of_eval (fun i => ((measurable_pi_apply i).comp measurable_fst).prodMk
    ((measurable_pi_apply i).comp measurable_snd))

theorem rareCalls_preserving (μ : Measure Gap) [IsProbabilityMeasure μ] (q : SignLaw) :
    MeasurePreserving rareCalls
      (rareSeedLaw.prod (Measure.infinitePi (fun _ : ℕ => originalPopulationTapeLaw μ q)))
      (Measure.infinitePi (fun _ : ℕ => samplingMeasure (originalPopulationTapeLaw μ q))) := by
  exact ⟨measurable_rareCalls,BlindUpper.infinitePi_zip
    (fun _ : ℕ => levelMeasure) (fun _ : ℕ => originalPopulationTapeLaw μ q)⟩

def rareAverage (a ρ : ℝ) (n : ℕ) :=
  BlindUpper.productionAverage (rareUnbiasedProcedure a ρ).output n

theorem rareAverage_mse (μ : Measure Gap) [IsProbabilityMeasure μ]
    (α a ρ : ℝ) (hα : 2 < α) (ha : 0 < a) (ha' : a ≤ 1/2)
    (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hm : PowerMargin μ α a) (q : SignLaw)
    (hq : RarePrior μ ρ q) (n : ℕ) :
    (∫⁻ z, ENNReal.ofReal ((rareAverage a ρ n z-signMean μ q.val)^2)
      ∂Measure.infinitePi (fun _ : ℕ => samplingMeasure (originalPopulationTapeLaw μ q))) ≤
      ENNReal.ofReal (28*ρ/((n : ℝ)+1)) := by
  have hY := rareUnbiased_memLp μ α a ρ hα ha ha' hρ hρ1 hm q hq
  have hmean := rareUnbiased_mean μ α a ρ hα ha ha' hρ hρ1 hm q hq
  unfold rareAverage
  rw [BlindUpper.productionAverage_mse _ _ (rareUnbiasedProcedure a ρ).measurable_output hY,
    hmean,sub_self,zero_pow (by norm_num : (2 : ℕ) ≠ 0),add_zero]
  apply ENNReal.ofReal_le_ofReal
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact (variance_le_expectation_sq (rareUnbiasedProcedure a ρ).measurable_output.aestronglyMeasurable).trans
    (rareUnbiased_second_moment μ α a ρ hα ha ha' hρ hρ1 hm q hq)

def rareArrayWork (a ρ : ℝ) (n : ℕ) (z : ℕ → ℕ × (ℕ → Bool)) : ℝ≥0∞ :=
  ∑ i : Fin (n+1), stoppedProcedureWork (rareUnbiasedProcedure a ρ) (z i.val)

theorem rareArrayWork_bound (μ : Measure Gap) [IsProbabilityMeasure μ] (q : SignLaw)
    (a ρ W : ℝ) (hwork : (∫⁻ z, stoppedProcedureWork (rareUnbiasedProcedure a ρ) z
      ∂samplingMeasure (originalPopulationTapeLaw μ q)) ≤ ENNReal.ofReal W) (n : ℕ) :
    (∫⁻ z, rareArrayWork a ρ n z
      ∂Measure.infinitePi (fun _ : ℕ => samplingMeasure (originalPopulationTapeLaw μ q))) ≤
      ENNReal.ofReal (((n : ℝ)+1)*(W)) := by
  have he (i : Fin (n+1)) :
      (∫⁻ z : ℕ → ℕ × (ℕ → Bool), stoppedProcedureWork (rareUnbiasedProcedure a ρ) (z i.val)
        ∂Measure.infinitePi (fun _ : ℕ => samplingMeasure (originalPopulationTapeLaw μ q))) =
      ∫⁻ z, stoppedProcedureWork (rareUnbiasedProcedure a ρ) z ∂samplingMeasure (originalPopulationTapeLaw μ q) :=
    (measurePreserving_eval_infinitePi (fun _ : ℕ => samplingMeasure (originalPopulationTapeLaw μ q)) i.val).lintegral_comp
      (measurable_stoppedProcedureWork (rareUnbiasedProcedure a ρ))
  unfold rareArrayWork
  have hf (i : Fin (n+1)) : Measurable
      (fun z : ℕ → ℕ × (ℕ → Bool) => stoppedProcedureWork (rareUnbiasedProcedure a ρ) (z i.val)) :=
    (measurable_stoppedProcedureWork (rareUnbiasedProcedure a ρ)).comp (measurable_pi_apply i.val)
  rw [lintegral_finsetSum Finset.univ (fun i _ => hf i)]
  simp_rw [he]
  calc
    _ ≤ ∑ _i : Fin (n+1), ENNReal.ofReal (W) :=
      Finset.sum_le_sum (fun _ _ => hwork)
    _ = _ := by
      simp [ENNReal.ofReal_mul (by positivity : 0 ≤ (n : ℝ)+1),ENNReal.ofReal_add,
        ENNReal.ofReal_natCast]

end ThresholdHC.RareAboveTwo
