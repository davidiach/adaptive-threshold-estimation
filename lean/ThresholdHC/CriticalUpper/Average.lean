import ThresholdHC.CriticalUpper.UnbiasedPopulation
import ThresholdHC.BlindUpper.ProductionAverage
import ThresholdHC.BlindUpper.InfiniteArrays

/-! Independent calls: exact seed pairing, averaging error and summed actual work. -/

noncomputable section
namespace ThresholdHC.CriticalUpper
open MeasureTheory ProbabilityTheory ThresholdHC.CriticalEntropy ThresholdHC.Uniform713
open scoped ENNReal

abbrev CriticalSeed := ℕ → ℕ

def criticalSeedLaw : Measure CriticalSeed := Measure.infinitePi (fun _ : ℕ => levelMeasure)

instance criticalSeedLaw_probability : IsProbabilityMeasure criticalSeedLaw := by
  unfold criticalSeedLaw
  infer_instance

def criticalCalls (z : CriticalSeed × (ℕ → ℕ → Bool)) : ℕ → ℕ × (ℕ → Bool) :=
  fun i => (z.1 i,z.2 i)

theorem measurable_criticalCalls : Measurable criticalCalls := by
  exact Measurable.of_eval (fun i => ((measurable_pi_apply i).comp measurable_fst).prodMk
    ((measurable_pi_apply i).comp measurable_snd))

theorem criticalCalls_preserving (q : ℝ → unitInterval) (hq : Measurable q) :
    MeasurePreserving criticalCalls
      (criticalSeedLaw.prod (Measure.infinitePi (fun _ : ℕ => criticalTapeLaw q)))
      (Measure.infinitePi (fun _ : ℕ => samplingMeasure (criticalTapeLaw q))) := by
  let := criticalTapeLaw_probability q hq
  exact ⟨measurable_criticalCalls,BlindUpper.infinitePi_zip
    (fun _ : ℕ => levelMeasure) (fun _ : ℕ => criticalTapeLaw q)⟩

def criticalAverage (ρ : ℝ) (n : ℕ) :=
  BlindUpper.productionAverage (criticalUnbiasedProcedure ρ).output n

theorem criticalAverage_mse (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (q : ℝ → unitInterval) (hq : Measurable q)
    (hmass : (∫ d, (q d : ℝ) ∂criticalGapLaw) ≤ ρ) (n : ℕ) :
    (∫⁻ z, ENNReal.ofReal ((criticalAverage ρ n z-(∫ d, (q d : ℝ) ∂criticalGapLaw))^2)
      ∂Measure.infinitePi (fun _ : ℕ => samplingMeasure (criticalTapeLaw q))) ≤
      ENNReal.ofReal (28*ρ/((n : ℝ)+1)) := by
  let := criticalTapeLaw_probability q hq
  have hY := criticalUnbiased_memLp ρ hρ hρ1 q hq hmass
  have hm := criticalUnbiased_mean ρ hρ hρ1 q hq hmass
  unfold criticalAverage
  rw [BlindUpper.productionAverage_mse _ _ (criticalUnbiasedProcedure ρ).measurable_output hY,
    hm,sub_self,zero_pow (by norm_num : (2 : ℕ) ≠ 0),add_zero]
  apply ENNReal.ofReal_le_ofReal
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact (variance_le_expectation_sq (criticalUnbiasedProcedure ρ).measurable_output.aestronglyMeasurable).trans
    (criticalUnbiased_second_moment ρ hρ hρ1 q hq hmass)

def criticalArrayWork (ρ : ℝ) (n : ℕ) (z : ℕ → ℕ × (ℕ → Bool)) : ℝ≥0∞ :=
  ∑ i : Fin (n+1), stoppedProcedureWork (criticalUnbiasedProcedure ρ) (z i.val)

theorem criticalArrayWork_bound (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (q : ℝ → unitInterval) (hq : Measurable q)
    (hmass : (∫ d, (q d : ℝ) ∂criticalGapLaw) ≤ ρ) (n : ℕ) :
    (∫⁻ z, criticalArrayWork ρ n z
      ∂Measure.infinitePi (fun _ : ℕ => samplingMeasure (criticalTapeLaw q))) ≤
      ENNReal.ofReal (((n : ℝ)+1)*(112000000*criticalLogFactor ρ)) := by
  let := criticalTapeLaw_probability q hq
  have he (i : Fin (n+1)) :
      (∫⁻ z : ℕ → ℕ × (ℕ → Bool), stoppedProcedureWork (criticalUnbiasedProcedure ρ) (z i.val)
        ∂Measure.infinitePi (fun _ : ℕ => samplingMeasure (criticalTapeLaw q))) =
      ∫⁻ z, stoppedProcedureWork (criticalUnbiasedProcedure ρ) z ∂samplingMeasure (criticalTapeLaw q) :=
    (measurePreserving_eval_infinitePi (fun _ : ℕ => samplingMeasure (criticalTapeLaw q)) i.val).lintegral_comp
      (measurable_stoppedProcedureWork (criticalUnbiasedProcedure ρ))
  unfold criticalArrayWork
  have hf (i : Fin (n+1)) : Measurable
      (fun z : ℕ → ℕ × (ℕ → Bool) => stoppedProcedureWork (criticalUnbiasedProcedure ρ) (z i.val)) :=
    (measurable_stoppedProcedureWork (criticalUnbiasedProcedure ρ)).comp (measurable_pi_apply i.val)
  rw [lintegral_finsetSum Finset.univ (fun i _ => hf i)]
  simp_rw [he]
  calc
    _ ≤ ∑ _i : Fin (n+1), ENNReal.ofReal (112000000*criticalLogFactor ρ) :=
      Finset.sum_le_sum (fun _ _ => criticalUnbiased_expected_work ρ hρ hρ1 q hq hmass)
    _ = _ := by
      simp [ENNReal.ofReal_mul (by positivity : 0 ≤ (n : ℝ)+1),ENNReal.ofReal_add,
        ENNReal.ofReal_natCast]

end ThresholdHC.CriticalUpper
