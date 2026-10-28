import ThresholdHC.CriticalUpper.Unbiased

/-! Expected actual flip count, including the unbounded geometric level. -/

noncomputable section
namespace ThresholdHC.CriticalUpper
open MeasureTheory Set ThresholdHC.CriticalEntropy ThresholdHC.Uniform713
open scoped ENNReal
open scoped ENNReal

theorem calibratedCost_population_work (ρ : ℝ) (j : ℕ)
    (q : ℝ → unitInterval) (hq : Measurable q) :
    populationExpectedWork criticalGapLaw (Measure.dirac ())
      (fun d => criticalParameter d false) (fun d => criticalParameter d true) q (calibratedScreen ρ j) =
      ∫⁻ ω, ENNReal.ofReal (calibratedCost ρ j ω : ℝ) ∂criticalTapeLaw q := by
  let := criticalTapeLaw_probability q hq
  rw [populationInput_work criticalGapLaw (Measure.dirac ()) _ _ q
    (measurable_criticalParameter false) (measurable_criticalParameter true) hq]
  change (∫⁻ z, stoppedProcedureWork (calibratedScreen ρ j) z
    ∂(Measure.dirac ()).prod (criticalTapeLaw q)) = _
  have he : stoppedProcedureWork (calibratedScreen ρ j) =
      fun z : Unit × (ℕ → Bool) => ENNReal.ofReal (calibratedCost ρ j z.2 : ℝ) := by
    funext z
    simp [calibratedScreen,screenProcedure,stoppedProcedureWork,BlindUpper.finiteStoppedProcedure,calibratedCost]
  have hf : Measurable (fun z : Unit × (ℕ → Bool) => ENNReal.ofReal (calibratedCost ρ j z.2 : ℝ)) :=
    ENNReal.measurable_ofReal.comp
    ((measurable_of_countable (fun n : ℕ => (n : ℝ))).comp
      ((measurable_calibratedCost ρ j).comp measurable_snd))
  rw [he,lintegral_prod _ hf.aemeasurable]
  simp

theorem coupledCost_population_bound (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (q : ℝ → unitInterval) (hq : Measurable q)
    (hmass : (∫ d, (q d : ℝ) ∂criticalGapLaw) ≤ ρ) (j : ℕ) :
    (∫⁻ ω, ENNReal.ofReal (coupledCost ρ j ω : ℝ) ∂criticalTapeLaw q) ≤
      ENNReal.ofReal (1000000*criticalLogFactor ρ*((j : ℝ)+1)^2) := by
  have hL := (criticalLogFactor_pos ρ hρ hρ1).le
  have hb (k : ℕ) := calibratedScreen_work ρ hρ hρ1 k q hq hmass
  simp_rw [calibratedCost_population_work ρ _ q hq] at hb
  cases j with
  | zero =>
    apply (hb 0).trans
    apply ENNReal.ofReal_le_ofReal
    norm_num
    linarith
  | succ j =>
    calc
      _ ≤ ∫⁻ ω, ENNReal.ofReal (calibratedCost ρ (j+1) ω : ℝ)+
          ENNReal.ofReal (calibratedCost ρ j ω : ℝ) ∂criticalTapeLaw q := by
        apply lintegral_mono
        intro ω
        dsimp only
        rw [← ENNReal.ofReal_add (by positivity : 0 ≤ (calibratedCost ρ (j+1) ω : ℝ))
          (by positivity : 0 ≤ (calibratedCost ρ j ω : ℝ))]
        exact ENNReal.ofReal_le_ofReal (by exact_mod_cast coupledCost_succ_le ρ j ω)
      _ = (∫⁻ ω, ENNReal.ofReal (calibratedCost ρ (j+1) ω : ℝ) ∂criticalTapeLaw q)+
          (∫⁻ ω, ENNReal.ofReal (calibratedCost ρ j ω : ℝ) ∂criticalTapeLaw q) := by
        apply lintegral_add_left
        exact ENNReal.measurable_ofReal.comp
          ((measurable_of_countable (fun n : ℕ => (n : ℝ))).comp (measurable_calibratedCost ρ (j+1)))
      _ ≤ ENNReal.ofReal (500000*criticalLogFactor ρ*((j+1 : ℕ)+1)^2)+
          ENNReal.ofReal (500000*criticalLogFactor ρ*((j : ℝ)+1)^2) := add_le_add (hb (j+1)) (hb j)
      _ ≤ _ := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
        apply ENNReal.ofReal_le_ofReal
        push_cast
        have hn : 0 ≤ (j : ℝ) := Nat.cast_nonneg j
        have hsq : ((j : ℝ)+1)^2 ≤ ((j : ℝ)+2)^2 := by nlinarith
        nlinarith [mul_le_mul_of_nonneg_left hsq (by positivity : 0 ≤ 500000*criticalLogFactor ρ)]

theorem hasSum_work_geometric :
    HasSum (fun j : ℕ => (3/4 : ℝ)^j*((j : ℝ)+1)^2) 112 := by
  have h : ‖(3/4 : ℝ)‖ < 1 := by norm_num
  convert ((hasSum_sq_mul_geometric_of_norm_lt_one h).add
    ((hasSum_coe_mul_geometric_of_norm_lt_one h).mul_left 2)).add
      (hasSum_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 3/4) (by norm_num)) using 1
  · funext j
    ring
  · norm_num

theorem lintegral_levelMeasure (F : ℕ → ℝ≥0∞) :
    (∫⁻ j, F j ∂levelMeasure) = ∑' j, ENNReal.ofReal (levelProb j)*F j := by
  simp only [levelMeasure,lintegral_sum_measure,lintegral_smul_measure,lintegral_dirac,smul_eq_mul]

theorem criticalUnbiased_expected_work (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (q : ℝ → unitInterval) (hq : Measurable q)
    (hmass : (∫ d, (q d : ℝ) ∂criticalGapLaw) ≤ ρ) :
    (∫⁻ z, stoppedProcedureWork (criticalUnbiasedProcedure ρ) z ∂samplingMeasure (criticalTapeLaw q)) ≤
      ENNReal.ofReal (112000000*criticalLogFactor ρ) := by
  let := criticalTapeLaw_probability q hq
  have hL := (criticalLogFactor_pos ρ hρ hρ1).le
  unfold samplingMeasure
  rw [lintegral_prod _ (measurable_stoppedProcedureWork _).aemeasurable]
  simp_rw [criticalUnbiasedProcedure_work]
  rw [lintegral_levelMeasure]
  calc
    _ ≤ ∑' j : ℕ, ENNReal.ofReal (1000000*criticalLogFactor ρ*((3/4 : ℝ)^j*((j : ℝ)+1)^2)) := by
      apply ENNReal.tsum_le_tsum
      intro j
      calc
        _ ≤ ENNReal.ofReal (levelProb j)*ENNReal.ofReal (1000000*criticalLogFactor ρ*((j : ℝ)+1)^2) :=
          mul_le_mul' le_rfl (coupledCost_population_bound ρ hρ hρ1 q hq hmass j)
        _ = ENNReal.ofReal (levelProb j*(1000000*criticalLogFactor ρ*((j : ℝ)+1)^2)) := by
          rw [ENNReal.ofReal_mul (levelProb_pos j).le]
        _ ≤ _ := by
          apply ENNReal.ofReal_le_ofReal
          have h := mul_le_mul_of_nonneg_right (levelProb_upper j)
            (by positivity : 0 ≤ 1000000*criticalLogFactor ρ*((j : ℝ)+1)^2)
          nlinarith only [h]
    _ = _ := by
      rw [← ENNReal.ofReal_tsum_of_nonneg (fun j => by positivity)
        (hasSum_work_geometric.mul_left (1000000*criticalLogFactor ρ)).summable,
        (hasSum_work_geometric.mul_left (1000000*criticalLogFactor ρ)).tsum_eq]
      congr 1
      ring

end ThresholdHC.CriticalUpper
