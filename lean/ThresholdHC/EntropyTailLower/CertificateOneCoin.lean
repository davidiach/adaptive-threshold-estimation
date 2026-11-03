import ThresholdHC.EntropyTailLower.CertificateCentering
import ThresholdHC.EntropyTailLower.FlowOneCoin
import ThresholdHC.EntropyTail.Objective

/-! Large certificate bias already controls the capped selection cost.
Small bias gives positive intensity and an actual one-coin guarantee with
moment/work product at most four times budget times certificate variance.
Localization and entropy-tail packing remain separate obligations. -/

noncomputable section
namespace ThresholdHC.EntropyTailLower
open MeasureTheory Real
open scoped ENNReal
open ThresholdHC.Tier6 ThresholdHC.RareAboveTwo ThresholdHC.StoppingProgram
open ThresholdHC.CriticalEntropy ThresholdHC.ObservableSimulation ThresholdHC.CapIdentification

theorem certificate_bias_le_root {N : ℕ} (C : Certificate N)
    (hb : 0 ≤ C.bias) (hv : 0 ≤ C.variance) :
    ENNReal.ofReal C.bias ≤ certificateSquared C ^ (1/2:ℝ) := by
  rw [certificateSquared,ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num),← Real.sqrt_eq_rpow]
  apply ENNReal.ofReal_le_ofReal
  calc
    C.bias = sqrt (C.bias^2) := (sqrt_sq hb).symm
    _ ≤ _ := sqrt_le_sqrt (by linarith)

theorem certificate_large_bias_lower {N : ℕ} (μ : Measure Gap) (ρ B : ℝ)
    (C : Certificate N) (hb : 0 ≤ C.bias) (hv : 0 ≤ C.variance) (hlarge : ρ/128 ≤ C.bias) :
    ENNReal.ofReal (1/128:ℝ)*ThresholdHC.EntropyTail.selection μ ρ B ≤ certificateSquared C ^ (1/2:ℝ) := by
  apply le_trans (mul_le_mul' le_rfl (ThresholdHC.EntropyTail.selection_le_rho μ ρ B))
  rw [← ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 1/128)]
  exact (ENNReal.ofReal_le_ofReal (by linarith)).trans (certificate_bias_le_root C hb hv)

theorem certificate_one_coin_guarantee {N : ℕ} (μ : Measure Gap) [IsProbabilityMeasure μ]
    (ρ B : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hN : 0 < N)
    (C : Certificate N) (hC : Feasible μ ρ B C) (hb : C.bias ≤ ρ/128) :
    0 < intensity C.flow ∧
    let f := (centeredCertificate μ C).flow
    let ν := flowCoinSeedLaw f
    let A := flowCoinProcedure hN f
    IsProbabilityMeasure ν ∧
      CappedPopulationGuarantee μ ν (gapParameter false) (gapParameter true) A ρ (4*intensity C.flow*C.variance) ∧
      ∀ q, CappedPrior μ ρ q → populationExpectedWork μ ν (gapParameter false) (gapParameter true) q A ≤
        ENNReal.ofReal (B/intensity C.flow) := by
  have hi : 0 < intensity C.flow := by
    rcases certificate_large_bias_or_positive_intensity μ ρ B hρ.le hρ1 C hC with hh | hh
    · linarith
    · exact hh
  refine ⟨hi,?_⟩
  let D := centeredCertificate μ C
  let f := D.flow
  let ν := flowCoinSeedLaw f
  let A := flowCoinProcedure hN f
  have hD : Feasible μ ρ B D := centeredCertificate_feasible μ ρ B hρ.le C hC hi
  have hif : intensity f = intensity C.flow := rfl
  have hsign (q : Gap → unitInterval) (hq : CappedPrior μ ρ q) :
      ∃ q' : SignLaw, signUnit q' = q ∧ RarePrior μ ρ q' := by
    let q' : SignLaw := ⟨fun d => (q d:ℝ),measurable_subtype_coe.comp hq.1,fun d => (q d).property⟩
    exact ⟨q',rfl,hq.2.2⟩
  have hw (q : Gap → unitInterval) (hq : CappedPrior μ ρ q) :
      populationExpectedWork μ ν (gapParameter false) (gapParameter true) q A ≤ ENNReal.ofReal (B/intensity C.flow) := by
    obtain ⟨q',rfl,hq'⟩ := hsign q hq
    rw [flowCoinProcedure_population_work μ q' hN f hD.cone (by rwa [hif])]
    apply ENNReal.ofReal_le_ofReal
    rw [hif]
    exact div_le_div_of_nonneg_right (hD.work_bound q' hq') hi.le
  refine ⟨flowCoinSeedLaw_probability f hD.cone,⟨?_,?_,?_⟩,hw⟩
  · intro q hq
    obtain ⟨q',rfl,hq'⟩ := hsign q hq
    apply (flowCoinProcedure_population_moment μ q' hN f hD.cone).trans
    apply ENNReal.ofReal_le_ofReal
    have hh := mul_le_mul_of_nonneg_left (hD.variance_bound q' hq')
      (show 0 ≤ intensity f by rw [hif]; exact hi.le)
    change intensity f*countMean μ q' f.momentWeight ≤ intensity f*(4*C.variance) at hh
    rw [hif] at hh ⊢
    nlinarith only [hh]
  · intro q hq
    exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hw q hq)
  · intro q hq
    obtain ⟨q',rfl,hq'⟩ := hsign q hq
    rw [flowCoinProcedure_population_mean μ q' hN f hD.cone]
    have hh := hD.bias_bound q' hq'
    change |0+countMean μ q' f.outputWeight-signMean μ q'.val| ≤ 2*C.bias at hh
    simp only [zero_add] at hh
    exact hh.trans (by linarith)

theorem certificate_one_coin_tradeoff {N : ℕ} (μ : Measure Gap) [IsProbabilityMeasure μ]
    (ρ B : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hN : 0 < N)
    (C : Certificate N) (hC : Feasible μ ρ B C) (hb : C.bias ≤ ρ/128) :
    let f := (centeredCertificate μ C).flow
    let ν := flowCoinSeedLaw f
    let A := flowCoinProcedure hN f
    (4*intensity C.flow*C.variance)*
      (populationExpectedWork μ ν (gapParameter false) (gapParameter true) (fun _ => 0) A).toReal ≤
        4*B*C.variance := by
  have h := certificate_one_coin_guarantee μ ρ B hρ hρ1 hN C hC hb
  have hnull : RarePrior μ ρ nullSignLaw := by simpa [RarePrior,signMean,nullSignLaw] using hρ.le
  have hB : 0 ≤ B := (countMean_nonneg μ nullSignLaw C.flow.continueWeight hC.cone.continue_nonneg).trans
    (hC.work_bound nullSignLaw hnull)
  have hq : CappedPrior μ ρ (fun _ => 0) := ⟨measurable_const,fun _ => by norm_num,by simpa using hρ.le⟩
  have hW := ENNReal.toReal_mono ENNReal.ofReal_ne_top (h.2.2.2 _ hq)
  rw [ENNReal.toReal_ofReal (div_nonneg hB h.1.le)] at hW
  calc
    _ ≤ (4*intensity C.flow*C.variance)*(B/intensity C.flow) :=
      mul_le_mul_of_nonneg_left hW (mul_nonneg (mul_nonneg (by norm_num) h.1.le) hC.variance_nonneg)
    _ = _ := by field_simp [h.1.ne']

end ThresholdHC.EntropyTailLower
