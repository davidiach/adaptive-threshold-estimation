import ThresholdHC.EntropyTailLower.CertificateOneCoin
import ThresholdHC.EntropyTailLower.PopulationPullback

/-! The actual one-coin certificate construction and the gated annular
bound combine on arbitrary small-gap probability laws. This is a
single-component obstruction, not the final entropy-tail lower bound. -/

noncomputable section
namespace ThresholdHC.EntropyTailLower
open MeasureTheory Set Real
open scoped ENNReal
open ThresholdHC.CriticalEntropy ThresholdHC.Tier6 ThresholdHC.StoppingProgram ThresholdHC.ObservableSimulation

theorem certificate_gated_annular_saturation {N : ℕ}
    (μ : Measure EntropyGap) [IsProbabilityMeasure μ]
    (ρ B : ℝ) (hρ : 0 < ρ) (hρ4 : ρ ≤ 1/4) (hN : 0 < N)
    (C : Certificate N) (hC : Feasible (μ.map entropyGapInclusion) ρ B C) (hbias : C.bias ≤ ρ/128)
    (a : ℝ) (ha : 0 < a) (ha4 : a ≤ 1/4) (hclose : ∀ᵐ (d : EntropyGap) ∂μ, (d:ℝ) ≤ a)
    {K : ℕ} (I : Fin K → Set EntropyGap) (b : Fin K → ℝ)
    (hb : ∀ i, 0 < b i) (hI : ∀ i, MeasurableSet (I i))
    (hdisjoint : Pairwise (fun i j => Disjoint (I i) (I j)))
    (hband : ∀ i d, d ∈ I i → b i/2 < (d:ℝ) ∧ (d:ℝ) ≤ b i)
    (hsep : ∀ i j, j.val = i.val+1 → 4*b j ≤ b i)
    (s : ℝ) (hs1 : s ≤ 1) (hmass : ∀ i, s ≤ μ.real (I i)) :
    min (s/a^2) (ρ*ThresholdHC.EntropyTailQuantile.costEntropy (fun i => μ.real (I i)/(b i)^2)) ≤
      4294967296*exp 48*B*C.variance := by
  let μg := μ.map entropyGapInclusion
  have hemb := entropyGapInclusion_measurableEmbedding
  let : IsProbabilityMeasure μg := (Measure.isProbabilityMeasure_map_iff hemb.measurable.aemeasurable).mpr inferInstance
  have hρ1 : ρ ≤ 1 := by linarith
  have hc := certificate_one_coin_guarantee μg ρ B hρ hρ1 hN C hC hbias
  let f := (centeredCertificate μg C).flow
  let ν := flowCoinSeedLaw f
  let A := flowCoinProcedure hN f
  let m := 4*intensity C.flow*C.variance
  let : IsProbabilityMeasure ν := hc.2.1
  have hm : 0 ≤ m := mul_nonneg (mul_nonneg (by norm_num) hc.1.le) hC.variance_nonneg
  have hguar := cappedGuarantee_pullback μ ν entropyGapInclusion hemb
    (gapParameter false) (gapParameter true) (measurable_gapParameter false) (measurable_gapParameter true)
    A ρ m hc.2.2.1
  rw [entropyGapInclusion_parameter false,entropyGapInclusion_parameter true] at hguar
  have hW : populationExpectedWork μg ν (gapParameter false) (gapParameter true) (fun _ => 0) A =
      populationExpectedWork μ ν (fun d => signParameter d false) (fun d => signParameter d true) (fun _ => 0) A := by
    have h := population_lintegral_map μ ν entropyGapInclusion hemb.measurable
      (gapParameter false) (gapParameter true) (fun _ => 0)
      (measurable_gapParameter false) (measurable_gapParameter true) measurable_const
      (stoppedProcedureWork A) (measurable_stoppedProcedureWork A)
    rw [entropyGapInclusion_parameter false,entropyGapInclusion_parameter true] at h
    exact h
  have ht := certificate_one_coin_tradeoff μg ρ B hρ hρ1 hN C hC hbias
  change m*(populationExpectedWork μg ν (gapParameter false) (gapParameter true) (fun _ => 0) A).toReal ≤
    4*B*C.variance at ht
  rw [hW] at ht
  let r : unitInterval := ⟨ρ,hρ.le,hρ1⟩
  have hAnn := population_gated_annular_saturation μ ν A r hρ hρ4 m hm hguar
    a ha ha4 hclose I b hb hI hdisjoint hband hsep s hs1 hmass
  calc
    _ ≤ _ := hAnn
    _ = (1073741824*exp 48)*(m*(populationExpectedWork μ ν
        (fun d => signParameter d false) (fun d => signParameter d true) (fun _ => 0) A).toReal) := by ring
    _ ≤ (1073741824*exp 48)*(4*B*C.variance) := mul_le_mul_of_nonneg_left ht (by positivity)
    _ = _ := by ring

end ThresholdHC.EntropyTailLower
