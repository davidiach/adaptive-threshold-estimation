import ThresholdHC.ConfidenceTransfer.CommonPairRate
import ThresholdHC.CriticalEntropy.CriticalCommonPair

noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace ThresholdHC.ConfidenceTransfer
open ThresholdHC.Tier6 ThresholdHC.CriticalEntropy ThresholdHC.ObservableSimulation

/-- The density 32d on (0,1/4], represented on the canonical domain of hidden gaps. -/
def criticalPositiveLaw : Measure Gap := Measure.comap Subtype.val criticalGapLaw

theorem criticalPositiveLaw_map : criticalPositiveLaw.map Subtype.val = criticalGapLaw := by
  refine (map_comap_subtype_coe (measurableSet_Ioc :
    MeasurableSet (Ioc (0 : ℝ) (1/2))) criticalGapLaw).trans ?_
  apply Measure.restrict_eq_self_of_ae_mem
  have hs : ∀ᵐ d ∂criticalGapLaw, d ∈ Ioc (0 : ℝ) (1/4) := ae_iff.mpr criticalGapLaw_supported
  filter_upwards [hs] with d hd using ⟨hd.1,hd.2.trans (by norm_num)⟩

instance criticalPositiveLaw_probability : IsProbabilityMeasure criticalPositiveLaw := by
  apply (Measure.isProbabilityMeasure_map_iff
    (measurable_subtype_coe : Measurable (Subtype.val : Gap → ℝ)).aemeasurable).mp
  rw [criticalPositiveLaw_map]
  infer_instance

private theorem criticalParameter_on_gap (d : Gap) (b : Bool) :
    criticalParameter d b = gapParameter b d :=
  projIcc_of_mem (by norm_num : (0 : ℝ) ≤ 1) (gapParameter b d).property

/-- Restricting the parameter type preserves the distribution of the Bernoulli
success probability, including its mixing over the unobserved sign. -/
theorem critical_parameter_law (q : ℝ → unitInterval) (hq : Measurable q) :
    populationParameterLaw criticalPositiveLaw (gapParameter false) (gapParameter true)
        (q ∘ Subtype.val) =
      populationParameterLaw criticalGapLaw (fun d => criticalParameter d false)
        (fun d => criticalParameter d true) q := by
  unfold populationParameterLaw
  conv_rhs => rw [← criticalPositiveLaw_map]
  have hp := Measure.map_prod_map criticalPositiveLaw uniformUnitMeasure
    (measurable_subtype_coe : Measurable (Subtype.val : Gap → ℝ)) measurable_id
  rw [Measure.map_id] at hp
  rw [hp,Measure.map_map (measurable_mixtureParameter _ _ _ (measurable_criticalParameter _)
    (measurable_criticalParameter _) hq) (measurable_subtype_coe.prodMap measurable_id)]
  congr 1
  funext z
  change (if z.2 < (q z.1 : ℝ) then gapParameter true z.1 else gapParameter false z.1) =
    (if z.2 < (q z.1 : ℝ) then criticalParameter z.1 true else criticalParameter z.1 false)
  rw [criticalParameter_on_gap,criticalParameter_on_gap]

def criticalSign (q : ℝ → unitInterval) (hq : Measurable q) : SignLaw :=
  ⟨fun d => (q d : ℝ), measurable_subtype_coe.comp (hq.comp measurable_subtype_coe),
   fun d => (q d).property⟩

theorem critical_sign_mean (q : ℝ → unitInterval) (hq : Measurable q) :
    signMean criticalPositiveLaw (criticalSign q hq).val = ∫ d, (q d : ℝ) ∂criticalGapLaw := by
  have hm : Measurable (fun d : ℝ => (q d : ℝ)) := measurable_subtype_coe.comp hq
  rw [← criticalPositiveLaw_map,integral_map measurable_subtype_coe.aemeasurable hm.aestronglyMeasurable]
  rfl

/-- The same critical pair controls every capped policy on the canonical gap
space, with exactly the same stopped transcript and expected null work. -/
theorem critical_local_transfer (q r : ℝ → unitInterval) (hq : Measurable q) (hr : Measurable r)
    (κ : ℝ) (h : LocalNullWorkBound criticalGapLaw (fun d => criticalParameter d false)
      (fun d => criticalParameter d true) q r κ) :
    LocalNullWorkBound criticalPositiveLaw (gapParameter false) (gapParameter true)
      (signUnit (criticalSign q hq)) (signUnit (criticalSign r hr)) κ := by
  intro R E _ _ ν _ A n hc
  have ht (s : ℝ → unitInterval) (hs : Measurable s) :
      cappedTranscriptLaw criticalPositiveLaw ν (gapParameter false) (gapParameter true)
        (signUnit (criticalSign s hs)) A n =
      cappedTranscriptLaw criticalGapLaw ν (fun d => criticalParameter d false)
        (fun d => criticalParameter d true) s A n := by
    change cappedTranscriptLaw _ _ _ _ (s ∘ Subtype.val) _ _ = _
    rw [populationInput_capped_law _ _ _ _ _ (measurable_gapParameter _)
      (measurable_gapParameter _) (hs.comp measurable_subtype_coe),
      populationInput_capped_law _ _ _ _ _ (measurable_criticalParameter _)
      (measurable_criticalParameter _) hs,critical_parameter_law s hs]
  have hw := critical_parameter_law (fun _ => 0) measurable_const
  rw [ht q hq, ht r hr, populationInput_work _ _ _ _ _ (measurable_gapParameter _)
    (measurable_gapParameter _) measurable_const]
  change populationParameterLaw criticalPositiveLaw _ _ (fun _ => 0) = _ at hw
  rw [hw,← populationInput_work _ _ _ _ _ (measurable_criticalParameter false)
    (measurable_criticalParameter true) measurable_const]
  exact h ν A n hc

/-- There is no common-pair premise in the critical-law lower bound. -/
def CriticalConfidenceLowerStatement : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ (ρ B δ : ℝ), 0 < ρ → ρ ≤ 1/4 → 0 < B → 0 < δ → δ ≤ 1/4 →
    ENNReal.ofReal (c * min ρ (Real.sqrt (ρ*criticalLogFactor ρ*Real.log (1/δ)/B))) ≤
      rareConfidenceRadius criticalPositiveLaw ρ B δ

end ThresholdHC.ConfidenceTransfer
