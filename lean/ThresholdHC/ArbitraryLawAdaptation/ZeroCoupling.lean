import ThresholdHC.ArbitraryLawAdaptation.ZeroModel

/-! Increasing-gap entropy and tail transport with unresolved mass at zero. -/

noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace ThresholdHC.ArbitraryLawAdaptation
open ThresholdHC.Tier6 (Gap)
open ThresholdHC.EntropyTail

def pairGapMap (z : Gap × Gap) : ℝ × ℝ := (z.1.val, z.2.val)

theorem pairGapEmbedding : MeasurableEmbedding pairGapMap :=
  gapEmbedding.prodMap gapEmbedding

theorem pairGap_comap_map (π : Measure (ℝ × ℝ))
    (hpos : ∀ᵐ z ∂π, z.1 ∈ Ioc 0 (1/2) ∧ z.2 ∈ Ioc 0 (1/2)) :
    (π.comap pairGapMap).map pairGapMap = π := by
  rw [pairGapEmbedding.map_comap]
  apply Measure.restrict_eq_self_of_ae_mem
  filter_upwards [hpos] with z hz
  exact ⟨(⟨z.1, hz.1⟩, ⟨z.2, hz.2⟩), rfl⟩

theorem pairGap_comap_marginals (π : Measure (ℝ × ℝ))
    (hpos : ∀ᵐ z ∂π, z.1 ∈ Ioc 0 (1/2) ∧ z.2 ∈ Ioc 0 (1/2)) :
    (π.comap pairGapMap).map Prod.fst = positivePart (π.map Prod.fst) ∧
      (π.comap pairGapMap).map Prod.snd = positivePart (π.map Prod.snd) := by
  have he := pairGap_comap_map π hpos
  constructor
  · have hm : ((π.comap pairGapMap).map Prod.fst).map Subtype.val = π.map Prod.fst := by
      rw [Measure.map_map measurable_subtype_coe measurable_fst]
      conv_rhs => rw [← he, Measure.map_map measurable_fst pairGapEmbedding.measurable]
      rfl
    have h := congrArg positivePart hm
    simpa only [positivePart_map] using h
  · have hm : ((π.comap pairGapMap).map Prod.snd).map Subtype.val = π.map Prod.snd := by
      rw [Measure.map_map measurable_subtype_coe measurable_snd]
      conv_rhs => rw [← he, Measure.map_map measurable_snd pairGapEmbedding.measurable]
      rfl
    have h := congrArg positivePart hm
    simpa only [positivePart_map] using h

theorem zeroGamma_increasing_coupling (π : Measure (ℝ × ℝ)) [IsFiniteMeasure π]
    (hclosed : ∀ᵐ z ∂π, z.1 ∈ Icc 0 (1/2) ∧ z.2 ∈ Icc 0 (1/2))
    (hup : ∀ᵐ z ∂π, z.1 ≤ z.2) :
    zeroGamma (π.map Prod.snd) ≤ 3*zeroGamma (π.map Prod.fst) := by
  by_cases hz : (π.map Prod.fst) {0} = 0
  · have hn : ∀ᵐ z ∂π, z.1 ≠ 0 := by
      have h := (measure_eq_zero_iff_ae_notMem).mp hz
      exact ae_of_ae_map measurable_fst.aemeasurable h
    have hpos : ∀ᵐ z ∂π, z.1 ∈ Ioc 0 (1/2) ∧ z.2 ∈ Ioc 0 (1/2) := by
      filter_upwards [hclosed, hup, hn] with z hc hu hnz
      have hp : 0 < z.1 := lt_of_le_of_ne hc.1.1 (Ne.symm hnz)
      exact ⟨⟨hp, hc.1.2⟩, ⟨hp.trans_le hu, hc.2.2⟩⟩
    have hzn : (π.map Prod.snd) {0} = 0 := by
      rw [measure_eq_zero_iff_ae_notMem]
      apply (ae_map_iff measurable_snd.aemeasurable (measurableSet_singleton 0).compl).mpr
      filter_upwards [hpos] with z hp
      exact ne_of_gt hp.2.1
    have hu : ∀ᵐ z ∂π.comap pairGapMap, (z.1 : ℝ) ≤ (z.2 : ℝ) := by
      rw [← pairGap_comap_map π hpos] at hup
      exact ae_of_ae_map pairGapEmbedding.measurable.aemeasurable hup
    have h := gamma_le_three_of_increasing_coupling (π.comap pairGapMap) hu
    rw [(pairGap_comap_marginals π hpos).1, (pairGap_comap_marginals π hpos).2] at h
    simpa only [zeroGamma, hz, hzn, ite_true] using h
  · rw [zeroGamma_of_atom hz]
    simp

theorem zeroTailCost_increasing_coupling (π : Measure (ℝ × ℝ))
    (hup : ∀ᵐ z ∂π, z.1 ≤ z.2) {h : ℝ} (hh : 0 ≤ h) :
    zeroTailCost (π.map Prod.snd) h ≤ zeroTailCost (π.map Prod.fst) h := by
  rw [zeroTailCost, zeroTailCost,
    lintegral_map (measurable_zeroTailWeight h) measurable_snd,
    lintegral_map (measurable_zeroTailWeight h) measurable_fst]
  exact lintegral_mono_ae (hup.mono fun _ hz => zeroTailWeight_antitone hh hz)

end ThresholdHC.ArbitraryLawAdaptation
