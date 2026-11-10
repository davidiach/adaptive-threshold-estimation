import ThresholdHC.ArbitraryLawAdaptation.CouplingEntropy

/-! Lift every fractional submeasure to a subcoupling by its Radon--Nikodym
density, then push it to the larger-gap marginal. -/

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace ThresholdHC.ArbitraryLawAdaptation
open ThresholdHC.Tier6 (Gap)
open ThresholdHC.EntropyTail

def selectionLift (π : Measure (Gap × Gap)) (σ : Measure Gap) : Measure (Gap × Gap) :=
  π.withDensity (fun z => σ.rnDeriv (π.map Prod.fst) z.1)

def transportedSelection (π : Measure (Gap × Gap)) (σ : Measure Gap) : Measure Gap :=
  (selectionLift π σ).map Prod.snd

theorem map_withDensity_comp {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    (π : Measure Ω) {g : Ω → E} (hg : Measurable g) {w : E → ℝ≥0∞} (hw : Measurable w) :
    (π.withDensity (fun z => w (g z))).map g = (π.map g).withDensity w := by
  ext s hs
  rw [Measure.map_apply hg hs, withDensity_apply _ (hg hs),
    withDensity_apply _ hs, setLIntegral_map hs hw hg]

theorem selectionLift_first (π : Measure (Gap × Gap)) [IsFiniteMeasure π]
    {σ : Measure Gap} (hσ : σ ≤ π.map Prod.fst) :
    (selectionLift π σ).map Prod.fst = σ := by
  have : IsFiniteMeasure σ := isFiniteMeasure_of_le (π.map Prod.fst) hσ
  rw [selectionLift, map_withDensity_comp π measurable_fst (Measure.measurable_rnDeriv _ _),
    Measure.withDensity_rnDeriv_eq _ _ (Measure.absolutelyContinuous_of_le hσ)]

theorem selectionLift_le (π : Measure (Gap × Gap)) [IsFiniteMeasure π]
    {σ : Measure Gap} (hσ : σ ≤ π.map Prod.fst) : selectionLift π σ ≤ π := by
  have h := ae_of_ae_map measurable_fst.aemeasurable (Measure.rnDeriv_le_one_of_le hσ)
  have h' : (fun z : Gap × Gap => σ.rnDeriv (π.map Prod.fst) z.1) ≤ᵐ[π] 1 := h
  exact (withDensity_mono h').trans_eq withDensity_one

theorem transportedSelection_le (π : Measure (Gap × Gap)) [IsFiniteMeasure π]
    {σ : Measure Gap} (hσ : σ ≤ π.map Prod.fst) :
    transportedSelection π σ ≤ π.map Prod.snd :=
  Measure.map_mono (selectionLift_le π hσ) measurable_snd

theorem transportedSelection_mass (π : Measure (Gap × Gap)) [IsFiniteMeasure π]
    {σ : Measure Gap} (hσ : σ ≤ π.map Prod.fst) :
    transportedSelection π σ Set.univ = σ Set.univ := by
  have hf := congrArg (fun μ : Measure Gap => μ Set.univ) (selectionLift_first π hσ)
  simpa only [transportedSelection, Measure.map_apply measurable_fst MeasurableSet.univ,
    Measure.map_apply measurable_snd MeasurableSet.univ, Set.preimage_univ] using hf

theorem map_sub_of_le {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    {π ξ : Measure Ω} [IsFiniteMeasure ξ] (hξ : ξ ≤ π) {g : Ω → E} (hg : Measurable g) :
    (π-ξ).map g = π.map g-ξ.map g := by
  have h := congrArg (fun μ : Measure Ω => μ.map g) (Measure.sub_add_cancel_of_le hξ)
  rw [Measure.map_add _ _ hg] at h
  rw [← h, Measure.add_sub_cancel]

theorem tailCost_increasing_coupling (π : Measure (Gap × Gap))
    (hup : ∀ᵐ z ∂π, (z.1 : ℝ) ≤ (z.2 : ℝ)) {h : ℝ} (hh : 0 ≤ h) :
    tailCost (π.map Prod.snd) h ≤ tailCost (π.map Prod.fst) h := by
  rw [tailCost, tailCost, lintegral_map (measurable_tailWeight h) measurable_snd,
    lintegral_map (measurable_tailWeight h) measurable_fst]
  apply lintegral_mono_ae
  filter_upwards [hup] with z hz
  exact ENNReal.ofReal_le_ofReal
    (min_le_min_left _ (div_le_div_of_nonneg_left hh z.1.property.1 hz))

theorem transportedSelection_costs (π : Measure (Gap × Gap)) [IsFiniteMeasure π]
    (hup : ∀ᵐ z ∂π, (z.1 : ℝ) ≤ (z.2 : ℝ))
    {σ : Measure Gap} (hσ : σ ≤ π.map Prod.fst) {h : ℝ} (hh : 0 ≤ h) :
    gamma (transportedSelection π σ) ≤ 3*gamma σ ∧
      tailCost (π.map Prod.snd-transportedSelection π σ) h ≤
        tailCost (π.map Prod.fst-σ) h := by
  have hξ := selectionLift_le π hσ
  have : IsFiniteMeasure (selectionLift π σ) := isFiniteMeasure_of_le π hξ
  have hupξ := (Measure.absolutelyContinuous_of_le hξ).ae_le hup
  have hupres := (Measure.absolutelyContinuous_of_le (Measure.sub_le : π-selectionLift π σ ≤ π)).ae_le hup
  constructor
  · simpa only [selectionLift_first π hσ, transportedSelection] using
      gamma_le_three_of_increasing_coupling (selectionLift π σ) hupξ
  · have ht := tailCost_increasing_coupling (π-selectionLift π σ) hupres hh
    rw [map_sub_of_le hξ measurable_fst, selectionLift_first π hσ,
      map_sub_of_le hξ measurable_snd] at ht
    exact ht

end ThresholdHC.ArbitraryLawAdaptation
