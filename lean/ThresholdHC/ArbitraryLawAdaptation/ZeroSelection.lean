import ThresholdHC.ArbitraryLawAdaptation.ZeroCoupling

/-! Fractional selection transport for the functional including mass at zero. -/

noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace ThresholdHC.ArbitraryLawAdaptation

def realSelectionLift (π : Measure (ℝ × ℝ)) (σ : Measure ℝ) : Measure (ℝ × ℝ) :=
  π.withDensity (fun z => σ.rnDeriv (π.map Prod.fst) z.1)

def realTransportedSelection (π : Measure (ℝ × ℝ)) (σ : Measure ℝ) : Measure ℝ :=
  (realSelectionLift π σ).map Prod.snd

theorem realSelectionLift_first (π : Measure (ℝ × ℝ)) [IsFiniteMeasure π]
    {σ : Measure ℝ} (hσ : σ ≤ π.map Prod.fst) :
    (realSelectionLift π σ).map Prod.fst = σ := by
  have : IsFiniteMeasure σ := isFiniteMeasure_of_le (π.map Prod.fst) hσ
  rw [realSelectionLift, map_withDensity_comp π measurable_fst (Measure.measurable_rnDeriv _ _),
    Measure.withDensity_rnDeriv_eq _ _ (Measure.absolutelyContinuous_of_le hσ)]

theorem realSelectionLift_le (π : Measure (ℝ × ℝ)) [IsFiniteMeasure π]
    {σ : Measure ℝ} (hσ : σ ≤ π.map Prod.fst) : realSelectionLift π σ ≤ π := by
  have h := ae_of_ae_map measurable_fst.aemeasurable (Measure.rnDeriv_le_one_of_le hσ)
  have h' : (fun z : ℝ × ℝ => σ.rnDeriv (π.map Prod.fst) z.1) ≤ᵐ[π] 1 := h
  exact (withDensity_mono h').trans_eq withDensity_one

theorem realTransportedSelection_le (π : Measure (ℝ × ℝ)) [IsFiniteMeasure π]
    {σ : Measure ℝ} (hσ : σ ≤ π.map Prod.fst) :
    realTransportedSelection π σ ≤ π.map Prod.snd :=
  Measure.map_mono (realSelectionLift_le π hσ) measurable_snd

theorem realTransportedSelection_mass (π : Measure (ℝ × ℝ)) [IsFiniteMeasure π]
    {σ : Measure ℝ} (hσ : σ ≤ π.map Prod.fst) :
    realTransportedSelection π σ Set.univ = σ Set.univ := by
  have hf := congrArg (fun μ : Measure ℝ => μ Set.univ) (realSelectionLift_first π hσ)
  simpa only [realTransportedSelection, Measure.map_apply measurable_fst MeasurableSet.univ,
    Measure.map_apply measurable_snd MeasurableSet.univ, Set.preimage_univ] using hf

theorem realTransportedSelection_costs (π : Measure (ℝ × ℝ)) [IsFiniteMeasure π]
    (hclosed : ∀ᵐ z ∂π, z.1 ∈ Icc 0 (1/2) ∧ z.2 ∈ Icc 0 (1/2))
    (hup : ∀ᵐ z ∂π, z.1 ≤ z.2) {σ : Measure ℝ} (hσ : σ ≤ π.map Prod.fst)
    {h : ℝ} (hh : 0 ≤ h) :
    zeroGamma (realTransportedSelection π σ) ≤ 3*zeroGamma σ ∧
      zeroTailCost (π.map Prod.snd-realTransportedSelection π σ) h ≤
        zeroTailCost (π.map Prod.fst-σ) h := by
  have hξ := realSelectionLift_le π hσ
  have : IsFiniteMeasure (realSelectionLift π σ) := isFiniteMeasure_of_le π hξ
  have hupξ := (Measure.absolutelyContinuous_of_le hξ).ae_le hup
  have hcξ := (Measure.absolutelyContinuous_of_le hξ).ae_le hclosed
  have hupres := (Measure.absolutelyContinuous_of_le (Measure.sub_le : π-realSelectionLift π σ ≤ π)).ae_le hup
  constructor
  · simpa only [realSelectionLift_first π hσ, realTransportedSelection] using
      zeroGamma_increasing_coupling (realSelectionLift π σ) hcξ hupξ
  · have ht := zeroTailCost_increasing_coupling (π-realSelectionLift π σ) hupres hh
    rw [map_sub_of_le hξ measurable_fst, realSelectionLift_first π hσ,
      map_sub_of_le hξ measurable_snd] at ht
    exact ht

theorem realTransportedSelection_objective (π : Measure (ℝ × ℝ)) [IsFiniteMeasure π]
    (hclosed : ∀ᵐ z ∂π, z.1 ∈ Icc 0 (1/2) ∧ z.2 ∈ Icc 0 (1/2))
    (hup : ∀ᵐ z ∂π, z.1 ≤ z.2) {σ : Measure ℝ} (hσ : σ ≤ π.map Prod.fst) (ρ B : ℝ) :
    zeroObjective (π.map Prod.snd) ρ B (realTransportedSelection π σ) ≤
      ENNReal.ofReal (Real.sqrt 3)*zeroObjective (π.map Prod.fst) ρ B σ := by
  have hc := realTransportedSelection_costs π hclosed hup hσ (h := 1/Real.sqrt B) (by positivity)
  have hroot : (3 : ℝ≥0∞)^(1/2 : ℝ) = ENNReal.ofReal (Real.sqrt 3) := by
    rw [← ENNReal.ofReal_ofNat, ENNReal.ofReal_rpow_of_nonneg (by norm_num) (by norm_num),
      ← Real.sqrt_eq_rpow]
  have hge : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (Real.sqrt 3) := by
    simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal one_le_sqrt_three
  unfold zeroObjective
  rw [mul_add]
  apply add_le_add
  · calc
      _ ≤ ENNReal.ofReal (1/Real.sqrt B) *
          (ENNReal.ofReal ρ*(3*zeroGamma σ))^(1/2 : ℝ) :=
        mul_le_mul_right (ENNReal.rpow_le_rpow (mul_le_mul_right hc.1 _) (by norm_num)) _
      _ = _ := by
        rw [mul_left_comm (ENNReal.ofReal ρ), ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), hroot]
        ac_rfl
  · exact hc.2.trans (by
      simpa only [one_mul] using
        mul_le_mul_left hge (zeroTailCost (π.map Prod.fst-σ) (1/Real.sqrt B)))

theorem zeroSelection_increasing_coupling (π : Measure (ℝ × ℝ)) [IsFiniteMeasure π]
    (hclosed : ∀ᵐ z ∂π, z.1 ∈ Icc 0 (1/2) ∧ z.2 ∈ Icc 0 (1/2))
    (hup : ∀ᵐ z ∂π, z.1 ≤ z.2) (ρ B : ℝ) :
    zeroSelection (π.map Prod.snd) ρ B ≤
      ENNReal.ofReal (Real.sqrt 3)*zeroSelection (π.map Prod.fst) ρ B := by
  have hge : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (Real.sqrt 3) := by
    simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal one_le_sqrt_three
  have hne := ne_of_gt (lt_of_lt_of_le zero_lt_one hge)
  conv_rhs => rw [zeroSelection, mul_min]
  apply le_min
  · exact (min_le_left _ _).trans
      (by simpa only [one_mul] using mul_le_mul_left hge (ENNReal.ofReal ρ))
  · rw [ENNReal.mul_iInf_of_ne hne ENNReal.ofReal_ne_top]
    refine le_iInf fun σ => ?_
    rw [ENNReal.mul_iInf_of_ne hne ENNReal.ofReal_ne_top]
    refine le_iInf fun hσ => ?_
    have ht := realTransportedSelection_le π hσ
    have hle : zeroSelection (π.map Prod.snd) ρ B ≤
        zeroObjective (π.map Prod.snd) ρ B (realTransportedSelection π σ) :=
      (min_le_right _ _).trans (iInf₂_le (realTransportedSelection π σ) ht)
    exact hle.trans (realTransportedSelection_objective π hclosed hup hσ ρ B)

end ThresholdHC.ArbitraryLawAdaptation
