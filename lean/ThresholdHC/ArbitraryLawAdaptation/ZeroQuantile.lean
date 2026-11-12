import ThresholdHC.ArbitraryLawAdaptation.DominatedMass
import ThresholdHC.QuantileSelection.Full

/-! The quantile design of a law with mass at zero: (A16).

Let `α = z δ₀ + (1 - z) η`, with `η` a probability law of positive gaps and
`z` the unresolved mass at zero. The quantile design takes the lowest-gap
mass `ρ` of `α`: the whole zero atom, and the lowest-gap mass `ρ - z` of the
positive part. Under `η` this is the quantile part of mass
`r = (ρ - z)/(1 - z)`. The zero atom is charged at tail weight one, and the
remaining core `(1 - z) σ` by its cost entropy, so

  `Q_α = min{ρ, z + (1 - z) τ_ν(h) + h √(ρ (1 - z) Γ_σ)}`,   `h = B^{-1/2}`,

with `ν` and `σ` the quantile part and the quantile core of `η` at mass `r`.
When `z ≥ ρ` the design is the constant fallback and `Q_α = ρ`.

The comparison `Q_α ≤ 4 K_α` holds for every such law, where `K_α` is the
selection functional extended to laws with mass at zero. For `z ≥ ρ/2` it
follows from `K_α ≥ min{ρ, z}`. For `z < ρ/2`,

  `Q_α ≤ z + √2 (1 - z) Q_{η,r}`,   `K_α ≥ z`,   `K_α ≥ (1 - z) K_{η,r}`,

and the positive-gap comparison `Q_{η,r} ≤ (8/5) K_{η,r}` finishes. -/

noncomputable section
open MeasureTheory Real
open scoped ENNReal
namespace ThresholdHC.ArbitraryLawAdaptation
open ThresholdHC.Tier6 (Gap)
open ThresholdHC.EntropyTail ThresholdHC.EntropyTailQuantile

/-- The law `z δ₀ + (1 - z) η` on the real line. -/
def zeroAtomLaw (z : ℝ) (η : Measure Gap) : Measure ℝ :=
  ENNReal.ofReal z • Measure.dirac 0 + ENNReal.ofReal (1 - z) • η.map Subtype.val

instance zeroAtomLaw_finite (z : ℝ) (η : Measure Gap) [IsFiniteMeasure η] :
    IsFiniteMeasure (zeroAtomLaw z η) := by
  have h1 : IsFiniteMeasure (ENNReal.ofReal z • Measure.dirac (0 : ℝ)) :=
    (Measure.dirac (0 : ℝ)).smul_finite ENNReal.ofReal_ne_top
  have h2 : IsFiniteMeasure (ENNReal.ofReal (1 - z) • η.map Subtype.val) :=
    (η.map Subtype.val).smul_finite ENNReal.ofReal_ne_top
  unfold zeroAtomLaw
  infer_instance

/-- The mass of `z δ₀ + (1 - z) η` at zero is `z`. -/
theorem zeroAtomLaw_zero_atom (z : ℝ) (η : Measure Gap) :
    zeroAtomLaw z η {0} = ENNReal.ofReal z := by
  unfold zeroAtomLaw
  rw [Measure.add_apply, Measure.smul_apply, Measure.smul_apply, mappedGap_zero_atom,
    Measure.dirac_apply_of_mem (Set.mem_singleton (0 : ℝ)), smul_eq_mul, smul_eq_mul, mul_one,
    mul_zero, add_zero]

/-- The zero floor of one objective: a selection with finite entropy has no
mass at zero, and zero has tail weight one. -/
theorem zeroMass_le_zeroObjective {α σ : Measure ℝ} [IsFiniteMeasure α] (hσ : σ ≤ α) {ρ B : ℝ}
    (hρ : 0 < ρ) (hB : 0 < B) : α {0} ≤ zeroObjective α ρ B σ := by
  have : IsFiniteMeasure σ := isFiniteMeasure_of_le α hσ
  by_cases hs : σ {0} = 0
  · have hsub : (α - σ) {0} = α {0} := by
      rw [Measure.sub_apply (measurableSet_singleton 0) hσ, hs, tsub_zero]
    have hind : (α - σ) {0} ≤ zeroTailCost (α - σ) (1 / Real.sqrt B) := by
      rw [← lintegral_indicator_one (measurableSet_singleton (0 : ℝ))]
      refine lintegral_mono fun d => ?_
      by_cases hd : d = 0
      · rw [hd, zeroTailWeight_zero]
        exact Set.indicator_le_self' (fun _ _ => zero_le_one) _
      · rw [Set.indicator_of_notMem (by simpa using hd)]
        exact zero_le
    rw [← hsub]
    exact hind.trans le_add_self
  · have hh : 0 < 1 / Real.sqrt B := by positivity
    unfold zeroObjective
    rw [zeroGamma_of_atom hs, ENNReal.mul_top (ENNReal.ofReal_pos.mpr hρ).ne',
      ENNReal.top_rpow_of_pos (by norm_num), ENNReal.mul_top (ENNReal.ofReal_pos.mpr hh).ne',
      top_add]
    exact le_top

/-- The zero floor: `K_α ≥ min{ρ, α{0}}`. -/
theorem min_zeroMass_le_zeroSelection (α : Measure ℝ) [IsFiniteMeasure α] {ρ B : ℝ}
    (hρ : 0 < ρ) (hB : 0 < B) : min (ENNReal.ofReal ρ) (α {0}) ≤ zeroSelection α ρ B :=
  le_min (min_le_left _ _)
    (le_iInf₂ fun _ hσ => (min_le_right _ _).trans (zeroMass_le_zeroObjective hσ hρ hB))

/-- Scaling the gap law: `c K_{η,r} ≤ K_{c η,ρ}` when `c r ≤ ρ`. -/
theorem smul_selection_le (η : Measure Gap) [IsFiniteMeasure η] {c r ρ B : ℝ} (hc : 0 < c)
    (hr : 0 ≤ r) (hcr : c * r ≤ ρ) :
    ENNReal.ofReal c * selection η r B ≤ selection (ENNReal.ofReal c • η) ρ B := by
  have hcne : ENNReal.ofReal c ≠ 0 := (ENNReal.ofReal_pos.mpr hc).ne'
  have hctop : ENNReal.ofReal c ≠ ⊤ := ENNReal.ofReal_ne_top
  have hρ0 : 0 ≤ ρ := (mul_nonneg hc.le hr).trans hcr
  have hfin : IsFiniteMeasure (ENNReal.ofReal c • η) := η.smul_finite hctop
  unfold selection
  rw [mul_min]
  refine le_min ((min_le_left _ _).trans ?_) ((min_le_right _ _).trans ?_)
  · rw [← ENNReal.ofReal_mul hc.le]
    exact ENNReal.ofReal_le_ofReal hcr
  · refine le_iInf₂ fun σ hσ => ?_
    obtain ⟨τ, hτη, rfl⟩ : ∃ τ : Measure Gap, τ ≤ η ∧ σ = ENNReal.ofReal c • τ := by
      refine ⟨(ENNReal.ofReal c)⁻¹ • σ, fun s => ?_, ?_⟩
      · have h1 : σ s ≤ ENNReal.ofReal c * η s := by simpa using hσ s
        calc ((ENNReal.ofReal c)⁻¹ • σ) s = (ENNReal.ofReal c)⁻¹ * σ s := by simp
          _ ≤ (ENNReal.ofReal c)⁻¹ * (ENNReal.ofReal c * η s) := by gcongr
          _ = η s := by rw [← mul_assoc, ENNReal.inv_mul_cancel hcne hctop, one_mul]
      · rw [smul_smul, ENNReal.mul_inv_cancel hcne hctop, one_smul]
    have : IsFiniteMeasure τ := isFiniteMeasure_of_le η hτη
    have : IsFiniteMeasure (ENNReal.ofReal c • τ) := τ.smul_finite hctop
    have hres : ENNReal.ofReal c • η - ENNReal.ofReal c • τ = ENNReal.ofReal c • (η - τ) := by
      have he : ENNReal.ofReal c • (η - τ) + ENNReal.ofReal c • τ = ENNReal.ofReal c • η := by
        rw [← smul_add, Measure.sub_add_cancel_of_le hτη]
      rw [← he, Measure.add_sub_cancel]
    have hsq : ENNReal.ofReal c = (ENNReal.ofReal (c ^ 2)) ^ (1 / 2 : ℝ) := by
      rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num), ← Real.sqrt_eq_rpow,
        Real.sqrt_sq hc.le]
    have hin : ENNReal.ofReal (c ^ 2) * (ENNReal.ofReal r * gamma τ) ≤
        ENNReal.ofReal ρ * (ENNReal.ofReal c * gamma τ) := by
      have h1 : ENNReal.ofReal (c ^ 2) * ENNReal.ofReal r ≤
          ENNReal.ofReal ρ * ENNReal.ofReal c := by
        rw [← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ c ^ 2), ← ENNReal.ofReal_mul hρ0]
        exact ENNReal.ofReal_le_ofReal (by nlinarith [mul_le_mul_of_nonneg_left hcr hc.le])
      calc ENNReal.ofReal (c ^ 2) * (ENNReal.ofReal r * gamma τ)
          = ENNReal.ofReal (c ^ 2) * ENNReal.ofReal r * gamma τ := (mul_assoc _ _ _).symm
        _ ≤ ENNReal.ofReal ρ * ENNReal.ofReal c * gamma τ := by gcongr
        _ = ENNReal.ofReal ρ * (ENNReal.ofReal c * gamma τ) := mul_assoc _ _ _
    have hmul : (ENNReal.ofReal (c ^ 2) * (ENNReal.ofReal r * gamma τ)) ^ (1 / 2 : ℝ) =
        ENNReal.ofReal c * (ENNReal.ofReal r * gamma τ) ^ (1 / 2 : ℝ) := by
      rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), ← hsq]
    calc ENNReal.ofReal c * (⨅ σ', ⨅ (_ : σ' ≤ η), selectionObjective η r B σ')
        ≤ ENNReal.ofReal c * selectionObjective η r B τ := by
          gcongr
          exact iInf₂_le τ hτη
      _ ≤ selectionObjective (ENNReal.ofReal c • η) ρ B (ENNReal.ofReal c • τ) := by
          unfold selectionObjective
          rw [canonicalGamma_smul τ hc.le, hres, tailCost_smul, mul_add]
          refine add_le_add ?_ le_rfl
          calc ENNReal.ofReal c *
                (ENNReal.ofReal (1 / Real.sqrt B) * (ENNReal.ofReal r * gamma τ) ^ (1 / 2 : ℝ))
              = ENNReal.ofReal (1 / Real.sqrt B) *
                  (ENNReal.ofReal (c ^ 2) * (ENNReal.ofReal r * gamma τ)) ^ (1 / 2 : ℝ) := by
                rw [hmul, mul_left_comm]
            _ ≤ ENNReal.ofReal (1 / Real.sqrt B) *
                  (ENNReal.ofReal ρ * (ENNReal.ofReal c * gamma τ)) ^ (1 / 2 : ℝ) := by
                gcongr

/-- Scaling commutes with the embedding of positive gaps in the real line. -/
theorem map_val_smul (c : ℝ≥0∞) (σ : Measure Gap) :
    (c • σ).map Subtype.val = c • σ.map Subtype.val := by
  ext s hs
  rw [Measure.map_apply measurable_subtype_coe hs, Measure.smul_apply, Measure.smul_apply,
    Measure.map_apply measurable_subtype_coe hs]

/-- `K_α ≥ (1 - z) K_{η,r}` for `α = z δ₀ + (1 - z) η`, when `(1 - z) r ≤ ρ`. -/
theorem positive_selection_le_zeroSelection (η : Measure Gap) [IsFiniteMeasure η]
    {z r ρ B : ℝ} (hz1 : z < 1) (hr : 0 ≤ r) (hcr : (1 - z) * r ≤ ρ) :
    ENNReal.ofReal (1 - z) * selection η r B ≤ zeroSelection (zeroAtomLaw z η) ρ B := by
  have hc : 0 < 1 - z := by linarith
  have : IsFiniteMeasure (ENNReal.ofReal (1 - z) • η) := η.smul_finite ENNReal.ofReal_ne_top
  have hle : (ENNReal.ofReal (1 - z) • η).map Subtype.val ≤ zeroAtomLaw z η := by
    rw [map_val_smul]
    exact Measure.le_add_left le_rfl
  calc ENNReal.ofReal (1 - z) * selection η r B
      ≤ selection (ENNReal.ofReal (1 - z) • η) ρ B := smul_selection_le η hc hr hcr
    _ = zeroSelection ((ENNReal.ofReal (1 - z) • η).map Subtype.val) ρ B :=
        (zeroSelection_map _ ρ B).symm
    _ ≤ zeroSelection (zeroAtomLaw z η) ρ B := zeroSelection_mono hle ρ B

/-- The rarity of the positive part: `r = (ρ - z)/(1 - z)`, the mass that the
quantile design removes under `η` when the zero atom has mass `z`. -/
def conditionalRarity (ρ z : ℝ) : ℝ := (ρ - z) / (1 - z)

/-- The quantile value `Q_α(B)` of `α = z δ₀ + (1 - z) η`. When `z ≥ ρ` the
design is the constant fallback. Otherwise the zero atom is charged at tail
weight one, the quantile part of `η` of mass `r` by its tail modulus, and the
quantile core by its cost entropy, each scaled by the positive mass `1 - z`. -/
def zeroQuantileValue (z : ℝ) (η : Measure Gap) (ρ B : ℝ) : ℝ≥0∞ :=
  if ρ ≤ z then ENNReal.ofReal ρ
  else min (ENNReal.ofReal ρ)
    (ENNReal.ofReal z +
      (ENNReal.ofReal (1 - z) *
          ENNReal.ofReal (tailModulus (quantileTail η (conditionalRarity ρ z)) (budgetScale B)) +
        ENNReal.ofReal (budgetScale B) *
          (ENNReal.ofReal ρ * (ENNReal.ofReal (1 - z) *
            measureCostEntropy (quantileCore η (conditionalRarity ρ z)))) ^ (1 / (2 : ℝ))))

/-- Without a zero atom the design is the closed quantile value. -/
theorem zeroQuantileValue_zero (η : Measure Gap) {ρ B : ℝ} (hρ : 0 < ρ) :
    zeroQuantileValue 0 η ρ B = closedQuantileValue η ρ B := by
  unfold zeroQuantileValue closedQuantileValue conditionalRarity
  rw [ite_eq_right (not_le.mpr hρ), sub_zero, sub_zero, div_one, ENNReal.ofReal_zero,
    ENNReal.ofReal_one, zero_add, one_mul, one_mul]

/-- The design never exceeds the rarity bound. -/
theorem zeroQuantileValue_le_rho (z : ℝ) (η : Measure Gap) (ρ B : ℝ) :
    zeroQuantileValue z η ρ B ≤ ENNReal.ofReal ρ := by
  unfold zeroQuantileValue
  split_ifs
  · exact le_rfl
  · exact min_le_left _ _

/-- `Q_α ≤ z + √2 (1 - z) Q_{η,r}` when `z ≤ ρ/2`, in both cap cases. -/
theorem zeroQuantileValue_le_closed (η : Measure Gap) {z ρ B : ℝ} (hz0 : 0 ≤ z) (hρ : 0 < ρ)
    (hρ1 : ρ ≤ 1) (hz : 2 * z ≤ ρ) :
    zeroQuantileValue z η ρ B ≤
      ENNReal.ofReal z +
        ENNReal.ofReal (Real.sqrt 2 * (1 - z)) *
          closedQuantileValue η (conditionalRarity ρ z) B := by
  have hzlt : ¬ ρ ≤ z := by linarith
  have hc : 0 < 1 - z := by linarith
  have hcr : (1 - z) * conditionalRarity ρ z = ρ - z := by
    unfold conditionalRarity
    field_simp
  have hr0 : 0 ≤ conditionalRarity ρ z := div_nonneg (by linarith) hc.le
  have hs2 : (1 : ℝ) ≤ Real.sqrt 2 := Real.one_le_sqrt.mpr (by norm_num)
  have hroot : ENNReal.ofReal (Real.sqrt 2 * (1 - z)) =
      (ENNReal.ofReal (2 * (1 - z) ^ 2)) ^ (1 / 2 : ℝ) := by
    rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num), ← Real.sqrt_eq_rpow,
      Real.sqrt_mul (by norm_num), Real.sqrt_sq hc.le]
  unfold zeroQuantileValue closedQuantileValue
  rw [ite_eq_right hzlt, mul_min, ← min_add_add_left]
  refine le_min ((min_le_left _ _).trans ?_) ((min_le_right _ _).trans ?_)
  · rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_add hz0 (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    nlinarith [mul_nonneg hc.le hr0]
  · rw [mul_add]
    refine add_le_add le_rfl (add_le_add ?_ ?_)
    · gcongr
      nlinarith
    · have hin : ENNReal.ofReal ρ * (ENNReal.ofReal (1 - z) *
            measureCostEntropy (quantileCore η (conditionalRarity ρ z))) ≤
          ENNReal.ofReal (2 * (1 - z) ^ 2) * (ENNReal.ofReal (conditionalRarity ρ z) *
            measureCostEntropy (quantileCore η (conditionalRarity ρ z))) := by
        have h1 : ENNReal.ofReal ρ * ENNReal.ofReal (1 - z) ≤
            ENNReal.ofReal (2 * (1 - z) ^ 2) * ENNReal.ofReal (conditionalRarity ρ z) := by
          rw [← ENNReal.ofReal_mul hρ.le, ← ENNReal.ofReal_mul (by positivity)]
          apply ENNReal.ofReal_le_ofReal
          have h2 : 2 * (1 - z) ^ 2 * conditionalRarity ρ z = 2 * (1 - z) * (ρ - z) := by
            rw [← hcr]
            ring
          rw [h2]
          nlinarith
        calc ENNReal.ofReal ρ * (ENNReal.ofReal (1 - z) *
              measureCostEntropy (quantileCore η (conditionalRarity ρ z)))
            = ENNReal.ofReal ρ * ENNReal.ofReal (1 - z) *
                measureCostEntropy (quantileCore η (conditionalRarity ρ z)) :=
              (mul_assoc _ _ _).symm
          _ ≤ ENNReal.ofReal (2 * (1 - z) ^ 2) * ENNReal.ofReal (conditionalRarity ρ z) *
                measureCostEntropy (quantileCore η (conditionalRarity ρ z)) := by gcongr
          _ = _ := mul_assoc _ _ _
      calc ENNReal.ofReal (budgetScale B) * (ENNReal.ofReal ρ * (ENNReal.ofReal (1 - z) *
            measureCostEntropy (quantileCore η (conditionalRarity ρ z)))) ^ (1 / (2 : ℝ))
          ≤ ENNReal.ofReal (budgetScale B) * (ENNReal.ofReal (2 * (1 - z) ^ 2) *
              (ENNReal.ofReal (conditionalRarity ρ z) *
                measureCostEntropy (quantileCore η (conditionalRarity ρ z)))) ^ (1 / (2 : ℝ)) := by
            gcongr
        _ = ENNReal.ofReal (Real.sqrt 2 * (1 - z)) * (ENNReal.ofReal (budgetScale B) *
              (ENNReal.ofReal (conditionalRarity ρ z) *
                measureCostEntropy (quantileCore η (conditionalRarity ρ z))) ^ (1 / (2 : ℝ))) := by
            rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), ← hroot, mul_left_comm]

/-- (A16) for `α = z δ₀ + (1 - z) η`: `Q_α ≤ 4 K_α`. Here `η` is any
probability law of positive gaps, `z ≥ 0` is the mass at zero, and `K_α` is
the selection functional extended to laws with mass at zero. -/
theorem zeroQuantileValue_le_four (η : Measure Gap) [IsProbabilityMeasure η] {z ρ B : ℝ}
    (hz0 : 0 ≤ z) (hρ : 0 < ρ) (hρ4 : ρ ≤ 1 / 4) (hB : 0 < B) :
    zeroQuantileValue z η ρ B ≤ 4 * zeroSelection (zeroAtomLaw z η) ρ B := by
  have hfloor : min (ENNReal.ofReal ρ) (ENNReal.ofReal z) ≤
      zeroSelection (zeroAtomLaw z η) ρ B := by
    have h := min_zeroMass_le_zeroSelection (zeroAtomLaw z η) hρ hB
    rwa [zeroAtomLaw_zero_atom] at h
  by_cases h2 : ρ ≤ 2 * z
  · -- `z ≥ ρ/2`: `Q_α ≤ ρ ≤ 2 min{ρ, z} ≤ 2 K_α`.
    have hρle : ENNReal.ofReal ρ ≤ 2 * min (ENNReal.ofReal ρ) (ENNReal.ofReal z) := by
      rw [mul_min]
      refine le_min ?_ ?_
      · exact le_mul_of_one_le_left zero_le (by norm_num)
      · rw [← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_mul (by norm_num)]
        exact ENNReal.ofReal_le_ofReal h2
    calc zeroQuantileValue z η ρ B ≤ ENNReal.ofReal ρ := zeroQuantileValue_le_rho z η ρ B
      _ ≤ 2 * min (ENNReal.ofReal ρ) (ENNReal.ofReal z) := hρle
      _ ≤ 2 * zeroSelection (zeroAtomLaw z η) ρ B := by gcongr
      _ ≤ 4 * zeroSelection (zeroAtomLaw z η) ρ B := by
          gcongr
          norm_num
  · -- `z < ρ/2`: the positive-gap comparison at rarity `r`.
    have hzρ : 2 * z ≤ ρ := (not_le.mp h2).le
    have hc : 0 < 1 - z := by linarith
    have hcr : (1 - z) * conditionalRarity ρ z = ρ - z := by
      unfold conditionalRarity
      field_simp
    have hr : 0 < conditionalRarity ρ z := div_pos (by linarith) hc
    have hrρ : conditionalRarity ρ z ≤ ρ := by
      unfold conditionalRarity
      rw [div_le_iff₀ hc]
      nlinarith
    have h85 := (QuantileSelection.locked_selection_comparison η hr (hrρ.trans hρ4) hB).2
    have hpos := positive_selection_le_zeroSelection η (B := B) (by linarith : z < 1) hr.le
      (by rw [hcr]; linarith : (1 - z) * conditionalRarity ρ z ≤ ρ)
    have hzK : ENNReal.ofReal z ≤ zeroSelection (zeroAtomLaw z η) ρ B := by
      rwa [min_eq_right (ENNReal.ofReal_le_ofReal (by linarith : z ≤ ρ))] at hfloor
    have hconst : ENNReal.ofReal (Real.sqrt 2 * (8 / 5)) ≤ 3 := by
      rw [← ENNReal.ofReal_ofNat 3]
      apply ENNReal.ofReal_le_ofReal
      have hs : Real.sqrt 2 ≤ 15 / 8 := Real.sqrt_le_iff.mpr ⟨by norm_num, by norm_num⟩
      linarith
    calc zeroQuantileValue z η ρ B
        ≤ ENNReal.ofReal z + ENNReal.ofReal (Real.sqrt 2 * (1 - z)) *
            closedQuantileValue η (conditionalRarity ρ z) B :=
          zeroQuantileValue_le_closed η hz0 hρ (by linarith) hzρ
      _ ≤ ENNReal.ofReal z + ENNReal.ofReal (Real.sqrt 2 * (1 - z)) *
            (ENNReal.ofReal (8 / 5) * selection η (conditionalRarity ρ z) B) := by gcongr
      _ = ENNReal.ofReal z + ENNReal.ofReal (Real.sqrt 2 * (8 / 5)) *
            (ENNReal.ofReal (1 - z) * selection η (conditionalRarity ρ z) B) := by
          rw [ENNReal.ofReal_mul (Real.sqrt_nonneg 2), ENNReal.ofReal_mul (Real.sqrt_nonneg 2)]
          ring
      _ ≤ zeroSelection (zeroAtomLaw z η) ρ B + 3 * zeroSelection (zeroAtomLaw z η) ρ B := by
          gcongr
      _ = 4 * zeroSelection (zeroAtomLaw z η) ρ B := by ring

/-- The design value is an admissible objective. For `z < ρ`, the selection
objective of `α = z δ₀ + (1 - z) η` at the quantile core of `η` of rarity `r`,
scaled by `1 - z`, is the second term of `Q_α`. -/
theorem zeroObjective_quantileCore (η : Measure Gap) [IsProbabilityMeasure η] {z ρ : ℝ}
    (hzρ : z < ρ) (hρ1 : ρ ≤ 1) (B : ℝ) :
    zeroObjective (zeroAtomLaw z η) ρ B
        ((ENNReal.ofReal (1 - z) • quantileCore η (conditionalRarity ρ z)).map Subtype.val) =
      ENNReal.ofReal z +
        (ENNReal.ofReal (1 - z) *
            ENNReal.ofReal (tailModulus (quantileTail η (conditionalRarity ρ z)) (budgetScale B)) +
          ENNReal.ofReal (budgetScale B) *
            (ENNReal.ofReal ρ * (ENNReal.ofReal (1 - z) *
              measureCostEntropy (quantileCore η (conditionalRarity ρ z)))) ^ (1 / (2 : ℝ))) := by
  have hc : 0 < 1 - z := by linarith
  have hr : 0 < conditionalRarity ρ z := div_pos (by linarith) hc
  have hr1 : conditionalRarity ρ z ≤ 1 := by
    unfold conditionalRarity
    rw [div_le_iff₀ hc]
    linarith
  have hsum := quantileTail_add_core η hr hr1
  have htail : IsFiniteMeasure (quantileTail η (conditionalRarity ρ z)) :=
    isFiniteMeasure_of_le η (quantileTail_le η hr hr1)
  have hcore : IsFiniteMeasure (quantileCore η (conditionalRarity ρ z)) :=
    isFiniteMeasure_of_le η Measure.sub_le
  have hfin : IsFiniteMeasure
      (ENNReal.ofReal (1 - z) • (quantileCore η (conditionalRarity ρ z)).map Subtype.val) :=
    Measure.smul_finite _ ENNReal.ofReal_ne_top
  -- The residual of `α` is the zero atom plus the scaled quantile part.
  have hres : zeroAtomLaw z η -
        ENNReal.ofReal (1 - z) • (quantileCore η (conditionalRarity ρ z)).map Subtype.val =
      ENNReal.ofReal z • Measure.dirac 0 +
        ENNReal.ofReal (1 - z) • (quantileTail η (conditionalRarity ρ z)).map Subtype.val := by
    have he : ENNReal.ofReal z • Measure.dirac 0 +
          ENNReal.ofReal (1 - z) • (quantileTail η (conditionalRarity ρ z)).map Subtype.val +
          ENNReal.ofReal (1 - z) • (quantileCore η (conditionalRarity ρ z)).map Subtype.val =
        zeroAtomLaw z η := by
      unfold zeroAtomLaw
      rw [add_assoc, ← smul_add, ← Measure.map_add _ _ measurable_subtype_coe, hsum]
    rw [← he, Measure.add_sub_cancel]
  have hgamma : gamma (quantileCore η (conditionalRarity ρ z)) =
      measureCostEntropy (quantileCore η (conditionalRarity ρ z)) :=
    le_antisymm (gamma_le_quantile_measureCostEntropy _) (quantile_measureCostEntropy_le _)
  have hscale : 1 / Real.sqrt B = budgetScale B := by
    unfold budgetScale
    rw [one_div]
  unfold zeroObjective
  rw [map_val_smul, hres, zeroTailCost_add, zeroTailCost_smul, zeroTailCost_smul,
    zeroTailCost_dirac_zero, mul_one, zeroTailCost_map, ← map_val_smul, zeroGamma_map,
    canonicalGamma_smul _ hc.le, hgamma, hscale,
    ← quantile_tailModulus_eq _ (budgetScale_nonneg B)]
  ring

/-- `K_α ≤ Q_α`: the quantile design is an admissible selection. -/
theorem zeroSelection_le_zeroQuantileValue (η : Measure Gap) [IsProbabilityMeasure η]
    (z : ℝ) {ρ : ℝ} (hρ1 : ρ ≤ 1) (B : ℝ) :
    zeroSelection (zeroAtomLaw z η) ρ B ≤ zeroQuantileValue z η ρ B := by
  unfold zeroQuantileValue
  split_ifs with h
  · exact min_le_left _ _
  · refine le_min (min_le_left _ _) ?_
    rw [← zeroObjective_quantileCore η (not_le.mp h) hρ1 B]
    refine (min_le_right _ _).trans (iInf₂_le _ ?_)
    rw [map_val_smul]
    refine le_trans (fun s => ?_) (Measure.le_add_left le_rfl)
    simp only [Measure.smul_apply, smul_eq_mul]
    gcongr
    all_goals first | exact Measure.sub_le | exact measurable_subtype_coe

/-- The mass of a law on the real line at zero. -/
def zeroMass (α : Measure ℝ) : ℝ := α.real {0}

/-- The positive part of a law on the real line, normalized by its mass
`1 - α{0}`. -/
def positiveLaw (α : Measure ℝ) : Measure Gap :=
  (ENNReal.ofReal (1 - zeroMass α))⁻¹ • positivePart α

/-- Normalization of the positive part. A probability law on `[0, 1/2]` with
`α{0} < 1` is `z δ₀ + (1 - z) η`, with `z = α{0}` and `η` its normalized
positive part, which is a probability law of positive gaps. -/
theorem zeroAtomLaw_decomposition (α : Measure ℝ) [IsProbabilityMeasure α]
    (hsupp : α (Set.Icc 0 (1 / 2))ᶜ = 0) (hz : zeroMass α < 1) :
    IsProbabilityMeasure (positiveLaw α) ∧ zeroAtomLaw (zeroMass α) (positiveLaw α) = α := by
  have hc : 0 < 1 - zeroMass α := by linarith
  have hcne : ENNReal.ofReal (1 - zeroMass α) ≠ 0 := (ENNReal.ofReal_pos.mpr hc).ne'
  have hctop : ENNReal.ofReal (1 - zeroMass α) ≠ ⊤ := ENNReal.ofReal_ne_top
  have hz0 : ENNReal.ofReal (zeroMass α) = α {0} := by
    unfold zeroMass
    rw [ofReal_measureReal]
  have hsplit : Set.Icc (0 : ℝ) (1 / 2) = {0} ∪ Set.Ioc 0 (1 / 2) := by
    ext x
    simp only [Set.mem_Icc, Set.mem_union, Set.mem_singleton_iff, Set.mem_Ioc]
    constructor
    · rintro ⟨h0, h1⟩
      rcases h0.eq_or_lt with h | h
      · exact Or.inl h.symm
      · exact Or.inr ⟨h, h1⟩
    · rintro (h | ⟨h0, h1⟩)
      · rw [h]
        exact ⟨le_rfl, by norm_num⟩
      · exact ⟨h0.le, h1⟩
  have hdisj : Disjoint ({0} : Set ℝ) (Set.Ioc 0 (1 / 2)) := by
    rw [Set.disjoint_singleton_left]
    exact fun h => lt_irrefl _ h.1
  -- The law is its restriction to `{0}` plus its restriction to `(0, 1/2]`.
  have hα : α = α.restrict {0} + α.restrict (Set.Ioc 0 (1 / 2)) := by
    rw [← Measure.restrict_union hdisj measurableSet_Ioc, ← hsplit]
    exact (Measure.restrict_eq_self_of_ae_mem (by
      rw [ae_iff]
      exact hsupp)).symm
  have hpos : (positivePart α) Set.univ = ENNReal.ofReal (1 - zeroMass α) := by
    have h1 : (positivePart α) Set.univ = α (Set.Ioc 0 (1 / 2)) := by
      have h := congrArg (fun m : Measure ℝ => m Set.univ) (map_positivePart α)
      simp only [Measure.map_apply measurable_subtype_coe MeasurableSet.univ, Set.preimage_univ,
        Measure.restrict_apply MeasurableSet.univ, Set.univ_inter] at h
      exact h
    have h2 : α {0} + α (Set.Ioc 0 (1 / 2)) = 1 := by
      rw [← measure_union hdisj measurableSet_Ioc, ← hsplit]
      have h3 := measure_add_measure_compl (μ := α) (measurableSet_Icc (a := (0 : ℝ))
        (b := 1 / 2))
      rw [hsupp, add_zero, measure_univ] at h3
      exact h3
    have hzn : 0 ≤ zeroMass α := measureReal_nonneg
    rw [h1, ENNReal.ofReal_sub 1 hzn, ENNReal.ofReal_one, hz0]
    exact ENNReal.eq_sub_of_add_eq (measure_ne_top α {0}) (by rw [add_comm]; exact h2)
  refine ⟨⟨?_⟩, ?_⟩
  · unfold positiveLaw
    rw [Measure.smul_apply, hpos, smul_eq_mul, ENNReal.inv_mul_cancel hcne hctop]
  · have hmap : (positiveLaw α).map Subtype.val =
        (ENNReal.ofReal (1 - zeroMass α))⁻¹ • α.restrict (Set.Ioc 0 (1 / 2)) := by
      rw [← map_positivePart]
      exact map_val_smul _ _
    unfold zeroAtomLaw
    rw [hmap, smul_smul, ENNReal.mul_inv_cancel hcne hctop, one_smul, hz0,
      ← Measure.restrict_singleton]
    exact hα.symm

/-- The quantile design value of a law on `[0, 1/2]`: the value of its
decomposition into the zero atom and the normalized positive part. -/
def quantileDesignValue (α : Measure ℝ) (ρ B : ℝ) : ℝ≥0∞ :=
  zeroQuantileValue (zeroMass α) (positiveLaw α) ρ B

/-- (A16). For every probability law `α` on `[0, 1/2]`, every rarity
`0 < ρ ≤ 1/4` and every budget `B > 0`: `Q_α(B) ≤ 4 K_α(B)`. -/
theorem quantileDesignValue_le_four (α : Measure ℝ) [IsProbabilityMeasure α]
    (hsupp : α (Set.Icc 0 (1 / 2))ᶜ = 0) {ρ B : ℝ} (hρ : 0 < ρ) (hρ4 : ρ ≤ 1 / 4)
    (hB : 0 < B) : quantileDesignValue α ρ B ≤ 4 * zeroSelection α ρ B := by
  have hz0 : 0 ≤ zeroMass α := measureReal_nonneg
  by_cases hz : zeroMass α < 1
  · obtain ⟨hprob, hdec⟩ := zeroAtomLaw_decomposition α hsupp hz
    have h := zeroQuantileValue_le_four (positiveLaw α) (B := B) hz0 hρ hρ4 hB
    rwa [hdec] at h
  · -- The law is the unit mass at zero: both sides are governed by the cap.
    have hρz : ρ ≤ zeroMass α := by linarith [not_lt.mp hz]
    have hQ : quantileDesignValue α ρ B = ENNReal.ofReal ρ := by
      unfold quantileDesignValue zeroQuantileValue
      rw [ite_eq_left hρz]
    have hK : ENNReal.ofReal ρ ≤ zeroSelection α ρ B := by
      have h := min_zeroMass_le_zeroSelection α hρ hB
      have hatom : ENNReal.ofReal ρ ≤ α {0} := by
        have : α {0} = ENNReal.ofReal (zeroMass α) := by
          unfold zeroMass
          rw [ofReal_measureReal]
        rw [this]
        exact ENNReal.ofReal_le_ofReal hρz
      rwa [min_eq_left hatom] at h
    rw [hQ]
    exact hK.trans (le_mul_of_one_le_left zero_le (by norm_num))

/-- `K_α ≤ Q_α` for every probability law on `[0, 1/2]` and `ρ ≤ 1`. -/
theorem zeroSelection_le_quantileDesignValue (α : Measure ℝ) [IsProbabilityMeasure α]
    (hsupp : α (Set.Icc 0 (1 / 2))ᶜ = 0) {ρ : ℝ} (hρ1 : ρ ≤ 1) (B : ℝ) :
    zeroSelection α ρ B ≤ quantileDesignValue α ρ B := by
  by_cases hz : zeroMass α < 1
  · obtain ⟨hprob, hdec⟩ := zeroAtomLaw_decomposition α hsupp hz
    have h := zeroSelection_le_zeroQuantileValue (positiveLaw α) (zeroMass α) hρ1 B
    rwa [hdec] at h
  · unfold quantileDesignValue zeroQuantileValue
    rw [ite_eq_left (by linarith [not_lt.mp hz] : ρ ≤ zeroMass α)]
    exact min_le_left _ _

end ThresholdHC.ArbitraryLawAdaptation
