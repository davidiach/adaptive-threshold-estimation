import ThresholdHC.ConfidenceTransferSteps.Specification
import ThresholdHC.ShiftedPower.Amplify
import ThresholdHC.ShiftedPower.RateScale
import ThresholdHC.RareAboveTwo.Budget
import ThresholdHC.Confidence.Lower

/-! The upper half of note (22) and the law-independent hard-cap family of the
remark after it.

The above-two RMS family `RareAboveTwo.above_two_upper` (budgets `B ≥ 1`), with the
constant half-rarity estimator for budgets `B < 1`, gives one family per budget
over the whole power-margin class with risk at most `max 1 C · aboveTwoRate a ρ b`.
The rate obeys the budget scaling `f b ≤ √(b'/b) f b'`, so the median amplification
`ShiftedPower.amplify_margin` yields a procedure with a cap of `⌊B⌋` flips on every
valid path and failure probability at most `δ` at radius
`27 · max 1 C · aboveTwoRate a ρ (B/ℓ)`. That rate equals
`min{ρ, √(ρℓ)/(a√B)}` (`aboveTwoRate_confidence`). -/

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace ThresholdHC.ConfidenceTransferSteps
open ThresholdHC.Tier6 ThresholdHC.RareAboveTwo

theorem aboveTwoRate_nonneg {a ρ b : ℝ} (ha : 0 ≤ a) (hρ : 0 ≤ ρ) :
    0 ≤ aboveTwoRate a ρ b :=
  le_min hρ (by positivity)

/-- The rate at the effective budget `B/ℓ` is the note's confidence rate. -/
theorem aboveTwoRate_confidence {a ρ B δ : ℝ} (hρ : 0 ≤ ρ) (hB : 0 < B)
    (hδ : 0 < δ) (hδ' : δ ≤ 1/4) :
    aboveTwoRate a ρ (B/Real.log (1/δ)) =
      min ρ (Real.sqrt (ρ * Real.log (1/δ)) / (a * Real.sqrt B)) := by
  have hℓ := ThresholdHC.Confidence.confidence_log_pos hδ hδ'
  have hs : 0 < Real.sqrt (Real.log (1/δ)) := Real.sqrt_pos.mpr hℓ
  unfold aboveTwoRate
  congr 1
  rw [Real.sqrt_div hB.le, Real.sqrt_mul hρ]
  rcases eq_or_ne a 0 with ha | ha
  · simp [ha]
  rcases eq_or_ne (Real.sqrt B) 0 with hb | hb
  · simp [hb]
  field_simp

/-- The budget scaling of the above-two rate. -/
theorem aboveTwoRate_scale {a ρ b b' : ℝ} (ha : 0 < a) (hρ : 0 ≤ ρ) (hb : 0 < b)
    (hbb : b ≤ b') :
    aboveTwoRate a ρ b ≤ Real.sqrt (b'/b) * aboveTwoRate a ρ b' := by
  obtain ⟨hc,he⟩ := ThresholdHC.ShiftedPower.rate_budget_scale ha hb hbb
  have hc0 : 0 ≤ Real.sqrt (b'/b) := Real.sqrt_nonneg _
  have hr (x : ℝ) : Real.sqrt ρ/(a*Real.sqrt x) = Real.sqrt ρ*((Real.sqrt x)⁻¹/a) := by
    rw [div_eq_mul_inv, mul_inv, mul_comm a⁻¹, ← div_eq_mul_inv]
  unfold aboveTwoRate
  rw [hr b, hr b', he, mul_min_of_nonneg _ _ hc0]
  apply min_le_min (le_mul_of_one_le_left hρ hc)
  apply le_of_eq
  ring

/-- The base RMS family at every positive budget, uniform over the power-margin
class. -/
theorem above_two_base {α a ρ C : ℝ} (ha : 0 < a) (ha' : a ≤ 1/2) (hρ : 0 < ρ)
    (hρ4 : ρ ≤ 1/4) {R : Type} [mR : MeasurableSpace R] {rule : ℝ → ℝ → ℝ → AdaptiveEstimator R}
    (hup : ∀ a ρ B : ℝ, 0 < a → a ≤ 1/2 → 0 < ρ → ρ ≤ 1/4 → 1 ≤ B →
      ∀ (μ : Measure Gap) [IsProbabilityMeasure μ], PowerMargin μ α a →
        RareBudget μ (rule a ρ B) ρ B ∧
        rareRisk μ (rule a ρ B) ρ ≤ ENNReal.ofReal (min (ρ/2) (C*Real.sqrt ρ/(a*Real.sqrt B))))
    (b : ℝ) (hb : 0 < b) :
    ∃ (S : Type) (_ : MeasurableSpace S) (A : AdaptiveEstimator S),
      ∀ (ν : Measure Gap) [IsProbabilityMeasure ν], PowerMargin ν α a →
        RareBudget ν A ρ b ∧ rareRisk ν A ρ ≤ ENNReal.ofReal (max 1 C * aboveTwoRate a ρ b) := by
  have hM : 1 ≤ max 1 C := le_max_left _ _
  have hM0 : 0 ≤ max 1 C := zero_le_one.trans hM
  have ht : 0 ≤ Real.sqrt ρ/(a*Real.sqrt b) := by positivity
  by_cases hb1 : 1 ≤ b
  · refine ⟨R, mR, rule a ρ b, ?_⟩
    intro ν _ hm
    obtain ⟨hw, hR⟩ := hup a ρ b ha ha' hρ hρ4 hb1 ν hm
    refine ⟨hw, hR.trans (ENNReal.ofReal_le_ofReal ?_)⟩
    rw [aboveTwoRate, mul_min_of_nonneg _ _ hM0]
    apply le_min
    · exact (min_le_left _ _).trans (by nlinarith)
    · have hb' := mul_le_mul_of_nonneg_right (le_max_right (1 : ℝ) C) ht
      exact (min_le_right _ _).trans (by simpa only [mul_div_assoc] using hb')
  · have hb1' : b < 1 := lt_of_not_ge hb1
    refine ⟨Unit, inferInstance, constantEstimator (ρ/2), ?_⟩
    intro ν _ _
    refine ⟨constant_rare_budget ν ρ b (ρ/2), (half_rarity_risk ν ρ hρ.le).trans
      (ENNReal.ofReal_le_ofReal ?_)⟩
    have hsb : Real.sqrt b < 1 := by simpa using Real.sqrt_lt_sqrt hb.le hb1'
    have hsb0 : 0 < Real.sqrt b := Real.sqrt_pos.mpr hb
    have hsρ : ρ ≤ Real.sqrt ρ := by
      have h1 : Real.sqrt ρ ≤ 1 := Real.sqrt_le_one.mpr (by linarith)
      have h2 : Real.sqrt ρ * Real.sqrt ρ = ρ := Real.mul_self_sqrt hρ.le
      nlinarith [Real.sqrt_nonneg ρ]
    have hden : 0 < a*Real.sqrt b := mul_pos ha hsb0
    have hρle : ρ ≤ Real.sqrt ρ/(a*Real.sqrt b) := by
      rw [le_div_iff₀ hden]
      have : a*Real.sqrt b ≤ 1 := by nlinarith
      nlinarith
    rw [aboveTwoRate, min_eq_left hρle]
    nlinarith

/-- The remark after note (22). -/
theorem above_two_confidence_family_proof : AboveTwoConfidenceFamilyStatement := by
  intro α hα
  obtain ⟨C, _, R, mR, rule, hup⟩ := above_two_upper α hα
  refine ⟨27 * max 1 C, by positivity, ?_⟩
  intro a ρ B δ ha ha' hρ hρ4 hB hδ hδ'
  have hM0 : 0 ≤ max 1 C := zero_le_one.trans (le_max_left _ _)
  have h := ThresholdHC.ShiftedPower.amplify_margin (α := α) (a := a) (ρ := ρ) (C := max 1 C)
    (fun b => aboveTwoRate a ρ b) hM0 hB hδ hδ'
    (fun b _ => aboveTwoRate_nonneg ha.le hρ.le)
    (fun b b' hb hbb => aboveTwoRate_scale ha hρ.le hb hbb)
    (fun b hb => above_two_base (mR := mR) ha ha' hρ hρ4 hup b hb)
  simpa only [aboveTwoRate_confidence hρ.le hB hδ hδ'] using h

end ThresholdHC.ConfidenceTransferSteps
