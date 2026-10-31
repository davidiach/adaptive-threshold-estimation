import ThresholdHC.StoppingProgram.InformationFiniteness
import ThresholdHC.StoppingProgram.AbsorbedPriors

/-! Midpoint references are automatically finite on every capped prefix,
and their quadratic information is within factors four and eight of squared
Hellinger distance, including zero-probability outcomes. -/

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace ThresholdHC.StoppingProgram
open ThresholdHC.Tier6 (Gap SignLaw)

theorem midpoint_prefixCoefficient (μ : Measure Gap) [IsProbabilityMeasure μ]
    (q r : SignLaw) (n k : ℕ) (hk : k ≤ n) :
    prefixCoefficient μ (midpointPrior q r) n k =
      (prefixCoefficient μ q n k+prefixCoefficient μ r n k)/2 := by
  let s : CountState n := ⟨⟨n,by omega⟩,⟨k,by change k < n+1; omega⟩⟩
  have he := midpointPrior_countCoefficient μ q r s
  change (n.choose k:ℝ)*prefixCoefficient μ (midpointPrior q r) n k =
    ((n.choose k:ℝ)*prefixCoefficient μ q n k+(n.choose k:ℝ)*prefixCoefficient μ r n k)/2 at he
  have hc : (n.choose k:ℝ) ≠ 0 := by exact_mod_cast (Nat.choose_pos hk).ne'
  apply mul_left_cancel₀ hc
  nlinarith [he]

theorem midpoint_prefixInformation_finite (μ : Measure Gap) [IsProbabilityMeasure μ]
    (q r : SignLaw) (n k : ℕ) (hk : k ≤ n) :
    prefixInformation μ (midpointFourPriors q r) n k ≠ ⊤ := by
  apply ne_of_lt
  apply (perspective_finite_iff (prefixCoefficient_nonneg μ (midpointPrior q r) n k)).mpr
  by_cases hp : 0 < prefixCoefficient μ (midpointPrior q r) n k
  · exact Or.inl hp
  · apply Or.inr
    change prefixCoefficient μ r n k-prefixCoefficient μ q n k = 0
    rw [midpoint_prefixCoefficient μ q r n k hk] at hp
    linarith [prefixCoefficient_nonneg μ q n k,prefixCoefficient_nonneg μ r n k]

theorem midpoint_informationRatio_finite (μ : Measure Gap) [IsProbabilityMeasure μ]
    (N : ℕ) (q r : SignLaw) : informationRatio μ N (midpointFourPriors q r) ≠ ⊤ :=
  ne_top_of_le_ne_top ENNReal.ofReal_ne_top (informationRatio_le_bellmanRatio μ N _
    (fun n k _ hk => midpoint_prefixInformation_finite μ q r n k hk))

theorem perspective_toReal_eq (x y : ℝ) (hy : 0 ≤ y) : (perspective x y).toReal = x^2/y := by
  by_cases hp : 0 < y
  · rw [perspective_pos hp,ENNReal.toReal_ofReal (div_nonneg (sq_nonneg x) hy)]
  · have hz : y = 0 := by linarith
    subst y
    by_cases hx : x = 0 <;> simp [perspective,hx]

theorem midpoint_prefixReward (μ : Measure Gap) [IsProbabilityMeasure μ]
    (q r : SignLaw) (n k : ℕ) (hk : k ≤ n) :
    prefixReward μ (midpointFourPriors q r) n k =
      (prefixCoefficient μ q n k-prefixCoefficient μ r n k)^2/
        ((prefixCoefficient μ q n k+prefixCoefficient μ r n k)/2) := by
  unfold prefixReward prefixInformation midpointFourPriors
  rw [perspective_toReal_eq _ _ (prefixCoefficient_nonneg μ _ _ _),midpoint_prefixCoefficient μ q r n k hk]
  ring

theorem midpoint_quadratic_hellinger (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    2*(Real.sqrt a-Real.sqrt b)^2 ≤ (a-b)^2/((a+b)/2) ∧
      (a-b)^2/((a+b)/2) ≤ 4*(Real.sqrt a-Real.sqrt b)^2 := by
  have hsa := Real.sq_sqrt ha
  have hsb := Real.sq_sqrt hb
  have hprod : 0 ≤ Real.sqrt a*Real.sqrt b := mul_nonneg (Real.sqrt_nonneg a) (Real.sqrt_nonneg b)
  have hid : (a-b)^2 = (Real.sqrt a-Real.sqrt b)^2*(Real.sqrt a+Real.sqrt b)^2 := by
    calc
      _ = ((Real.sqrt a)^2-(Real.sqrt b)^2)^2 := by rw [hsa,hsb]
      _ = _ := by ring
  by_cases hz : a+b = 0
  · have ha0 : a = 0 := by linarith
    have hb0 : b = 0 := by linarith
    simp [ha0,hb0]
  · have hp : 0 < (a+b)/2 := by positivity
    constructor
    · apply (le_div_iff₀ hp).mpr
      have hlow : a+b ≤ (Real.sqrt a+Real.sqrt b)^2 := by nlinarith
      have hh := mul_le_mul_of_nonneg_left hlow (sq_nonneg (Real.sqrt a-Real.sqrt b))
      nlinarith [hid]
    · apply (div_le_iff₀ hp).mpr
      have hu : (Real.sqrt a+Real.sqrt b)^2 ≤ 2*(a+b) := by nlinarith [sq_nonneg (Real.sqrt a-Real.sqrt b)]
      have hh := mul_le_mul_of_nonneg_left hu (sq_nonneg (Real.sqrt a-Real.sqrt b))
      nlinarith [hid]

end ThresholdHC.StoppingProgram
