import ThresholdHC.StoppingProgram.ConstantInformation
import ThresholdHC.StoppingProgram.PrefixRisk
import ThresholdHC.StoppingProgram.TruncationLimit

/-! Universal rare-mean risk floor, proved using constant sign priors and
their latent-label information. This is independent of the entropy-tail law. -/

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace ThresholdHC.StoppingProgram
open ThresholdHC.Tier6 ThresholdHC.RareAboveTwo

theorem constant_pair_risk_floor {R : Type} [MeasurableSpace R]
    (μ : Measure Gap) [IsProbabilityMeasure μ] (A : AdaptiveEstimator R)
    (ρ B δ : ℝ) (hρ : 0 < ρ) (hρquarter : ρ ≤ 1/4) (hB : 0 ≤ B)
    (hδ : 0 ≤ δ) (hδρ : δ ≤ ρ/2) (hsmall : B*δ^2 ≤ ρ/16)
    (hbudget : RareBudget μ A ρ B) : ENNReal.ofReal (δ/4) ≤ rareRisk μ A ρ := by
  have hu : 0 ≤ ρ/2 ∧ ρ/2 ≤ 1 := by constructor <;> linarith
  have hv : 0 ≤ ρ/2+δ ∧ ρ/2+δ ≤ 1 := by constructor <;> linarith
  let q := constantPrior (ρ/2) hu
  let r := constantPrior (ρ/2+δ) hv
  let m := (ρ/2+(ρ/2+δ))/2
  have hm : 0 < m := by dsimp only [m]; linarith
  have hmρ : m ≤ ρ := by dsimp only [m]; linarith
  have hm1 : m < 1 := by linarith
  have hmhalf : ρ/2 ≤ m := by dsimp only [m]; linarith
  have hden : 3*ρ/8 ≤ m*(1-m) := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hmhalf) (show 0 ≤ 1-m by linarith),
      mul_nonneg hρ.le (show 0 ≤ 1-m-3/4 by linarith)]
  have hq : RarePrior μ ρ q := by change signMean μ (constantPrior _ _).val ≤ ρ; rw [constantPrior_mean]; linarith
  have hr : RarePrior μ ρ r := by change signMean μ (constantPrior _ _).val ≤ ρ; rw [constantPrior_mean]; linarith
  apply prefix_lower_transfer μ A ρ B hρ.le hB hbudget q r hq hr
  intro N
  have hK : informationRatio μ N (midpointFourPriors q r) ≤ ENNReal.ofReal (δ^2/(m*(1-m))) := by
    have h := constant_informationRatio_bound μ N (ρ/2) (ρ/2+δ) m hu hv hm hm1
    have he : ρ/2+δ-ρ/2 = δ := by ring
    rw [he] at h
    simpa only [midpointFourPriors,q,r,constantPrior_midpoint] using h
  have hKr : (informationRatio μ N (midpointFourPriors q r)).toReal ≤ δ^2/(m*(1-m)) := by
    have hh := ENNReal.toReal_mono ENNReal.ofReal_ne_top hK
    simpa only [ENNReal.toReal_ofReal (by positivity : 0 ≤ δ^2/(m*(1-m)))] using hh
  have hKB : (informationRatio μ N (midpointFourPriors q r)).toReal*B ≤ 2 := by
    have hp : 0 < m*(1-m) := mul_pos hm (by linarith)
    have hb : δ^2/(m*(1-m))*B ≤ 2 := by
      rw [div_mul_eq_mul_div]
      apply (div_le_iff₀ hp).mpr
      nlinarith [hsmall,hden]
    exact (mul_le_mul_of_nonneg_right hKr hB).trans hb
  have hmid := mixPrior_rare μ q r hq hr (1/2) (by norm_num)
  have hgap : signMean μ q.val ≤ signMean μ r.val := by
    simp only [q,r,constantPrior_mean]
    linarith
  have hl := observable_prefix_risk μ A q r N B hB (hbudget _ hmid) hgap
    (prefixTruncation A ρ N) (measurable_prefixTruncation A ρ N)
  apply le_trans (ENNReal.ofReal_le_ofReal ?_) hl
  simp only [q,r,constantPrior_mean]
  have he : ρ/2+δ-ρ/2 = δ := by ring
  rw [he]
  nlinarith [mul_nonneg hδ (show 0 ≤ 2-(informationRatio μ N (midpointFourPriors q r)).toReal*B by linarith)]

theorem bernoulli_label_floor {R : Type} [MeasurableSpace R]
    (μ : Measure Gap) [IsProbabilityMeasure μ] (A : AdaptiveEstimator R)
    (ρ B : ℝ) (hρ : 0 < ρ) (hρquarter : ρ ≤ 1/4) (hB : 0 < B)
    (hbudget : RareBudget μ A ρ B) :
    ENNReal.ofReal ((1/16:ℝ)*min ρ (Real.sqrt (ρ/B))) ≤ rareRisk μ A ρ := by
  let δ := min ρ (Real.sqrt (ρ/B))/4
  have hδ : 0 ≤ δ := by dsimp only [δ]; positivity
  have hδρ : δ ≤ ρ/2 := by
    have h := min_le_left ρ (Real.sqrt (ρ/B))
    dsimp only [δ]
    linarith
  have hδs : δ ≤ Real.sqrt (ρ/B)/4 := by
    exact div_le_div_of_nonneg_right (min_le_right _ _) (by norm_num)
  have hsq : δ^2 ≤ ρ/B/4^2 := by
    calc
      _ ≤ (Real.sqrt (ρ/B)/4)^2 := (sq_le_sq₀ hδ (by positivity)).mpr hδs
      _ = _ := by rw [div_pow,Real.sq_sqrt (div_nonneg hρ.le hB.le)]
  have hsmall : B*δ^2 ≤ ρ/16 := by
    have hh := mul_le_mul_of_nonneg_left hsq hB.le
    have he : B*(ρ/B/4^2) = ρ/16 := by field_simp; ring
    rwa [he] at hh
  have h := constant_pair_risk_floor μ A ρ B δ hρ hρquarter hB.le hδ hδρ hsmall hbudget
  convert h using 1
  congr 1
  dsimp only [δ]
  ring

theorem bernoulli_label_minimax_floor (μ : Measure Gap) [IsProbabilityMeasure μ]
    (ρ B : ℝ) (hρ : 0 < ρ) (hρquarter : ρ ≤ 1/4) (hB : 0 < B) :
    ENNReal.ofReal ((1/16:ℝ)*min ρ (Real.sqrt (ρ/B))) ≤ rareMinimaxRisk μ ρ B := by
  apply le_sInf
  rintro t ⟨R,mR,A,hbudget,rfl⟩
  exact bernoulli_label_floor μ A ρ B hρ hρquarter hB hbudget

end ThresholdHC.StoppingProgram
