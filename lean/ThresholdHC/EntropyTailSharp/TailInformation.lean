import ThresholdHC.FiniteQuantile.TailInformation

/-! Every prefix likelihood and its posterior-energy potential are bounded and measurable, including at impossible words. -/
noncomputable section
open MeasureTheory Set Real
open scoped BigOperators ENNReal
namespace ThresholdHC.EntropyTailSharp
open ThresholdHC.FiniteQuantile
open ThresholdHC.Tier6 ThresholdHC.StoppingProgram ThresholdHC.CriticalEntropy ThresholdHC.EntropyTailQuantile

theorem mixture_quadratic_bound_of_integrable (μ : Measure Gap) [IsFiniteMeasure μ]
    (D M V : Gap → ℝ) (hiD : Integrable D μ) (hiM : Integrable M μ) (hiV : Integrable V μ)
    (hM : ∀ g, 0 ≤ M g)
    (hlocal : ∀ g y, 2*y*D g - y^2*M g ≤ V g) :
    (∫ g, D g ∂μ)^2 / (∫ g, M g ∂μ) ≤ ∫ g, V g ∂μ := by
  have hint (y : ℝ) : 2*y*(∫ g, D g ∂μ) - y^2*(∫ g, M g ∂μ) ≤ ∫ g, V g ∂μ := by
    calc
      _ = ∫ g, (2*y*D g - y^2*M g) ∂μ := by
        rw [integral_sub (hiD.const_mul _) (hiM.const_mul _), integral_const_mul, integral_const_mul]
      _ ≤ _ := integral_mono ((hiD.const_mul _).sub (hiM.const_mul _)) hiV (fun g => hlocal g y)
  rcases (integral_nonneg hM : 0 ≤ ∫ g, M g ∂μ).eq_or_lt with hz | hp
  · simpa [← hz] using hint 0
  · have hh := hint ((∫ g, D g ∂μ)/(∫ g, M g ∂μ))
    convert hh using 1
    field_simp
    ring

theorem tail_information_ratio_general (μ : Measure Gap) [IsProbabilityMeasure μ]
    {ρ h : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hh : 0 ≤ h) (cap : ℕ) :
    informationRatio μ cap (midpointFourPriors (tailEndpoint μ hρ hρ1 hh false)
      (tailEndpoint μ hρ hρ1 hh true)) ≤ ENNReal.ofReal (h^2/4) := by
  let w := cutWeight (quantileThreshold μ ρ) (quantileBoundaryFraction μ ρ)
  let e := tailEpsilon h
  let low := tailEndpoint μ hρ hρ1 hh false
  let high := tailEndpoint μ hρ hρ1 hh true
  let mid := midpointPrior low high
  let M := fun n k (g : Gap) => w g * midpointMass g n k +
    (1-w g) * prefixLikelihood false n k g
  let D := fun n k (g : Gap) => 2*w g*e g *
    (prefixLikelihood true n k g - prefixLikelihood false n k g)
  let P := fun n k (g : Gap) => w g*(16*(e g)^2)*prefixEnergy g n k
  have hw (g : Gap) : w g ∈ Icc (0:ℝ) 1 := cutWeight_range
    ⟨(quantileBoundaryFraction_properties μ hρ hρ1).1,
     (quantileBoundaryFraction_properties μ hρ hρ1).2.1⟩ g
  have hm (g : Gap) : mid.val g = w g / 2 := by
    dsimp [mid, midpointPrior, mixPrior, low, high, tailEndpoint, w, e]
    ring
  let mix (q : SignLaw) (n k : ℕ) (g : Gap) :=
    q.val g * prefixLikelihood true n k g + (1-q.val g) * prefixLikelihood false n k g
  have hmix (q : SignLaw) (n k : ℕ) : Integrable (mix q n k) μ := by
    have h := (CapIdentification.integrable_weighted_prefix μ q true n k).add
      ((CapIdentification.integrable_prefixLikelihood μ false n k).sub
        (CapIdentification.integrable_weighted_prefix μ q false n k))
    convert h using 1
    funext g
    dsimp [mix]
    ring
  have hMf (n k : ℕ) : mix mid n k = M n k := by
    funext g
    dsimp only [mix,M,midpointMass]
    rw [hm g]
    ring
  have hDf (n k : ℕ) : mix high n k - mix low n k = D n k := by
    funext g
    dsimp [mix,D,low,high,tailEndpoint,e,w]
    ring
  have hMi (n k : ℕ) : Integrable (M n k) μ := (hMf n k) ▸ hmix mid n k
  have hDi (n k : ℕ) : Integrable (D n k) μ := (hDf n k) ▸ (hmix high n k).sub (hmix low n k)
  have hM (n k : ℕ) : prefixCoefficient μ mid n k = ∫ g, M n k g ∂μ := by
    change (∫ g, mix mid n k g ∂μ) = _
    rw [hMf]
  have hD (n k : ℕ) : prefixCoefficient μ high n k - prefixCoefficient μ low n k =
      ∫ g, D n k g ∂μ := by
    change (∫ g, mix high n k g ∂μ) - (∫ g, mix low n k g ∂μ) = _
    rw [← integral_sub (hmix high n k) (hmix low n k), ← hDf]
    rfl
  have hPi (n k : ℕ) : Integrable (P n k) μ := by
    have hlik (s : Bool) : Measurable (prefixLikelihood s n k) := by
      cases s <;> unfold prefixLikelihood <;> simp only [ite_true, Bool.false_eq_true, ite_false] <;> fun_prop
    have hwm : Measurable w := measurable_cutWeight _ _
    have hem : Measurable e := by
      change Measurable (fun g : Gap => min (1:ℝ) (h/(g:ℝ))/16)
      fun_prop
    apply Integrable.of_bound (C := 1)
    · apply Measurable.aestronglyMeasurable
      dsimp only [P,prefixEnergy,posteriorEnergy]
      fun_prop
    · apply Filter.Eventually.of_forall
      intro g
      have he := tailEpsilon_bounds hh g
      have hp0 := prefixLikelihood_nonneg true n k g
      have hm0 := prefixLikelihood_nonneg false n k g
      have hp1 := CapIdentification.prefixLikelihood_le_one true n k g
      have hm1 := CapIdentification.prefixLikelihood_le_one false n k g
      let a := prefixLikelihood true n k g / 2
      let b := prefixLikelihood false n k g / 2
      have ha : 0 ≤ a := by dsimp [a]; positivity
      have hb : 0 ≤ b := by dsimp [b]; positivity
      have hE : posteriorEnergy a b ≤ a+b := by
        rcases (add_nonneg ha hb).eq_or_lt with hz | hpos
        · simp [posteriorEnergy, ← hz]
        · apply (div_le_iff₀ hpos).mpr
          nlinarith only [mul_nonneg ha hb]
      have hbound : prefixEnergy g n k ≤ 1 := hE.trans (by dsimp [a,b]; linarith)
      have hnon : 0 ≤ prefixEnergy g n k := div_nonneg (sq_nonneg _) (add_nonneg ha hb)
      have hesq := (sq_le_sq₀ he.1 (by norm_num : (0:ℝ) ≤ 1/16)).mpr he.2.1
      have hwgt : w g * (16*(e g)^2) ≤ 1 :=
        (mul_le_of_le_one_left (by positivity) (hw g).2).trans (by dsimp [e]; nlinarith only [hesq])
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (mul_nonneg (hw g).1 (by positivity)) hnon)]
      exact (mul_le_of_le_one_left hnon hwgt).trans hbound
  have hmid (g : Gap) (n k : ℕ) : 0 ≤ midpointMass g n k := by
    unfold midpointMass
    positivity [prefixLikelihood_nonneg true n k g, prefixLikelihood_nonneg false n k g]
  apply informationRatio_of_potential μ low high (h^2/4) (fun n k => ∫ g, P n k g ∂μ) _ _ _ cap
  · simp [P, prefixEnergy, posteriorEnergy, prefixLikelihood]
  · intro n k hk
    rw [midpoint_prefixReward μ low high n k hk, ← midpoint_prefixCoefficient μ low high n k hk]
    have hsq : (prefixCoefficient μ low n k - prefixCoefficient μ high n k)^2 =
        (prefixCoefficient μ high n k - prefixCoefficient μ low n k)^2 := by ring
    rw [hsq, hD, hM]
    apply mixture_quadratic_bound_of_integrable μ (D n k) (M n k) (P n k) (hDi n k) (hMi n k) (hPi n k)
    · intro g
      exact add_nonneg (mul_nonneg (hw g).1 (hmid g n k))
        (mul_nonneg (sub_nonneg.mpr (hw g).2) (prefixLikelihood_nonneg false n k g))
    · intro g y
      have hlocal := fractional_word_bound
        (a := prefixLikelihood true n k g / 2) (b := prefixLikelihood false n k g / 2)
        (by positivity [prefixLikelihood_nonneg true n k g])
        (by positivity [prefixLikelihood_nonneg false n k g]) (hw g).1 (hw g).2 (e g) y
      dsimp [D,M,P,midpointMass,prefixEnergy]
      convert hlocal using 1; ring
  · intro n k hk
    rw [hM, ← integral_add (hPi _ _) (hPi _ _), ← integral_const_mul,
      ← integral_add (hPi n k) ((hMi n k).const_mul _)]
    apply integral_mono ((hPi _ _).add (hPi _ _)) ((hPi n k).add ((hMi n k).const_mul _))
    intro g
    have he := tailEpsilon_bounds hh g
    have hsq := (sq_le_sq₀ (mul_nonneg he.1 g.property.1.le)
      (div_nonneg hh (by norm_num : (0:ℝ) ≤ 16))).mpr he.2.2
    have hscale : 64*(e g)^2*(g:ℝ)^2 ≤ h^2/4 := by nlinarith only [hsq]
    have hweight : 0 ≤ w g * (16*(e g)^2) := mul_nonneg (hw g).1 (by positivity)
    have hchildren := mul_le_mul_of_nonneg_left (prefixEnergy_step g hk) hweight
    have hpay := mul_le_mul_of_nonneg_right hscale (mul_nonneg (hw g).1 (hmid g n k))
    have hrest := mul_nonneg (div_nonneg (sq_nonneg h) (by norm_num : (0:ℝ) ≤ 4))
      (mul_nonneg (sub_nonneg.mpr (hw g).2) (prefixLikelihood_nonneg false n k g))
    simp only [Pi.add_apply, P, M]
    nlinarith only [hchildren, hpay, hrest]

end ThresholdHC.EntropyTailSharp
