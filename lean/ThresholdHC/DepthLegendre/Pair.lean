import ThresholdHC.DepthLegendre.Moments
import ThresholdHC.DepthLegendre.QuadraticLaw
import ThresholdHC.CapIdentification.StoppedMatching

/-! The explicit hard pair of `thm:cap` in
`research/2026-10-27-nonlinear-population/upper/proof-body.tex` (lines 89-128):
`q_±(d) = (1 ± u_K(d/h))/2 · 1{d ≤ h}`, `h = a √ρ`, for the exact quadratic law.
`|u_K| ≤ 1` makes both admissible sign laws. The change of variable `d = h x`
gives the targets `ρ/2 (1 ± m_K)`, each at most `ρ`, and
`∫ (q_+ - q_-) d^(2j+1) dμ = 2ρ h^(2j+1) ∫₀¹ x^(2j+2) u_K = 0` for `j < K`. Then
`CapIdentification` turns the matching odd moments into equal word
probabilities through depth `2K`, and bounds the separation by the cap-`2K`
diameter (a Lean-only consequence). -/

noncomputable section
namespace ThresholdHC.DepthLegendre
open MeasureTheory Polynomial
open ThresholdHC.Tier6 (Gap SignLaw signMean)
open ThresholdHC.RareAboveTwo (ExactPowerLaw RarePrior)
open ThresholdHC.CapIdentification (OddMomentMatch capDiameter capDiameter_attained
  odd_moments_iff_count_match wordLikelihood_eq_of_count_match)

theorem depthSign_bounds (K : ℕ) (hK : 1 ≤ K) {a ρ : ℝ} (ha : 0 < a) (hρ : 0 < ρ)
    (plus : Bool) (d : Gap) : 0 ≤ depthSign K a ρ plus d ∧ depthSign K a ρ plus d ≤ 1 := by
  have hh : 0 < a * Real.sqrt ρ := mul_pos ha (Real.sqrt_pos.mpr hρ)
  unfold depthSign
  by_cases hd : (d:ℝ) ≤ a * Real.sqrt ρ
  · have hx : (d:ℝ) / (a * Real.sqrt ρ) ∈ Set.Icc (0:ℝ) 1 :=
      ⟨div_nonneg d.2.1.le hh.le, (div_le_one hh).mpr hd⟩
    have hb := abs_le.mp (abs_depthPolynomial_le_one K hK _ hx)
    simp only [hd, ↓reduceIte]
    cases plus
    · simp only [Bool.false_eq_true, ↓reduceIte]
      constructor <;> linarith [hb.1, hb.2]
    · simp only [↓reduceIte]
      constructor <;> linarith [hb.1, hb.2]
  · simp only [hd, ↓reduceIte]
    exact ⟨le_refl 0, zero_le_one⟩

theorem measurable_depthSign (K : ℕ) (a ρ : ℝ) (plus : Bool) :
    Measurable (depthSign K a ρ plus) := by
  unfold depthSign
  exact Measurable.ite (measurableSet_le measurable_subtype_coe measurable_const)
    ((measurable_const.add (measurable_const.mul ((depthPolynomial K).continuous.measurable.comp
      (measurable_subtype_coe.div_const _)))).div_const 2) measurable_const

/-- The targets `θ_± = ρ/2 (1 ± m_K)`. -/
theorem depthSign_mean (μ : Measure Gap) [IsProbabilityMeasure μ] {a ρ : ℝ}
    (ha : 0 < a) (ha2 : a ≤ 1/2) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hm : ExactPowerLaw μ 2 a)
    (K : ℕ) (plus : Bool) :
    signMean μ (depthSign K a ρ plus) =
      ρ/2 * (1 + (if plus then (1:ℝ) else -1) * depthMoment K) := by
  set s : ℝ := if plus then (1:ℝ) else -1
  have h := quadratic_cut_integral μ ha ha2 hρ hρ1 hm
    (fun x => (1 + s * (depthPolynomial K).eval x) / 2)
    ((continuous_const.add (continuous_const.mul (depthPolynomial K).continuous)).div_const 2)
  unfold signMean
  refine h.trans ?_
  have he : (fun x : ℝ => 2 * ρ * x * ((1 + s * (depthPolynomial K).eval x) / 2)) =
      fun x => ρ * x + (s * ρ / 2) * (2 * x * (depthPolynomial K).eval x) := by
    funext x
    ring
  rw [he, intervalIntegral.integral_add, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul, integral_id, depthPolynomial_first_moment]
  · ring
  · exact (continuous_const.mul continuous_id).intervalIntegrable 0 1
  · exact (continuous_const.mul ((continuous_const.mul continuous_id).mul
      (depthPolynomial K).continuous)).intervalIntegrable 0 1

/-- `∫ (q_+ - q_-) d^(2j+1) dμ = 0` for `j < K`. -/
theorem depthSign_odd_moment (μ : Measure Gap) [IsProbabilityMeasure μ] {a ρ : ℝ}
    (ha : 0 < a) (ha2 : a ≤ 1/2) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hm : ExactPowerLaw μ 2 a)
    (K : ℕ) (hK : 1 ≤ K) (j : ℕ) (hj : j < K) :
    ∫ d, (depthSign K a ρ true d - depthSign K a ρ false d) * (d:ℝ)^(2*j+1) ∂μ = 0 := by
  have hs : 0 < Real.sqrt ρ := Real.sqrt_pos.mpr hρ
  have hcut := quadratic_cut_integral μ ha ha2 hρ hρ1 hm
    (fun x => (a * Real.sqrt ρ)^(2*j+1) * (x^(2*j+1) * (depthPolynomial K).eval x))
    (continuous_const.mul ((continuous_pow _).mul (depthPolynomial K).continuous))
  have hpt : ∀ d : Gap, (depthSign K a ρ true d - depthSign K a ρ false d) * (d:ℝ)^(2*j+1) =
      if (d:ℝ) ≤ a * Real.sqrt ρ then (a * Real.sqrt ρ)^(2*j+1) *
        (((d:ℝ) / (a * Real.sqrt ρ))^(2*j+1) *
          (depthPolynomial K).eval ((d:ℝ) / (a * Real.sqrt ρ))) else 0 := by
    intro d
    unfold depthSign
    by_cases hd : (d:ℝ) ≤ a * Real.sqrt ρ
    · simp only [hd, ↓reduceIte, Bool.false_eq_true, div_pow]
      field_simp
      ring
    · simp only [hd, ↓reduceIte, sub_self, zero_mul]
  rw [integral_congr_ae (Filter.Eventually.of_forall hpt), hcut]
  have he : (fun x : ℝ => 2 * ρ * x * ((a * Real.sqrt ρ)^(2*j+1) *
      (x^(2*j+1) * (depthPolynomial K).eval x))) =
      fun x => (2 * ρ * (a * Real.sqrt ρ)^(2*j+1)) * (x^(2*j+2) * (depthPolynomial K).eval x) := by
    funext x
    ring
  rw [he, intervalIntegral.integral_const_mul, depthPolynomial_orthogonal K hK j hj, mul_zero]

theorem depthMoment_pos (K : ℕ) : 0 < depthMoment K := by
  unfold depthMoment
  positivity

theorem depthMoment_le_one (K : ℕ) : depthMoment K ≤ 1 := by
  unfold depthMoment
  rw [div_le_one (by positivity)]
  have : (0:ℝ) ≤ K := Nat.cast_nonneg K
  nlinarith

/-- `thm:cap`, the explicit pair. -/
theorem depthPair : DepthPairStatement := by
  intro μ _ a ρ K ha ha2 hρ hρ4 hK hm
  have ha2' : a ≤ 1/2 := ha2.le
  have hρ1 : ρ ≤ 1 := by linarith
  let qH : SignLaw := ⟨depthSign K a ρ true, measurable_depthSign K a ρ true,
    depthSign_bounds K hK ha hρ true⟩
  let qL : SignLaw := ⟨depthSign K a ρ false, measurable_depthSign K a ρ false,
    depthSign_bounds K hK ha hρ false⟩
  have hmH : signMean μ qH.val = ρ/2 * (1 + depthMoment K) := by
    have := depthSign_mean μ ha ha2' hρ hρ1 hm K true
    simp only [↓reduceIte, one_mul] at this
    exact this
  have hmL : signMean μ qL.val = ρ/2 * (1 - depthMoment K) := by
    have := depthSign_mean μ ha ha2' hρ hρ1 hm K false
    simp only [Bool.false_eq_true, ↓reduceIte, neg_mul, one_mul, ← sub_eq_add_neg] at this
    exact this
  have hm0 := depthMoment_pos K
  have hm1 := depthMoment_le_one K
  have hH : RarePrior μ ρ qH := by
    change signMean μ qH.val ≤ ρ
    rw [hmH]
    nlinarith
  have hL : RarePrior μ ρ qL := by
    change signMean μ qL.val ≤ ρ
    rw [hmL]
    nlinarith
  have hdiff : signMean μ qH.val - signMean μ qL.val = ρ / (((K:ℝ)+1) * (2*K+1)) := by
    rw [hmH, hmL, depthMoment]
    ring
  have hodd : OddMomentMatch μ qH qL (2*K) := by
    intro j
    have hj : j.val < K := by
      have := j.isLt
      omega
    exact depthSign_odd_moment μ ha ha2' hρ hρ1 hm K hK j.val hj
  have hcount := (odd_moments_iff_count_match μ qH qL (2*K)).mp hodd
  refine ⟨qH, qL, rfl, rfl, hH, hL, hmH, hmL, hdiff, hodd,
    fun n k hn hk => wordLikelihood_eq_of_count_match μ qH qL (2*K) hcount n k hn hk, ?_⟩
  obtain ⟨_, _, _, _, _, _, hmax⟩ := capDiameter_attained μ hρ.le (2*K)
  rw [← hdiff]
  exact hmax qH qL hH hL hodd

end ThresholdHC.DepthLegendre
