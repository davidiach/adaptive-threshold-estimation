import ThresholdHC.AnytimeLower.CoefficientCertificate
import ThresholdHC.AnytimeLower.FiniteFamily
import ThresholdHC.AnytimeLower.InflatedScale

noncomputable section
open MeasureTheory Real Set Filter
open scoped ENNReal Topology
namespace ThresholdHC.AnytimeLower
open ThresholdHC.Tier3 ThresholdHC.Tier6

theorem selection_le_coefficient_scale (μ : Measure Gap) [IsProbabilityMeasure μ]
    (ρ : ℝ) (hb : BddAbove (selectionCoefficients μ ρ)) {B : ℝ} (hB : 0 < B) :
    ThresholdHC.EntropyTail.selection μ ρ B ≤
      ENNReal.ofReal (selectionCoefficient μ ρ*ThresholdHC.EntropyTailQuantile.budgetScale B) := by
  have he := normalizedSelection_le_coefficient μ ρ hb hB
  have hs : 0 < sqrt B := sqrt_pos.mpr hB
  have hr : (ThresholdHC.EntropyTail.selection μ ρ B).toReal ≤
      selectionCoefficient μ ρ*ThresholdHC.EntropyTailQuantile.budgetScale B := by
    unfold ThresholdHC.EntropyTailQuantile.budgetScale
    rw [← div_eq_mul_inv]
    exact (le_div_iff₀ hs).mpr (by simpa only [normalizedSelection,mul_comm] using he)
  rw [← ENNReal.ofReal_toReal (ThresholdHC.HardBudget.finite_selection μ ρ B)]
  exact ENNReal.ofReal_le_ofReal hr

/-- The finite-coefficient branch of the law-dependent time-uniform lower bound. -/
theorem finite_coefficient_matching {R : Type} [MeasurableSpace R]
    (μ : Measure Gap) [IsProbabilityMeasure μ]
    {ρ δ : ℝ} (hρ : 0 < ρ) (hρ4 : ρ ≤ 1/4)
    (hb : BddAbove (selectionCoefficients μ ρ))
    (A : AdaptiveEstimator R) (H : ∀ n, R × Prefix n → ℝ)
    (hH : ∀ n, Measurable (H n)) (hd : 0 ≤ δ ∧ δ ≤ 1/2)
    (t : ℕ → ℝ) (hacc : OnlineAccuracy μ A H ρ δ t) (M : ℕ) :
    ∃ n : ℕ, M ≤ n ∧ ENNReal.ofReal ((10:ℝ)⁻¹^22) *
      ThresholdHC.EntropyTail.selection μ ρ ((n:ℝ)/budgetInflation δ n) ≤ ENNReal.ofReal (t n) := by
  obtain ⟨Q,J,hQ,hJ,hI,hΔ,hcert⟩ := coefficient_certificate μ hρ hρ4 hb
  let C := selectionCoefficient μ ρ
  let Δ := signMean μ Q.high.val-signMean μ Q.low.val
  let s := certificateScale J
  let N := testingBudget δ s
  let τ := sqrt ((64/3)*J)/8
  have hC : 0 < C := selectionCoefficient_pos μ hρ (by linarith) hb
  have hτ : 0 < τ := by dsimp [τ]; positivity
  have he (k : ℕ) : geometricScale τ k = s k := by
    dsimp [τ,s,certificateScale,centralShift,geometricScale]
    ring
  have hN := testingBudget_tendsto (by linarith : δ < 1) s
    (certificateScale_pos hJ) certificateScale_antitone
  have hf := certificate_scheduled_frequently μ A H hH hd t hacc Q hQ hJ hI hΔ
  have hdense : ∀ᶠ k : ℕ in atTop, (k:ℝ) ≤ ((k:ℝ)+2)^2 := by
    apply Filter.Eventually.of_forall
    intro k
    have := Nat.cast_nonneg (α:=ℝ) k
    nlinarith [sq_nonneg (k:ℝ)]
  have hscale := dense_inflatedScale_bound hd hτ id monotone_id hdense
  simp only [id_eq,he] at hscale
  have hgap : ((10:ℝ)⁻¹^17)*C*sqrt J/2 ≤ Δ := by
    have hsq := sq_sqrt hJ.le
    change (((10:ℝ)⁻¹^17)*C/2)^2*J ≤ Δ^2 at hcert
    have hnon : 0 ≤ ((10:ℝ)⁻¹^17)*C*sqrt J/2 := by positivity
    have hid : (((10:ℝ)⁻¹^17)*C*sqrt J/2)^2 =
        (((10:ℝ)⁻¹^17)*C/2)^2*J := by
      rw [div_pow,mul_pow,mul_pow,hsq]
      ring
    nlinarith only [hcert,hid,hnon,hΔ]
  have hroot : sqrt ((64/3)*J) ≤ 5*sqrt J := by
    have hsq := sq_sqrt (show 0 ≤ (64/3:ℝ)*J by positivity)
    nlinarith [sq_sqrt hJ.le,sqrt_nonneg ((64/3)*J),sqrt_nonneg J]
  obtain ⟨k,hk,hsk,hMk⟩ := (hf.and_eventually (hscale.and
    (hN.eventually (eventually_ge_atTop M)))).exists
  have hnp : (0:ℝ) < N k := by exact_mod_cast hsk.1
  have hB : 0 < (N k:ℝ)/budgetInflation δ (N k) := div_pos hnp hsk.2.1
  have hK := selection_le_coefficient_scale μ ρ hb hB
  have hsc : inflatedScale δ (N k) ≤ 5*s k := hsk.2.2
  have hK' : ThresholdHC.EntropyTail.selection μ ρ ((N k:ℝ)/budgetInflation δ (N k)) ≤
      ENNReal.ofReal (25*C*sqrt J*centralShift k) := by
    apply hK.trans (ENNReal.ofReal_le_ofReal _)
    change C*inflatedScale δ (N k) ≤ _
    have hh := mul_le_mul_of_nonneg_left hsc hC.le
    have hh' := mul_le_mul_of_nonneg_right hroot (centralShift_bounds k).1.le
    change sqrt ((64/3)*J)*centralShift k ≤ _ at hh'
    dsimp [s,certificateScale] at hh
    nlinarith only [hh, mul_le_mul_of_nonneg_left hh' (show 0 ≤ 5*C by positivity)]
  have hlast : ((10:ℝ)⁻¹^22)*(25*C*sqrt J*centralShift k) ≤
      centralShift k*Δ/18 := by
    have hh := mul_le_mul_of_nonneg_right hgap (centralShift_bounds k).1.le
    have hn : 0 ≤ C*sqrt J*centralShift k :=
      mul_nonneg (mul_nonneg hC.le (sqrt_nonneg J)) (centralShift_bounds k).1.le
    norm_num at hh ⊢
    nlinarith only [hh,hn]
  refine ⟨N k,hMk,?_⟩
  calc
    _ ≤ ENNReal.ofReal ((10:ℝ)⁻¹^22)*ENNReal.ofReal (25*C*sqrt J*centralShift k) :=
      mul_le_mul_right hK' _
    _ = ENNReal.ofReal (((10:ℝ)⁻¹^22)*(25*C*sqrt J*centralShift k)) := by
      rw [ENNReal.ofReal_mul (by positivity : 0 ≤ (10:ℝ)⁻¹^22)]
    _ ≤ ENNReal.ofReal (centralShift k*Δ/18) := ENNReal.ofReal_le_ofReal hlast
    _ ≤ ENNReal.ofReal (t (N k)) := ENNReal.ofReal_le_ofReal hk

end ThresholdHC.AnytimeLower
