import ThresholdHC.RareAboveTwo.Specification
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.Layercake

/-! Consequences of the full power-margin class, without a density assumption. -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace ThresholdHC.RareAboveTwo
open ThresholdHC.Tier6

theorem exactPower_margin (μ : Measure Gap) (α a : ℝ) (h : ExactPowerLaw μ α a) :
    PowerMargin μ α a := by
  intro x hx _
  rw [h x hx]
  exact min_le_right _ _

theorem exactPower_support (μ : Measure Gap) [IsProbabilityMeasure μ]
    (α a : ℝ) (ha : 0 < a) (h : ExactPowerLaw μ α a) :
    ∀ᵐ d : Gap ∂μ, (d : ℝ) ≤ a := by
  apply (mem_ae_iff_prob_eq_one (measurableSet_le measurable_subtype_coe measurable_const)).2
  have hc := h a ha
  simp only [div_self ha.ne',Real.one_rpow,min_self] at hc
  exact (ENNReal.toReal_eq_one_iff _).mp hc

/-- A tail comparison gives a finite moment with an explicit universal factor. -/
theorem moment_of_power_tail {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (f : Ω → ℝ)
    (hf : Measurable f) (hn : ∀ ω, 0 ≤ f ω) (p : ℝ) (hp : 1 < p)
    (ht : ∀ t : ℝ, 1 < t → μ {ω | t ≤ f ω} ≤ ENNReal.ofReal (t^(-p))) :
    (∫⁻ ω, ENNReal.ofReal (f ω) ∂μ) ≤ ENNReal.ofReal (1+1/(p-1)) := by
  rw [lintegral_eq_lintegral_meas_le μ (ae_of_all _ hn) hf.aemeasurable]
  have hu : Ioi (0 : ℝ) = Ioc 0 1 ∪ Ioi 1 := by ext t; simp
  rw [hu,lintegral_union measurableSet_Ioi (by exact disjoint_left.mpr (fun t ht ht' => (not_lt_of_ge ht.2 ht')))]
  have hlow : (∫⁻ t : ℝ in Ioc 0 1, μ {ω | t ≤ f ω}) ≤ 1 := by
    calc
      _ ≤ ∫⁻ _t : ℝ in Ioc 0 1, (1 : ℝ≥0∞) := lintegral_mono (fun _ => prob_le_one)
      _ = 1 := by simp
  have htail : (∫⁻ t : ℝ in Ioi 1, μ {ω | t ≤ f ω}) ≤ ENNReal.ofReal (1/(p-1)) := by
    calc
      _ ≤ ∫⁻ t : ℝ in Ioi 1, ENNReal.ofReal (t^(-p)) := by
        apply setLIntegral_mono' measurableSet_Ioi
        exact fun t ht' => ht t ht'
      _ = ENNReal.ofReal (∫ t : ℝ in Ioi 1, t^(-p)) := by
        symm
        apply ofReal_integral_eq_lintegral_ofReal
        · exact integrableOn_Ioi_rpow_of_lt (by linarith) (by norm_num)
        · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht'
          exact Real.rpow_nonneg (by have : 1 < t := ht'; linarith) _
      _ = ENNReal.ofReal (1/(p-1)) := by
        rw [integral_Ioi_rpow_of_lt (by linarith : -p < -1) (by norm_num : (0 : ℝ) < 1)]
        congr 1
        simp only [Real.one_rpow]
        convert neg_div_neg_eq (1 : ℝ) (p-1) using 1; ring
  have hnon : 0 ≤ 1/(p-1) := by positivity
  simpa only [ENNReal.ofReal_add zero_le_one hnon,ENNReal.ofReal_one] using add_le_add hlow htail

theorem inverse_power_tail (μ : Measure Gap) [IsProbabilityMeasure μ]
    (α a s : ℝ) (ha : 0 < a) (hs : 0 < s) (h : PowerMargin μ α a)
    (t : ℝ) (ht : 1 < t) :
    μ {d : Gap | t ≤ (a/(d : ℝ))^s} ≤ ENNReal.ofReal (t^(-(α/s))) := by
  have ht0 : 0 < t := by linarith
  have hroot : 1 < t^(s⁻¹) := Real.one_lt_rpow ht (inv_pos.mpr hs)
  have hx : 0 < a/t^(s⁻¹) := div_pos ha (by positivity)
  have hxa : a/t^(s⁻¹) < a := (div_lt_self ha hroot)
  have hsub : {d : Gap | t ≤ (a/(d : ℝ))^s} ⊆ {d : Gap | (d : ℝ) ≤ a/t^(s⁻¹)} := by
    intro d hd
    have hr : t^(s⁻¹) ≤ a/(d : ℝ) :=
      (Real.rpow_inv_le_iff_of_pos ht0.le (div_pos ha d.property.1).le hs).2 hd
    exact (le_div_iff₀ (Real.rpow_pos_of_pos ht0 _)).2
      (by nlinarith [(le_div_iff₀ d.property.1).1 hr])
  apply (measure_mono hsub).trans
  rw [← ofReal_measureReal]
  apply (ENNReal.ofReal_le_ofReal (h _ hx hxa)).trans_eq
  congr 1
  have he : (a/t^(s⁻¹))/a = (t^(s⁻¹))⁻¹ := by field_simp
  rw [he,Real.inv_rpow (Real.rpow_nonneg ht0.le _),← Real.rpow_mul ht0.le,
    ← Real.rpow_neg ht0.le]
  congr 1
  ring

/-- Uniform inverse moments below the margin exponent, including singular laws. -/
theorem margin_inverse_moment (μ : Measure Gap) [IsProbabilityMeasure μ]
    (α a s : ℝ) (ha : 0 < a) (hs : 0 < s) (hsα : s < α) (h : PowerMargin μ α a) :
    (∫⁻ d : Gap, ENNReal.ofReal ((a/(d : ℝ))^s) ∂μ) ≤
      ENNReal.ofReal (1+1/(α/s-1)) := by
  apply moment_of_power_tail μ _ (by fun_prop)
    (fun d => Real.rpow_nonneg (div_pos ha d.property.1).le _) (α/s)
    ((one_lt_div hs).2 hsα)
  exact inverse_power_tail μ α a s ha hs h

theorem margin_inverse_integrable (μ : Measure Gap) [IsProbabilityMeasure μ]
    (α a s : ℝ) (ha : 0 < a) (hs : 0 < s) (hsα : s < α) (h : PowerMargin μ α a) :
    Integrable (fun d : Gap => (a/(d : ℝ))^s) μ := by
  refine ⟨(show Measurable (fun d : Gap => (a/(d : ℝ))^s) by fun_prop).aestronglyMeasurable,?_⟩
  rw [hasFiniteIntegral_iff_ofReal (ae_of_all _ (fun d =>
    Real.rpow_nonneg (div_pos ha d.property.1).le _))]
  exact (margin_inverse_moment μ α a s ha hs hsα h).trans_lt ENNReal.ofReal_lt_top

theorem margin_inverse_integral (μ : Measure Gap) [IsProbabilityMeasure μ]
    (α a s : ℝ) (ha : 0 < a) (hs : 0 < s) (hsα : s < α) (h : PowerMargin μ α a) :
    (∫ d : Gap, (a/(d : ℝ))^s ∂μ) ≤ 1+1/(α/s-1) := by
  have hi := margin_inverse_integrable μ α a s ha hs hsα h
  have hb := margin_inverse_moment μ α a s ha hs hsα h
  rw [← ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ (fun d =>
    Real.rpow_nonneg (div_pos ha d.property.1).le _))] at hb
  exact (ENNReal.ofReal_le_ofReal_iff (by have := (one_lt_div hs).2 hsα; positivity)).1 hb

end ThresholdHC.RareAboveTwo
