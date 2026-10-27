import ThresholdHC.Tier6.TestingModel
import ThresholdHC.Tier6.TestingFinite

noncomputable section
open MeasureTheory InformationTheory
open scoped ENNReal
namespace ThresholdHC.Tier6

theorem event_prob_le_of_squaredRisk_le {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (f : Ω → ℝ) (hf : Measurable f)
    (a t : ℝ) (ht : 0 < t) (s : Set Ω)
    (hs : ∀ x ∈ s, t ≤ (f x-a)^2)
    (hr : squaredRisk P f a ≤ ENNReal.ofReal (t/4)) : P.real s ≤ 1/4 := by
  have hm : Measurable (fun x => ENNReal.ofReal ((f x-a)^2)) := by fun_prop
  have hbound : ENNReal.ofReal t * P s ≤ ENNReal.ofReal (t/4) := by
    apply le_trans _ hr
    change ENNReal.ofReal t * P s ≤ ∫⁻ x, ENNReal.ofReal ((f x-a)^2) ∂P
    apply le_trans _ (mul_meas_ge_le_lintegral hm (ENNReal.ofReal t))
    exact mul_le_mul le_rfl (measure_mono (fun x hx => ENNReal.ofReal_le_ofReal (hs x hx))) bot_le bot_le
  have hreal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hbound
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal ht.le,
    ENNReal.toReal_ofReal (by positivity : 0 ≤ t/4)] at hreal
  change t * P.real s ≤ t/4 at hreal
  nlinarith

theorem two_point_risk_lower : TwoPointRiskStatement := by
  intro Ω _ P Q _ _ f a b hf hab hkl
  by_contra hn
  have hsmall : max (squaredRisk P f a) (squaredRisk Q f b) <
      ENNReal.ofReal ((b-a)^2/16) := lt_of_not_ge hn
  have hP : squaredRisk P f a ≤ ENNReal.ofReal (((b-a)^2/4)/4) := by
    have := (le_max_left (squaredRisk P f a) (squaredRisk Q f b)).trans hsmall.le
    convert this using 1 <;> congr 1 <;> ring
  have hQ : squaredRisk Q f b ≤ ENNReal.ofReal (((b-a)^2/4)/4) := by
    have := (le_max_right (squaredRisk P f a) (squaredRisk Q f b)).trans hsmall.le
    convert this using 1 <;> congr 1 <;> ring
  let s : Set Ω := {x | f x < (a+b)/2}
  have hs : MeasurableSet s := measurableSet_lt hf measurable_const
  have ht : 0 < (b-a)^2/4 := by positivity
  have hPe : P.real sᶜ ≤ 1/4 := event_prob_le_of_squaredRisk_le P f hf a _ ht sᶜ (by
    intro x hx
    have hx' : (b-a)/2 ≤ f x-a := by simp only [s, Set.mem_compl_iff, Set.mem_setOf_eq, not_lt] at hx; linarith
    have hsq := (sq_le_sq₀ (by linarith : 0 ≤ (b-a)/2) (by linarith : 0 ≤ f x-a)).2 hx'
    nlinarith) hP
  have hQe : Q.real s ≤ 1/4 := event_prob_le_of_squaredRisk_le Q f hf b _ ht s (by
    intro x hx
    have hx' : (b-a)/2 ≤ b-f x := by change f x < (a+b)/2 at hx; linarith
    have hsq := (sq_le_sq₀ (by linarith : 0 ≤ (b-a)/2) (by linarith : 0 ≤ b-f x)).2 hx'
    nlinarith) hQ
  have hp : (3/4:ℝ) ≤ P.real s := by rw [probReal_compl_eq_one_sub hs] at hPe; linarith
  have hsep := (klDiv_event_separation P Q s hs hp hQe).trans hkl
  norm_num at hsep

theorem squaredRisk_neg {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) (f : Ω → ℝ) (a : ℝ) :
    squaredRisk P (fun x => -f x) (-a) = squaredRisk P f a := by
  unfold squaredRisk
  congr 1
  funext x
  congr 1
  ring

theorem two_point_risk_lower_of_ne {Ω : Type} [MeasurableSpace Ω]
    (P Q : Measure Ω) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (f : Ω → ℝ) (a b : ℝ) (hf : Measurable f) (hab : a ≠ b)
    (hkl : klDiv P Q ≤ ENNReal.ofReal (1/8:ℝ)) :
    ENNReal.ofReal ((b-a)^2/16) ≤ max (squaredRisk P f a) (squaredRisk Q f b) := by
  rcases lt_or_gt_of_ne hab with h | h
  · exact two_point_risk_lower Ω P Q f a b hf h hkl
  · have hb := two_point_risk_lower Ω P Q (fun x => -f x) (-a) (-b) hf.neg (by linarith) hkl
    rw [squaredRisk_neg, squaredRisk_neg] at hb
    convert hb using 1 <;> congr 1 <;> ring

end ThresholdHC.Tier6
