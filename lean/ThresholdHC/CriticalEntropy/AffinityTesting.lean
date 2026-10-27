import ThresholdHC.CriticalEntropy.EventualAffinity
import ThresholdHC.Tier6.AlgorithmCore

noncomputable section

namespace ThresholdHC.CriticalEntropy
open MeasureTheory Set
open scoped ENNReal
set_option maxHeartbeats 1000000

def thresholdDecision {Ω : Type} (f : Ω → ℝ) (c : ℝ) (x : Ω) : Bool :=
  if f x < c then false else true

theorem measurable_thresholdDecision {Ω : Type} [MeasurableSpace Ω]
    (f : Ω → ℝ) (hf : Measurable f) (c : ℝ) : Measurable (thresholdDecision f c) :=
  measurable_const.ite (measurableSet_lt hf measurable_const) measurable_const

theorem risk_event_markov {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (f : Ω → ℝ) (hf : Measurable f)
    (a t ε : ℝ) (ht : 0 < t) (hε : 0 ≤ ε) (s : Set Ω)
    (hs : ∀ x ∈ s, t ≤ (f x-a)^2)
    (hr : Tier6.squaredRisk P f a ≤ ENNReal.ofReal (t*ε)) : P.real s ≤ ε := by
  have hm : Measurable (fun x => ENNReal.ofReal ((f x-a)^2)) := by fun_prop
  have hbound : ENNReal.ofReal t * P s ≤ ENNReal.ofReal (t*ε) := by
    apply le_trans _ hr
    change ENNReal.ofReal t * P s ≤ ∫⁻ x, ENNReal.ofReal ((f x-a)^2) ∂P
    apply le_trans _ (mul_meas_ge_le_lintegral hm (ENNReal.ofReal t))
    exact mul_le_mul le_rfl (measure_mono (fun x hx => ENNReal.ofReal_le_ofReal (hs x hx))) bot_le bot_le
  have hreal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hbound
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal ht.le,
    ENNReal.toReal_ofReal (mul_nonneg ht.le hε)] at hreal
  change t * P.real s ≤ t * ε at hreal
  nlinarith

theorem bool_affinity_le_half_of_errors
    (P Q : Measure Bool) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (hp : P.real {true} ≤ 1/16) (hq : Q.real {false} ≤ 1/16) :
    (hellingerAffinity P Q).toReal ≤ 1/2 := by
  have hp0 : 0 ≤ P.real {false} := ENNReal.toReal_nonneg
  have hp1 : 0 ≤ P.real {true} := ENNReal.toReal_nonneg
  have hq0 : 0 ≤ Q.real {false} := ENNReal.toReal_nonneg
  have hq1 : 0 ≤ Q.real {true} := ENNReal.toReal_nonneg
  have hpmax : P.real {false} ≤ 1 := measureReal_le_one
  have hqmax : Q.real {true} ≤ 1 := measureReal_le_one
  have hprod0 : P.real {false} * Q.real {false} ≤ (1/4:ℝ)^2 := by nlinarith
  have hprod1 : P.real {true} * Q.real {true} ≤ (1/4:ℝ)^2 := by nlinarith
  have hs0 : Real.sqrt (P.real {false} * Q.real {false}) ≤ 1/4 :=
    Real.sqrt_le_iff.mpr ⟨by norm_num,hprod0⟩
  have hs1 : Real.sqrt (P.real {true} * Q.real {true}) ≤ 1/4 :=
    Real.sqrt_le_iff.mpr ⟨by norm_num,hprod1⟩
  rw [hellingerAffinity_finite_real, realFiniteAffinity]
  simp only [Fintype.sum_bool]
  linarith

/-- A binary decision with substantial affinity forces nonzero squared risk.
This uses Hellinger directly and makes no inference of an upper KL bound. -/
theorem two_point_risk_lower_of_decision_affinity {Ω : Type} [MeasurableSpace Ω]
    (P Q : Measure Ω) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (f : Ω → ℝ) (a b : ℝ) (hf : Measurable f) (hab : a < b)
    (haff : (3/4:ℝ) ≤ (hellingerAffinity
      (P.map (thresholdDecision f ((a+b)/2)))
      (Q.map (thresholdDecision f ((a+b)/2)))).toReal) :
    ENNReal.ofReal ((b-a)^2/64) ≤ max (Tier6.squaredRisk P f a) (Tier6.squaredRisk Q f b) := by
  by_contra hn
  have hsmall := lt_of_not_ge hn
  have hP : Tier6.squaredRisk P f a ≤ ENNReal.ofReal (((b-a)^2/4)*(1/16)) := by
    have := (le_max_left (Tier6.squaredRisk P f a) (Tier6.squaredRisk Q f b)).trans hsmall.le
    convert this using 1 <;> congr 1 <;> ring
  have hQ : Tier6.squaredRisk Q f b ≤ ENNReal.ofReal (((b-a)^2/4)*(1/16)) := by
    have := (le_max_right (Tier6.squaredRisk P f a) (Tier6.squaredRisk Q f b)).trans hsmall.le
    convert this using 1 <;> congr 1 <;> ring
  let s : Set Ω := {x | f x < (a+b)/2}
  have ht : 0 < (b-a)^2/4 := by positivity
  have hPe : P.real sᶜ ≤ 1/16 := risk_event_markov P f hf a _ _ ht (by norm_num) sᶜ (by
    intro x hx
    have hx' : (b-a)/2 ≤ f x-a := by simp only [s,Set.mem_compl_iff,Set.mem_setOf_eq,not_lt] at hx; linarith
    have hsq := (sq_le_sq₀ (by linarith : 0 ≤ (b-a)/2) (by linarith : 0 ≤ f x-a)).2 hx'
    nlinarith) hP
  have hQe : Q.real s ≤ 1/16 := risk_event_markov Q f hf b _ _ ht (by norm_num) s (by
    intro x hx
    have hx' : (b-a)/2 ≤ b-f x := by change f x < (a+b)/2 at hx; linarith
    have hsq := (sq_le_sq₀ (by linarith : 0 ≤ (b-a)/2) (by linarith : 0 ≤ b-f x)).2 hx'
    nlinarith) hQ
  let d := thresholdDecision f ((a+b)/2)
  have hd : Measurable d := measurable_thresholdDecision f hf _
  let : IsProbabilityMeasure (P.map d) := inferInstance
  let : IsProbabilityMeasure (Q.map d) := inferInstance
  have hpt : (P.map d).real {true} ≤ 1/16 := by
    change (P.map d {true}).toReal ≤ _
    rw [Measure.map_apply hd (measurableSet_singleton true)]
    have heq : d ⁻¹' {true} = sᶜ := by ext x; simp [d,thresholdDecision,s]
    rw [heq]
    exact hPe
  have hqf : (Q.map d).real {false} ≤ 1/16 := by
    change (Q.map d {false}).toReal ≤ _
    rw [Measure.map_apply hd (measurableSet_singleton false)]
    have heq : d ⁻¹' {false} = s := by ext x; simp [d,thresholdDecision,s]
    rw [heq]
    exact hQe
  have hhalf := bool_affinity_le_half_of_errors (P.map d) (Q.map d) hpt hqf
  linarith

end ThresholdHC.CriticalEntropy
