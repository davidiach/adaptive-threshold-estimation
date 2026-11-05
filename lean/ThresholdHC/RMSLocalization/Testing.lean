import ThresholdHC.RMSLocalization.BinaryAffinity

noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace ThresholdHC.RMSLocalization
open ThresholdHC.CriticalEntropy

theorem squared_risk_lower_of_affinity {Ω : Type} [MeasurableSpace Ω]
    (P Q : Measure Ω) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (f : Ω → ℝ) (a b : ℝ) (hf : Measurable f) (hab : a < b)
    (haff : (9/10:ℝ) ≤ (hellingerAffinity
      (P.map (thresholdDecision f ((a+b)/2)))
      (Q.map (thresholdDecision f ((a+b)/2)))).toReal) :
    ENNReal.ofReal ((b-a)^2/16) ≤ max (Tier6.squaredRisk P f a) (Tier6.squaredRisk Q f b) := by
  by_contra hn
  have hsmall := lt_of_not_ge hn
  have hP : Tier6.squaredRisk P f a ≤ ENNReal.ofReal (((b-a)^2/4)*(1/4)) := by
    have := (le_max_left (Tier6.squaredRisk P f a) (Tier6.squaredRisk Q f b)).trans hsmall.le
    convert this using 1
    congr 1
    ring
  have hQ : Tier6.squaredRisk Q f b ≤ ENNReal.ofReal (((b-a)^2/4)*(1/4)) := by
    have := (le_max_right (Tier6.squaredRisk P f a) (Tier6.squaredRisk Q f b)).trans hsmall.le
    convert this using 1
    congr 1
    ring
  let s : Set Ω := {x | f x < (a+b)/2}
  have ht : 0 < (b-a)^2/4 := by positivity
  have hPe : P.real sᶜ ≤ 1/4 := risk_event_markov P f hf a _ _ ht (by norm_num) sᶜ (by
    intro x hx
    have hx' : (b-a)/2 ≤ f x-a := by simp only [s,Set.mem_compl_iff,Set.mem_ofPred_eq,not_lt] at hx; linarith
    have hsq := (sq_le_sq₀ (by linarith : 0 ≤ (b-a)/2) (by linarith : 0 ≤ f x-a)).2 hx'
    nlinarith) hP
  have hQe : Q.real s ≤ 1/4 := risk_event_markov Q f hf b _ _ ht (by norm_num) s (by
    intro x hx
    have hx' : (b-a)/2 ≤ b-f x := by change f x < (a+b)/2 at hx; linarith
    have hsq := (sq_le_sq₀ (by linarith : 0 ≤ (b-a)/2) (by linarith : 0 ≤ b-f x)).2 hx'
    nlinarith) hQ
  let d := thresholdDecision f ((a+b)/2)
  have hd : Measurable d := measurable_thresholdDecision f hf _
  let : IsProbabilityMeasure (P.map d) := inferInstance
  let : IsProbabilityMeasure (Q.map d) := inferInstance
  have hpt : (P.map d).real {true} ≤ 1/4 := by
    change (P.map d {true}).toReal ≤ _
    rw [Measure.map_apply hd (measurableSet_singleton true)]
    have heq : d ⁻¹' {true} = sᶜ := by ext x; simp [d,thresholdDecision,s]
    rw [heq]
    exact hPe
  have hqf : (Q.map d).real {false} ≤ 1/4 := by
    change (Q.map d {false}).toReal ≤ _
    rw [Measure.map_apply hd (measurableSet_singleton false)]
    have heq : d ⁻¹' {false} = s := by ext x; simp [d,thresholdDecision,s]
    rw [heq]
    exact hQe
  have hhalf := bool_affinity_quarter_errors (P.map d) (Q.map d) hpt hqf
  linarith

theorem rms_pair_lower {Ω : Type} [MeasurableSpace Ω]
    (P Q : Measure Ω) (f : Ω → ℝ) (a b δ : ℝ) (hδ : 0 ≤ δ) (hsep : δ ≤ b-a)
    (hsq : ENNReal.ofReal ((b-a)^2/16) ≤
      max (Tier6.squaredRisk P f a) (Tier6.squaredRisk Q f b)) :
    ENNReal.ofReal (δ/4) ≤ max (Tier6.rootMeanRisk P f a) (Tier6.rootMeanRisk Q f b) := by
  have hsqδ : ENNReal.ofReal ((δ/4)^2) ≤
      max (Tier6.squaredRisk P f a) (Tier6.squaredRisk Q f b) := by
    apply le_trans _ hsq
    apply ENNReal.ofReal_le_ofReal
    have := (sq_le_sq₀ hδ (hδ.trans hsep)).2 hsep
    nlinarith
  have hh := ENNReal.rpow_le_rpow hsqδ (by norm_num : (0 : ℝ) ≤ 1/2)
  rw [ENNReal.max_rpow (by norm_num : (0 : ℝ) ≤ 1/2),
    ENNReal.ofReal_pow (by positivity : 0 ≤ δ/4)] at hh
  have heq : ((ENNReal.ofReal (δ/4))^2) ^ (1/2 : ℝ) = ENNReal.ofReal (δ/4) := by
    simpa only [Nat.cast_ofNat,one_div] using
      ENNReal.pow_rpow_inv_natCast (n := 2) (by norm_num) (ENNReal.ofReal (δ/4))
  rw [heq] at hh
  exact hh

end ThresholdHC.RMSLocalization
