import ThresholdHC.CriticalEntropy.CriticalRisk

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace ThresholdHC.CriticalEntropy

theorem affinity_power_controls_distance (a : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1)
    (n : ℕ) (hpow : 1/2 ≤ a^n) : (n : ℝ)*(1-a) ≤ 1 := by
  have hb : ∀ k : ℕ, a^k*(1+(k : ℝ)*(1-a)) ≤ 1 := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have hs : a*(1+((k : ℝ)+1)*(1-a)) ≤ 1+(k : ℝ)*(1-a) := by
        nlinarith [mul_nonneg (by positivity : (0 : ℝ) ≤ k+1) (sq_nonneg (1-a))]
      calc
        _ = a^k*(a*(1+((k : ℝ)+1)*(1-a))) := by rw [pow_succ]; push_cast; ring
        _ ≤ a^k*(1+(k : ℝ)*(1-a)) := mul_le_mul_of_nonneg_left hs (pow_nonneg ha k)
        _ ≤ 1 := ih
  have h := mul_le_mul_of_nonneg_right hpow (by positivity : 0 ≤ 1+(n : ℝ)*(1-a))
  nlinarith [hb n]

theorem critical_repeat_choice (h : ℝ) (hh : 0 < h) (h1 : h ≤ 1) :
    ∃ n : ℕ, 2 ≤ (n : ℝ)*h ∧ (n : ℝ)*h ≤ 3 := by
  refine ⟨⌈2/h⌉₊,?_,?_⟩
  · exact (div_le_iff₀ hh).mp (Nat.le_ceil (2/h))
  · have hc := mul_lt_mul_of_pos_right (Nat.ceil_lt_add_one (by positivity : 0 ≤ 2/h)) hh
    rw [add_mul,div_mul_cancel₀ _ hh.ne',one_mul] at hc
    linarith

/-- Compact minimization handles null work without dividing by it. -/
theorem compact_power_pair_bound {E : Type} [TopologicalSpace E]
    (K : Set E) (hKn : K.Nonempty) (hKc : IsCompact K)
    (H : E → ℝ) (hHc : Continuous H) (hH : ∀ z ∈ K, H z ∈ Icc 0 1)
    (a b : ℝ) (ha : 0 < a) (hb : 0 ≤ b)
    (hpairs : ∀ n : ℕ, (n : ℝ)*b < a → ∃ z ∈ K, 1/2 ≤ (1-H z)^n) :
    ∃ z ∈ K, H z*a ≤ 3*b := by
  obtain ⟨z,hz,hmin⟩ := hKc.exists_isMinOn hKn hHc.continuousOn
  refine ⟨z,hz,?_⟩
  by_contra! hbad
  have hh : 0 < H z := by nlinarith [hH z hz |>.1]
  obtain ⟨n,hnlo,hnhi⟩ := critical_repeat_choice (H z) hh (hH z hz).2
  have hnsmall : (n : ℝ)*b < a := by
    apply (mul_lt_mul_iff_left₀ hh).mp
    calc
      _ = ((n : ℝ)*H z)*b := by ring
      _ ≤ 3*b := mul_le_mul_of_nonneg_right hnhi hb
      _ < a*H z := by nlinarith
  obtain ⟨w,hw,hpow⟩ := hpairs n hnsmall
  have hdist := affinity_power_controls_distance (1-H w) (by linarith [(hH w hw).2])
    (by linarith [(hH w hw).1]) n hpow
  have hle := mul_le_mul_of_nonneg_left (hmin hw) (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
  nlinarith

theorem populationPairSet_covers_priors {D : Type} [MeasurableSpace D]
    (μ : Measure D) [IsProbabilityMeasure μ] (ρ δ : ℝ)
    (q r : D → unitInterval) (hq : CappedPrior μ ρ q) (hr : CappedPrior μ ρ r)
    (hgap : δ ≤ (∫ d, (q d : ℝ) ∂μ)-(∫ d, (r d : ℝ) ∂μ)) :
    ∃ z ∈ populationPairSet μ ρ δ,
      (fun d => (populationDualPrior μ z.1 d : ℝ)) =ᵐ[μ] (fun d => (r d : ℝ)) ∧
      (fun d => (populationDualPrior μ z.2 d : ℝ)) =ᵐ[μ] (fun d => (q d : ℝ)) := by
  obtain ⟨f,hf,heq⟩ := populationDualSet_covers_priors μ ρ q hq.1 hq.2.1 hq.2.2
  obtain ⟨g,hg,her⟩ := populationDualSet_covers_priors μ ρ r hr.1 hr.2.1 hr.2.2
  refine ⟨(g,f),⟨⟨hg,hf⟩,?_⟩,her,heq⟩
  change δ ≤ f (Lp.const 2 μ (1 : ℝ))-g (Lp.const 2 μ (1 : ℝ))
  rw [← populationDualPrior_mass μ ρ f hf,← populationDualPrior_mass μ ρ g hg,
    integral_congr_ae heq,integral_congr_ae her]
  exact hgap

theorem capped_observation_affinity_real_congr {D R E : Type}
    [MeasurableSpace D] [MeasurableSpace R] [MeasurableSpace E]
    (μ : Measure D) [IsProbabilityMeasure μ] (ν : Measure R) [IsProbabilityMeasure ν]
    (p₀ p₁ q₁ q₂ r₁ r₂ : D → unitInterval) (h₀ : Measurable p₀) (h₁ : Measurable p₁)
    (hq₁ : Measurable q₁) (hq₂ : Measurable q₂) (hr₁ : Measurable r₁) (hr₂ : Measurable r₂)
    (A : StoppedProcedure R E) (m : ℕ) (hcap : ∀ z, A.stop z ≤ m)
    (hp : ∀ᵐ d ∂μ, 0 < (p₀ d : ℝ) ∧ (p₀ d : ℝ) < 1 ∧
      0 < (p₁ d : ℝ) ∧ (p₁ d : ℝ) < 1)
    (heq : (fun d => (q₁ d : ℝ)) =ᵐ[μ] (fun d => (q₂ d : ℝ)))
    (her : (fun d => (r₁ d : ℝ)) =ᵐ[μ] (fun d => (r₂ d : ℝ))) :
    (hellingerAffinity (cappedTranscriptLaw μ ν p₀ p₁ q₁ A m)
      (cappedTranscriptLaw μ ν p₀ p₁ r₁ A m)).toReal =
    (hellingerAffinity (cappedTranscriptLaw μ ν p₀ p₁ q₂ A m)
      (cappedTranscriptLaw μ ν p₀ p₁ r₂ A m)).toReal := by
  have hq := congrArg (fun v => fun i => v (some i))
    (cappedObservationVector_congr_ae μ ν p₀ p₁ q₁ q₂ h₀ h₁ hq₁ hq₂ A m hcap heq)
  have hr := congrArg (fun v => fun i => v (some i))
    (cappedObservationVector_congr_ae μ ν p₀ p₁ r₁ r₂ h₀ h₁ hr₁ hr₂ A m hcap her)
  change (fun i => (cappedStatisticLaw μ ν p₀ p₁ q₁ A m).real {i}) =
    (fun i => (cappedStatisticLaw μ ν p₀ p₁ q₂ A m).real {i}) at hq
  change (fun i => (cappedStatisticLaw μ ν p₀ p₁ r₁ A m).real {i}) =
    (fun i => (cappedStatisticLaw μ ν p₀ p₁ r₂ A m).real {i}) at hr
  rw [capped_observation_affinity_real μ ν p₀ p₁ q₁ r₁ h₀ h₁ hq₁ hr₁ A m hcap hp,
    capped_observation_affinity_real μ ν p₀ p₁ q₂ r₂ h₀ h₁ hq₂ hr₂ A m hcap hp,hq,hr]

theorem capped_observation_affinity_real_symm {D R E : Type}
    [MeasurableSpace D] [MeasurableSpace R] [MeasurableSpace E]
    (μ : Measure D) [IsProbabilityMeasure μ] (ν : Measure R) [IsProbabilityMeasure ν]
    (p₀ p₁ q r : D → unitInterval) (h₀ : Measurable p₀) (h₁ : Measurable p₁)
    (hq : Measurable q) (hr : Measurable r) (A : StoppedProcedure R E)
    (m : ℕ) (hcap : ∀ z, A.stop z ≤ m)
    (hp : ∀ᵐ d ∂μ, 0 < (p₀ d : ℝ) ∧ (p₀ d : ℝ) < 1 ∧
      0 < (p₁ d : ℝ) ∧ (p₁ d : ℝ) < 1) :
    (hellingerAffinity (cappedTranscriptLaw μ ν p₀ p₁ q A m)
      (cappedTranscriptLaw μ ν p₀ p₁ r A m)).toReal =
    (hellingerAffinity (cappedTranscriptLaw μ ν p₀ p₁ r A m)
      (cappedTranscriptLaw μ ν p₀ p₁ q A m)).toReal := by
  rw [capped_observation_affinity_real μ ν p₀ p₁ q r h₀ h₁ hq hr A m hcap hp,
    capped_observation_affinity_real μ ν p₀ p₁ r q h₀ h₁ hr hq A m hcap hp]
  simp only [realFiniteAffinity,mul_comm]

theorem criticalLogFactor_pos (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) :
    0 < criticalLogFactor ρ := by
  have hL : 0 ≤ Real.log (1/ρ) := Real.log_nonneg ((le_div_iff₀ hρ).mpr (by simpa using hρ1))
  have hH : 0 ≤ Real.log (1+Real.log (1/ρ)) := Real.log_nonneg (by linarith)
  unfold criticalLogFactor
  positivity

/-- One policy's distance constraint is feasible on the common separated-pair
set, including when null expected work is zero. -/
theorem critical_capped_constraint_feasible : ∃ C : ℝ, 0 < C ∧
    ∀ (R E : Type) [MeasurableSpace R] [MeasurableSpace E]
      (ν : Measure R) [IsProbabilityMeasure ν] (A : StoppedProcedure R E)
      (m : ℕ), (∀ z, A.stop z ≤ m) → ∀ (ρ : unitInterval),
      0 < (ρ : ℝ) → (ρ : ℝ) ≤ 1/4 → ∀ δ : ℝ, 0 ≤ δ → δ ≤ (ρ : ℝ)/96 →
      ∃ z ∈ populationPairSet criticalGapLaw (ρ : ℝ) δ,
        (1-(hellingerAffinity
          (cappedTranscriptLaw criticalGapLaw ν
            (fun d => criticalParameter d false) (fun d => criticalParameter d true)
            (populationDualPrior criticalGapLaw z.1) A m)
          (cappedTranscriptLaw criticalGapLaw ν
            (fun d => criticalParameter d false) (fun d => criticalParameter d true)
            (populationDualPrior criticalGapLaw z.2) A m)).toReal)*
          (ρ : ℝ)*criticalLogFactor (ρ : ℝ) ≤
        C*δ^2*(populationExpectedWork criticalGapLaw ν
          (fun d => criticalParameter d false) (fun d => criticalParameter d true) (fun _ => 0) A).toReal := by
  obtain ⟨c,hc,hpairs⟩ := critical_capped_policy_pair
  refine ⟨27/(4*c),by positivity,?_⟩
  intro R E _ _ ν _ A m hcap ρ hρ hρ' δ hδ hδρ
  obtain ⟨hKc,hKv,hKn,hreal,hgeom⟩ := critical_pair_hellinger_geometry (ρ : ℝ) δ hδ
    (by linarith) (by linarith)
  obtain ⟨H,hHc,hHv,hH⟩ := hgeom R E ν A m hcap
  let w := (populationExpectedWork criticalGapLaw ν
    (fun d => criticalParameter d false) (fun d => criticalParameter d true) (fun _ => 0) A).toReal
  have hw : 0 ≤ w := ENNReal.toReal_nonneg
  have hmod : ∀ n : ℕ, (n : ℝ)*(9*(δ/2)^2*w) < c*(ρ : ℝ)*criticalLogFactor (ρ : ℝ) →
      ∃ z ∈ populationPairSet criticalGapLaw (ρ : ℝ) δ, 1/2 ≤ (1-H z)^n := by
    intro n hn
    obtain ⟨q,r,hq,hr,hgap,hpow⟩ := hpairs R E ν A m hcap ρ hρ hρ' n (δ/2)
      (by positivity) (by linarith) (by simpa only [mul_assoc] using hn)
    obtain ⟨z,hz,her,heq⟩ := populationPairSet_covers_priors criticalGapLaw (ρ : ℝ) δ q r hq hr
      (by linarith)
    refine ⟨z,hz,?_⟩
    rw [(hH z hz).1,sub_sub_cancel]
    rw [capped_observation_affinity_real_congr criticalGapLaw ν
      (fun d => criticalParameter d false) (fun d => criticalParameter d true)
      (populationDualPrior criticalGapLaw z.1) r (populationDualPrior criticalGapLaw z.2) q
      (measurable_criticalParameter false) (measurable_criticalParameter true)
      (populationDualPrior_measurable _ _) hr.1 (populationDualPrior_measurable _ _) hq.1
      A m hcap critical_parameters_interior her heq,
      capped_observation_affinity_real_symm criticalGapLaw ν
        (fun d => criticalParameter d false) (fun d => criticalParameter d true) r q
        (measurable_criticalParameter false) (measurable_criticalParameter true) hr.1 hq.1
        A m hcap critical_parameters_interior]
    exact hpow
  obtain ⟨z,hz,hbound⟩ := compact_power_pair_bound _ hKn hKc H hHc (fun z hz => (hH z hz).2)
    (c*(ρ : ℝ)*criticalLogFactor (ρ : ℝ)) (9*(δ/2)^2*w)
    (mul_pos (mul_pos hc hρ) (criticalLogFactor_pos (ρ : ℝ) hρ (by linarith)))
    (by positivity) hmod
  refine ⟨z,hz,?_⟩
  rw [← (hH z hz).1]
  apply (mul_le_mul_iff_left₀ hc).mp
  calc
    _ = H z*(c*(ρ : ℝ)*criticalLogFactor (ρ : ℝ)) := by ring
    _ ≤ 3*(9*(δ/2)^2*w) := hbound
    _ = _ := by dsimp only [w]; field_simp; ring

end ThresholdHC.CriticalEntropy
