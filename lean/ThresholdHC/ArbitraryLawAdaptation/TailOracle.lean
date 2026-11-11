import ThresholdHC.ArbitraryLawAdaptation.TailTestLaw
import ThresholdHC.EntropyTailQuantile.QuantileTailBound
import ThresholdHC.EntropyTail.Bridge

/-! The oracle comparison of the tail certificate.

At depth `J` write `t = 2^{-J}` and `N = 4^J`. The certificate is bounded by a
multiple of `u_J + W_J/N`, the integral over the gap law of one kernel: the
unresolved probability of a coin plus its normalized work envelope. This
module compares that integral with the entropy-tail selection functional
`K_{μ,ρ}(N)` of the rare-event theory.

The gap law is split at its lowest-gap quantile of mass `ρ`, with a fraction
of a boundary atom when needed. On the quantile part the kernel is at most
`2052 min{1, t/d}`, whose integral the existing quantile-tail floor bounds by
`2052 K`. The remaining core has gaps at least the quantile threshold `a > 0`,
where the kernel is at most `(1024(J+1) + 16) t²/a²`. Under the onset
condition `TailOnset`, `2048 (J+1) 2^{-J}/a² ≤ √ρ`, this is at most `t√ρ ≤ K/2`. Hence
`u_J + W_J/N ≤ 4096 K` and the certificate bound is at most `524288 K`. The
onset condition holds at every large depth. No inverse moment or tail
regularity of the law is assumed. -/

noncomputable section
open MeasureTheory Real
open scoped ENNReal Topology
namespace ThresholdHC.ArbitraryLawAdaptation
open ThresholdHC.Tier6 ThresholdHC.EntropyTailQuantile

/-- The single-coin kernel of the certificate bound: the unresolved probability
of a coin of gap `d` plus its work envelope over `N = 4^J`. -/
def tailOracleKernel (J : ℕ) (d : Gap) : ℝ :=
  tailUnresolvedProb J d + tailWorkEnvelope J d / 4 ^ J

/-- The onset condition at depth `J`: `2048 (J+1) 2^{-J}/a² ≤ √ρ`, where `a` is
the quantile threshold of mass `ρ` of the gap law. -/
def TailOnset (μ : Measure Gap) (ρ : ℝ) (J : ℕ) : Prop :=
  2048 * ((J : ℝ) + 1) * (1 / 2) ^ J / (quantileThreshold μ ρ) ^ 2 ≤ Real.sqrt ρ

theorem half_pow_eq (J : ℕ) : (1 / 2 : ℝ) ^ J = 1 / 2 ^ J := by
  rw [one_div_pow]

theorem four_pow_eq (J : ℕ) : (4 : ℝ) ^ J = (2 ^ J) ^ 2 := by
  rw [← pow_mul, mul_comm, pow_mul]
  norm_num

/-- `1 + log₂ x ≤ 2x` for `x ≥ 1`. -/
theorem one_add_logb_two_le {x : ℝ} (hx : 1 ≤ x) : 1 + Real.logb 2 x ≤ 2 * x := by
  have hlog2 : (1 : ℝ) / 2 ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hlogx : Real.log x ≤ x - 1 := Real.log_le_sub_one_of_pos (by linarith)
  have hlogx0 : 0 ≤ Real.log x := Real.log_nonneg hx
  have hdiv : Real.log x / Real.log 2 ≤ 2 * Real.log x := by
    rw [div_le_iff₀ (by linarith)]
    nlinarith
  unfold Real.logb
  linarith

/-- The normalized work envelope is at most `2048 min{1, t/d}`. -/
theorem tailWorkEnvelope_div_le (J : ℕ) (d : Gap) :
    tailWorkEnvelope J d / 4 ^ J ≤ 2048 * min 1 ((1 / 2) ^ J / (d : ℝ)) := by
  have hd0 : (0 : ℝ) < d := d.property.1
  have hN : (0 : ℝ) < 4 ^ J := by positivity
  have hT : (0 : ℝ) < 2 ^ J := by positivity
  by_cases hdt : (d : ℝ) ≤ (1 / 2) ^ J
  · have h1 : (1 : ℝ) ≤ (1 / 2) ^ J / d := by
      rw [le_div_iff₀ hd0]
      linarith
    rw [min_eq_left h1]
    have hle : tailWorkEnvelope J d / 4 ^ J ≤ 1 := by
      rw [div_le_one hN]
      exact tailWorkEnvelope_le J d
    linarith
  · have hlt : (1 / 2 : ℝ) ^ J < d := not_le.mp hdt
    have hr : (1 / 2 : ℝ) ^ J / d ≤ 1 := by
      rw [div_le_one hd0]
      exact hlt.le
    rw [min_eq_right hr]
    have hx : 1 ≤ (d : ℝ) * 2 ^ J := by
      rw [half_pow_eq, div_lt_iff₀ hT] at hlt
      linarith
    have hL : 1 + tailLog J d ≤ 2 * ((d : ℝ) * 2 ^ J) := by
      unfold tailLog
      rw [max_eq_right (Real.logb_nonneg (by norm_num) hx)]
      exact one_add_logb_two_le hx
    have hc : (0 : ℝ) ≤ 1024 / (d : ℝ) ^ 2 := by positivity
    rw [div_le_iff₀ hN]
    calc tailWorkEnvelope J d ≤ 1024 / (d : ℝ) ^ 2 * (1 + tailLog J d) := min_le_right _ _
      _ ≤ 1024 / (d : ℝ) ^ 2 * (2 * ((d : ℝ) * 2 ^ J)) := mul_le_mul_of_nonneg_left hL hc
      _ = 2048 * ((1 / 2) ^ J / (d : ℝ)) * 4 ^ J := by
          rw [half_pow_eq, four_pow_eq]
          field_simp
          ring

/-- The unresolved probability is at most `4 min{1, t/d}`. -/
theorem tailUnresolvedProb_le_four_min (J : ℕ) (d : Gap) :
    tailUnresolvedProb J d ≤ 4 * min 1 ((1 / 2) ^ J / (d : ℝ)) := by
  have hd0 : (0 : ℝ) < d := d.property.1
  have hr0 : (0 : ℝ) < (1 / 2) ^ J / d := by positivity
  have h := tailUnresolvedProb_le_envelope J d
  generalize (1 / 2 : ℝ) ^ J / (d : ℝ) = r at h hr0 ⊢
  rcases le_total 1 r with h1 | h1
  · rw [min_eq_left h1]
    linarith [min_le_left 1 (16 * r ^ 2)]
  · rw [min_eq_right h1]
    rcases le_total (1 / 4) r with h4 | h4
    · linarith [min_le_left 1 (16 * r ^ 2)]
    · have hsq : 16 * r ^ 2 ≤ 4 * r := by nlinarith
      linarith [min_le_right 1 (16 * r ^ 2)]

/-- On every gap the kernel is at most `2052 min{1, t/d}`. -/
theorem tailOracleKernel_le_tail (J : ℕ) (d : Gap) :
    tailOracleKernel J d ≤ 2052 * min 1 ((1 / 2) ^ J / (d : ℝ)) := by
  unfold tailOracleKernel
  linarith [tailUnresolvedProb_le_four_min J d, tailWorkEnvelope_div_le J d]

theorem tailLog_le (J : ℕ) (d : Gap) : tailLog J d ≤ J := by
  have hd0 : (0 : ℝ) < d := d.property.1
  have hd1 : (d : ℝ) ≤ 1 / 2 := d.property.2
  have hT : (0 : ℝ) < 2 ^ J := by positivity
  unfold tailLog
  refine max_le (Nat.cast_nonneg J) ?_
  calc Real.logb 2 ((d : ℝ) * 2 ^ J) ≤ Real.logb 2 (2 ^ J) :=
        Real.logb_le_logb_of_le (by norm_num) (by positivity) (by nlinarith)
    _ = J := by
        rw [Real.logb_pow, Real.logb_self_eq_one (by norm_num), mul_one]

/-- On gaps at least `a` the kernel is at most `(1024(J+1) + 16) t²/a²`. -/
theorem tailOracleKernel_le_core (J : ℕ) {a : ℝ} (ha : 0 < a) (d : Gap) (had : a ≤ (d : ℝ)) :
    tailOracleKernel J d ≤ (1024 * ((J : ℝ) + 1) + 16) * ((1 / 2) ^ J) ^ 2 / a ^ 2 := by
  have hd0 : (0 : ℝ) < d := d.property.1
  have hT : (0 : ℝ) < 2 ^ J := by positivity
  have ht : (0 : ℝ) < (1 / 2) ^ J := by positivity
  have hN : (0 : ℝ) < 4 ^ J := by positivity
  have ha2 : 0 < a ^ 2 := by positivity
  have hd2 : a ^ 2 ≤ (d : ℝ) ^ 2 := pow_le_pow_left₀ ha.le had 2
  have hinv : ((1 / 2 : ℝ) ^ J) ^ 2 / (d : ℝ) ^ 2 ≤ ((1 / 2 : ℝ) ^ J) ^ 2 / a ^ 2 :=
    div_le_div_of_nonneg_left (by positivity) ha2 hd2
  have hu : tailUnresolvedProb J d ≤ 16 * (((1 / 2 : ℝ) ^ J) ^ 2 / (d : ℝ) ^ 2) := by
    have h := (tailUnresolvedProb_le_envelope J d).trans (min_le_right _ _)
    rwa [div_pow] at h
  have hw : tailWorkEnvelope J d / 4 ^ J ≤
      1024 * ((J : ℝ) + 1) * (((1 / 2 : ℝ) ^ J) ^ 2 / (d : ℝ) ^ 2) := by
    have hL : 1 + tailLog J d ≤ (J : ℝ) + 1 := by linarith [tailLog_le J d]
    have hc : (0 : ℝ) ≤ 1024 / (d : ℝ) ^ 2 := by positivity
    rw [div_le_iff₀ hN]
    calc tailWorkEnvelope J d ≤ 1024 / (d : ℝ) ^ 2 * (1 + tailLog J d) := min_le_right _ _
      _ ≤ 1024 / (d : ℝ) ^ 2 * ((J : ℝ) + 1) := mul_le_mul_of_nonneg_left hL hc
      _ = 1024 * ((J : ℝ) + 1) * (((1 / 2 : ℝ) ^ J) ^ 2 / (d : ℝ) ^ 2) * 4 ^ J := by
          rw [half_pow_eq, four_pow_eq]
          field_simp
  have hJ : (0 : ℝ) ≤ 1024 * ((J : ℝ) + 1) := by positivity
  unfold tailOracleKernel
  calc tailUnresolvedProb J d + tailWorkEnvelope J d / 4 ^ J
      ≤ 16 * (((1 / 2 : ℝ) ^ J) ^ 2 / (d : ℝ) ^ 2) +
          1024 * ((J : ℝ) + 1) * (((1 / 2 : ℝ) ^ J) ^ 2 / (d : ℝ) ^ 2) := add_le_add hu hw
    _ = (1024 * ((J : ℝ) + 1) + 16) * (((1 / 2 : ℝ) ^ J) ^ 2 / (d : ℝ) ^ 2) := by ring
    _ ≤ (1024 * ((J : ℝ) + 1) + 16) * (((1 / 2 : ℝ) ^ J) ^ 2 / a ^ 2) :=
        mul_le_mul_of_nonneg_left hinv (by linarith)
    _ = (1024 * ((J : ℝ) + 1) + 16) * ((1 / 2) ^ J) ^ 2 / a ^ 2 := by ring

theorem tailOracleKernel_nonneg (J : ℕ) (d : Gap) : 0 ≤ tailOracleKernel J d := by
  unfold tailOracleKernel
  have h1 := tailUnresolvedProb_nonneg J d
  have h2 : 0 ≤ tailWorkEnvelope J d / 4 ^ J :=
    div_nonneg (tailWorkEnvelope_nonneg J d) (by positivity)
  linarith

theorem tailOracleKernel_le_two (J : ℕ) (d : Gap) : tailOracleKernel J d ≤ 2 := by
  unfold tailOracleKernel
  have h1 := tailUnresolvedProb_le_one J d
  have hN : (0 : ℝ) < 4 ^ J := by positivity
  have h2 : tailWorkEnvelope J d / 4 ^ J ≤ 1 := by
    rw [div_le_one hN]
    exact tailWorkEnvelope_le J d
  linarith

theorem measurable_tailOracleKernel (J : ℕ) : Measurable (tailOracleKernel J) :=
  (measurable_tailUnresolvedProb J).add
    (((measurable_tailWorkEnvelope J).comp measurable_subtype_coe).div_const _)

theorem integrable_tailOracleKernel (ξ : Measure Gap) [IsFiniteMeasure ξ] (J : ℕ) :
    Integrable (tailOracleKernel J) ξ :=
  ThresholdHC.Tier5.integrable_of_abs_bound ξ _ (measurable_tailOracleKernel J) 2 fun d => by
    rw [abs_of_nonneg (tailOracleKernel_nonneg J d)]
    exact tailOracleKernel_le_two J d

/-- `u_J + W_J/N` is the integral of the kernel over the gap law. -/
theorem tail_oracle_integral (μ : Measure Gap) [IsFiniteMeasure μ] (J : ℕ) :
    tailUnresolvedMass μ J + (∫ d : Gap, tailWorkEnvelope J d ∂μ) / 4 ^ J =
      ∫ d, tailOracleKernel J d ∂μ := by
  have hw : Integrable (fun d : Gap => tailWorkEnvelope J d / 4 ^ J) μ :=
    ThresholdHC.Tier5.integrable_of_abs_bound μ _
      (((measurable_tailWorkEnvelope J).comp measurable_subtype_coe).div_const _) 1 fun d => by
        have hN : (0 : ℝ) < 4 ^ J := by positivity
        rw [abs_of_nonneg (div_nonneg (tailWorkEnvelope_nonneg J d) hN.le), div_le_one hN]
        exact tailWorkEnvelope_le J d
  unfold tailOracleKernel tailUnresolvedMass
  rw [integral_add (integrable_tailUnresolvedProb μ J) hw, integral_div]

/-- The onset condition holds at every large depth. -/
theorem tail_onset_exists {a ρ : ℝ} (ha : 0 < a) (hρ : 0 < ρ) :
    ∃ J₀ : ℕ, ∀ J : ℕ, J₀ ≤ J →
      2048 * ((J : ℝ) + 1) * (1 / 2) ^ J / a ^ 2 ≤ Real.sqrt ρ := by
  have h1 : Filter.Tendsto (fun n : ℕ => (n : ℝ) ^ 1 / (2 : ℝ) ^ n) Filter.atTop (𝓝 0) :=
    tendsto_pow_const_div_const_pow_of_one_lt 1 (by norm_num)
  have h0 : Filter.Tendsto (fun n : ℕ => (n : ℝ) ^ 0 / (2 : ℝ) ^ n) Filter.atTop (𝓝 0) :=
    tendsto_pow_const_div_const_pow_of_one_lt 0 (by norm_num)
  have hsum : Filter.Tendsto
      (fun n : ℕ => 2048 / a ^ 2 * ((n : ℝ) ^ 1 / (2 : ℝ) ^ n + (n : ℝ) ^ 0 / (2 : ℝ) ^ n))
      Filter.atTop (𝓝 0) := by
    have h := (h1.add h0).const_mul (2048 / a ^ 2)
    simpa using h
  have hev := hsum.eventually (ge_mem_nhds (Real.sqrt_pos.mpr hρ))
  obtain ⟨J₀, hJ₀⟩ := Filter.eventually_atTop.mp hev
  refine ⟨J₀, fun J hJ => ?_⟩
  have h := hJ₀ J hJ
  have hT : (0 : ℝ) < 2 ^ J := by positivity
  have heq : 2048 * ((J : ℝ) + 1) * (1 / 2) ^ J / a ^ 2 =
      2048 / a ^ 2 * ((J : ℝ) ^ 1 / (2 : ℝ) ^ J + (J : ℝ) ^ 0 / (2 : ℝ) ^ J) := by
    rw [half_pow_eq]
    field_simp
  rw [heq]
  exact h

/-- The onset condition of a gap law holds at every large depth. The onset
depends on the law only through its quantile threshold. -/
theorem tailOnset_eventually (μ : Measure Gap) [IsProbabilityMeasure μ] {ρ : ℝ} (hρ : 0 < ρ)
    (hρ1 : ρ ≤ 1) : ∃ J₀ : ℕ, ∀ J : ℕ, J₀ ≤ J → TailOnset μ ρ J :=
  tail_onset_exists (quantileThreshold_properties μ hρ hρ1).1 hρ

/-- The selection functional is at least `2t√ρ` once `2t ≤ √ρ`. -/
theorem selection_ge_scale (μ : Measure Gap) [IsProbabilityMeasure μ] {ρ : ℝ} (hρ : 0 < ρ)
    (hρ4 : ρ ≤ 1 / 4) (J : ℕ) (hsmall : 2 * (1 / 2 : ℝ) ^ J ≤ Real.sqrt ρ) :
    ENNReal.ofReal (2 * (1 / 2) ^ J * Real.sqrt ρ) ≤ EntropyTail.selection μ ρ (4 ^ J) := by
  have ht : (0 : ℝ) < (1 / 2) ^ J := by positivity
  have hsqrt : Real.sqrt ((4 : ℝ) ^ J) = 2 ^ J := by
    rw [four_pow_eq, Real.sqrt_sq (by positivity)]
  have hscale : 1 / Real.sqrt ((4 : ℝ) ^ J) = (1 / 2) ^ J := by
    rw [hsqrt, half_pow_eq]
  have hs0 : 0 ≤ Real.sqrt ρ := Real.sqrt_nonneg ρ
  have hs1 : Real.sqrt ρ ≤ 1 / 2 := by
    rw [show (1 / 2 : ℝ) = Real.sqrt (1 / 4) by
      rw [show (1 / 4 : ℝ) = (1 / 2) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt hρ4
  have hsq : Real.sqrt ρ * Real.sqrt ρ = ρ := Real.mul_self_sqrt hρ.le
  have hfloor := EntropyTail.iInf_objective_lower μ hρ.le ((4 : ℝ) ^ J)
  rw [hscale] at hfloor
  have hmin : min (2 * (1 / 2 : ℝ) ^ J * Real.sqrt ρ) (min 1 (2 * (1 / 2 : ℝ) ^ J)) =
      2 * (1 / 2) ^ J * Real.sqrt ρ := by
    apply min_eq_left
    refine le_min (by nlinarith) (by nlinarith)
  rw [hmin] at hfloor
  unfold EntropyTail.selection
  refine le_min (ENNReal.ofReal_le_ofReal (by nlinarith)) hfloor

/-- The oracle comparison. Under the onset condition at depth `J`, with `a` the
quantile threshold of mass `ρ`, `u_J + W_J/N ≤ 4096 K_{μ,ρ}(N)`. -/
theorem tail_oracle_comparison (μ : Measure Gap) [IsProbabilityMeasure μ] {ρ : ℝ} (hρ : 0 < ρ)
    (hρ4 : ρ ≤ 1 / 4) (J : ℕ) (hon : TailOnset μ ρ J) :
    ENNReal.ofReal (tailUnresolvedMass μ J + (∫ d : Gap, tailWorkEnvelope J d ∂μ) / 4 ^ J) ≤
      4096 * EntropyTail.selection μ ρ (4 ^ J) := by
  unfold TailOnset at hon
  have hρ1 : ρ ≤ 1 := by linarith
  obtain ⟨ha, ha2, -, -⟩ := quantileThreshold_properties μ hρ hρ1
  have hνle := quantileTail_le μ hρ hρ1
  have hν : IsFiniteMeasure (quantileTail μ ρ) := isFiniteMeasure_of_le μ hνle
  have hσle : quantileCore μ ρ ≤ μ := Measure.sub_le
  have hσ : IsFiniteMeasure (quantileCore μ ρ) := isFiniteMeasure_of_le μ hσle
  have hsplit := quantileTail_add_core μ hρ hρ1
  have ht : (0 : ℝ) < (1 / 2) ^ J := by positivity
  have hJ0 : (0 : ℝ) ≤ J := Nat.cast_nonneg J
  have hs0 : 0 ≤ Real.sqrt ρ := Real.sqrt_nonneg ρ
  -- The integral over the law splits at the quantile.
  have hint : ∫ d, tailOracleKernel J d ∂μ =
      ∫ d, tailOracleKernel J d ∂quantileTail μ ρ +
        ∫ d, tailOracleKernel J d ∂quantileCore μ ρ := by
    conv_lhs => rw [← hsplit]
    exact integral_add_measure (integrable_tailOracleKernel _ J)
      (integrable_tailOracleKernel _ J)
  -- The quantile part against the tail modulus.
  have htail : ∫ d, tailOracleKernel J d ∂quantileTail μ ρ ≤
      2052 * tailModulus (quantileTail μ ρ) ((1 / 2) ^ J) := by
    have hi : Integrable (fun d : Gap => 2052 * min 1 ((1 / 2 : ℝ) ^ J / (d : ℝ)))
        (quantileTail μ ρ) :=
      ThresholdHC.Tier5.integrable_of_abs_bound _ _
        ((measurable_const.min (measurable_const.div measurable_subtype_coe)).const_mul 2052)
        2052 fun d => by
          have hd0 : (0 : ℝ) < d := d.property.1
          have h0 : (0 : ℝ) ≤ min 1 ((1 / 2 : ℝ) ^ J / (d : ℝ)) :=
            le_min zero_le_one (by positivity)
          rw [abs_of_nonneg (by positivity)]
          linarith [min_le_left 1 ((1 / 2 : ℝ) ^ J / (d : ℝ))]
    unfold tailModulus
    rw [← integral_const_mul]
    exact integral_mono (integrable_tailOracleKernel _ J) hi
      fun d => tailOracleKernel_le_tail J d
  -- The core part, where every gap is at least the quantile threshold.
  have hmass : (quantileCore μ ρ).real Set.univ ≤ 1 := by
    have h : quantileCore μ ρ Set.univ ≤ 1 :=
      (Measure.le_iff'.1 hσle Set.univ).trans_eq measure_univ
    have h' := ENNReal.toReal_mono ENNReal.one_ne_top h
    simpa [measureReal_def] using h'
  have hc0 : 0 ≤ (1024 * ((J : ℝ) + 1) + 16) * ((1 / 2) ^ J) ^ 2 / (quantileThreshold μ ρ) ^ 2 := by
    positivity
  have hcore : ∫ d, tailOracleKernel J d ∂quantileCore μ ρ ≤
      (1024 * ((J : ℝ) + 1) + 16) * ((1 / 2) ^ J) ^ 2 / (quantileThreshold μ ρ) ^ 2 := by
    calc ∫ d, tailOracleKernel J d ∂quantileCore μ ρ
        ≤ ∫ _d : Gap, (1024 * ((J : ℝ) + 1) + 16) * ((1 / 2) ^ J) ^ 2 /
            (quantileThreshold μ ρ) ^ 2 ∂quantileCore μ ρ := by
          apply integral_mono_ae (integrable_tailOracleKernel _ J) (integrable_const _)
          filter_upwards [quantileCore_support μ ρ] with d hd
          exact tailOracleKernel_le_core J ha d hd
      _ = (quantileCore μ ρ).real Set.univ * ((1024 * ((J : ℝ) + 1) + 16) * ((1 / 2) ^ J) ^ 2 /
            (quantileThreshold μ ρ) ^ 2) := by
          rw [integral_const, smul_eq_mul]
      _ ≤ 1 * ((1024 * ((J : ℝ) + 1) + 16) * ((1 / 2) ^ J) ^ 2 /
            (quantileThreshold μ ρ) ^ 2) := mul_le_mul_of_nonneg_right hmass hc0
      _ = (1024 * ((J : ℝ) + 1) + 16) * ((1 / 2) ^ J) ^ 2 / (quantileThreshold μ ρ) ^ 2 :=
          one_mul _
  -- The onset condition turns the core bound into `t√ρ` and gives `2t ≤ √ρ`.
  have hcore2 : (1024 * ((J : ℝ) + 1) + 16) * ((1 / 2) ^ J) ^ 2 / (quantileThreshold μ ρ) ^ 2 ≤
      (1 / 2) ^ J * Real.sqrt ρ := by
    have h16 : 1024 * ((J : ℝ) + 1) + 16 ≤ 2048 * ((J : ℝ) + 1) := by linarith
    calc (1024 * ((J : ℝ) + 1) + 16) * ((1 / 2) ^ J) ^ 2 / (quantileThreshold μ ρ) ^ 2
        ≤ 2048 * ((J : ℝ) + 1) * ((1 / 2) ^ J) ^ 2 / (quantileThreshold μ ρ) ^ 2 :=
          div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right h16 (by positivity))
            (by positivity)
      _ = (1 / 2) ^ J * (2048 * ((J : ℝ) + 1) * (1 / 2) ^ J / (quantileThreshold μ ρ) ^ 2) := by
          ring
      _ ≤ (1 / 2) ^ J * Real.sqrt ρ := mul_le_mul_of_nonneg_left hon ht.le
  have hsmall : 2 * (1 / 2 : ℝ) ^ J ≤ Real.sqrt ρ := by
    have ha4 : (quantileThreshold μ ρ) ^ 2 ≤ 1 / 4 := by nlinarith
    have h1 : 2 * (1 / 2 : ℝ) ^ J ≤
        2048 * ((J : ℝ) + 1) * (1 / 2) ^ J / (quantileThreshold μ ρ) ^ 2 := by
      rw [le_div_iff₀ (by positivity)]
      nlinarith [mul_nonneg hJ0 ht.le, mul_nonneg ht.le (sub_nonneg.mpr ha4)]
    linarith
  have hK := selection_ge_scale μ hρ hρ4 J hsmall
  -- The quantile-tail floor of the selection functional.
  have hfloor : ENNReal.ofReal (tailModulus (quantileTail μ ρ) ((1 / 2) ^ J)) ≤
      EntropyTail.selection μ ρ (4 ^ J) := by
    have h := quantileTail_le_selectionValue μ hρ hρ1 ((4 : ℝ) ^ J)
    rw [EntropyTail.quantile_selectionValue_eq] at h
    have hbs : EntropyTailQuantile.budgetScale ((4 : ℝ) ^ J) = (1 / 2) ^ J := by
      unfold EntropyTailQuantile.budgetScale
      rw [four_pow_eq, Real.sqrt_sq (by positivity), half_pow_eq, one_div]
    rwa [hbs] at h
  have hτ0 : 0 ≤ tailModulus (quantileTail μ ρ) ((1 / 2) ^ J) := tailModulus_nonneg _ ht.le
  have hreal : ∫ d, tailOracleKernel J d ∂quantileTail μ ρ +
      ∫ d, tailOracleKernel J d ∂quantileCore μ ρ ≤
        2052 * tailModulus (quantileTail μ ρ) ((1 / 2) ^ J) +
          1 / 2 * (2 * (1 / 2) ^ J * Real.sqrt ρ) := by
    linarith
  rw [tail_oracle_integral, hint]
  calc ENNReal.ofReal (∫ d, tailOracleKernel J d ∂quantileTail μ ρ +
        ∫ d, tailOracleKernel J d ∂quantileCore μ ρ)
      ≤ ENNReal.ofReal (2052 * tailModulus (quantileTail μ ρ) ((1 / 2) ^ J) +
          1 / 2 * (2 * (1 / 2) ^ J * Real.sqrt ρ)) := ENNReal.ofReal_le_ofReal hreal
    _ = ENNReal.ofReal 2052 * ENNReal.ofReal (tailModulus (quantileTail μ ρ) ((1 / 2) ^ J)) +
          ENNReal.ofReal (1 / 2) * ENNReal.ofReal (2 * (1 / 2) ^ J * Real.sqrt ρ) := by
        rw [ENNReal.ofReal_add (mul_nonneg (by norm_num) hτ0) (by positivity),
          ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_mul (by norm_num)]
    _ ≤ ENNReal.ofReal 2052 * EntropyTail.selection μ ρ (4 ^ J) +
          ENNReal.ofReal (1 / 2) * EntropyTail.selection μ ρ (4 ^ J) := by gcongr
    _ = ENNReal.ofReal (2052 + 1 / 2) * EntropyTail.selection μ ρ (4 ^ J) := by
        rw [← add_mul, ← ENNReal.ofReal_add (by norm_num) (by norm_num)]
    _ ≤ ENNReal.ofReal 4096 * EntropyTail.selection μ ρ (4 ^ J) := by
        gcongr
        norm_num
    _ = 4096 * EntropyTail.selection μ ρ (4 ^ J) := by rw [ENNReal.ofReal_ofNat]

/-- Under the onset condition the bound of statement (1) is at most
`524288 K_{μ,ρ}(N)`. -/
theorem tail_bound_le_oracle (μ : Measure Gap) [IsProbabilityMeasure μ] {ρ : ℝ} (hρ : 0 < ρ)
    (hρ4 : ρ ≤ 1 / 4) (J : ℕ) (hon : TailOnset μ ρ J) :
    ENNReal.ofReal (min 1 (128 * max (tailUnresolvedMass μ J)
        ((∫ d : Gap, tailWorkEnvelope J d ∂μ) / 4 ^ J))) ≤
      524288 * EntropyTail.selection μ ρ (4 ^ J) := by
  have hu0 : 0 ≤ tailUnresolvedMass μ J :=
    integral_nonneg fun d => tailUnresolvedProb_nonneg J d
  have hw0 : 0 ≤ (∫ d : Gap, tailWorkEnvelope J d ∂μ) / 4 ^ J :=
    div_nonneg (integral_nonneg fun d => tailWorkEnvelope_nonneg J d) (by positivity)
  have hmax : max (tailUnresolvedMass μ J) ((∫ d : Gap, tailWorkEnvelope J d ∂μ) / 4 ^ J) ≤
      tailUnresolvedMass μ J + (∫ d : Gap, tailWorkEnvelope J d ∂μ) / 4 ^ J :=
    max_le (by linarith) (by linarith)
  have hcmp := tail_oracle_comparison μ hρ hρ4 J hon
  calc ENNReal.ofReal (min 1 (128 * max (tailUnresolvedMass μ J)
        ((∫ d : Gap, tailWorkEnvelope J d ∂μ) / 4 ^ J)))
      ≤ ENNReal.ofReal (128 * (tailUnresolvedMass μ J +
          (∫ d : Gap, tailWorkEnvelope J d ∂μ) / 4 ^ J)) :=
        ENNReal.ofReal_le_ofReal ((min_le_right _ _).trans (by linarith))
    _ = ENNReal.ofReal 128 * ENNReal.ofReal (tailUnresolvedMass μ J +
          (∫ d : Gap, tailWorkEnvelope J d ∂μ) / 4 ^ J) := ENNReal.ofReal_mul (by norm_num)
    _ ≤ ENNReal.ofReal 128 * (4096 * EntropyTail.selection μ ρ (4 ^ J)) := by gcongr
    _ = 524288 * EntropyTail.selection μ ρ (4 ^ J) := by
        rw [ENNReal.ofReal_ofNat, ← mul_assoc]
        norm_num

end ThresholdHC.ArbitraryLawAdaptation
