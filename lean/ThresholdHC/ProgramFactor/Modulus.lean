import ThresholdHC.ProgramFactor.Population
import ThresholdHC.StoppingProgram.StrongDuality
import ThresholdHC.StoppingProgram.TruncationRisk
import ThresholdHC.StoppingProgram.TruncationLimit
import ThresholdHC.Genie.Model

/-! The quartet modulus with the constant 2/(3√7), the finite-cap program
bound with the factor 3√7/2, and its passage to the infinite cap through
prefix truncation. The weight a is chosen from x = B K as in the source:
a = 1/(1+√(3x/2)) for x > 0, and a = 1/2 for x = 0 in place of the limit
a → 1. The attained strong-duality quartet is used at each finite cap. -/

noncomputable section
namespace ThresholdHC.ProgramFactor
open MeasureTheory Filter
open scoped ENNReal Topology
open ThresholdHC.CriticalEntropy ThresholdHC.ObservableSimulation ThresholdHC.StoppingProgram
open ThresholdHC.Tier3 ThresholdHC.Tier6 ThresholdHC.RareAboveTwo

theorem two_le_sqrt_seven : 2 ≤ Real.sqrt 7 := by
  rw [show (2:ℝ) = Real.sqrt (2^2) by rw [Real.sqrt_sq (by norm_num)]]
  exact Real.sqrt_le_sqrt (by norm_num)

/-- The scalar step: some weight in (0,1) turns the population affinity bound
into the testing constant 2/(3√7). -/
theorem weight_choice (x : ℝ) (hx : 0 ≤ x) :
    ∃ a : ℝ, 0 < a ∧ a < 1 ∧
      2/(3*Real.sqrt 7)*(1/Real.sqrt (4+x)) ≤ a/2*(1-a^2/(2*(1-a)^2)*x) := by
  have h7 := two_le_sqrt_seven
  have hr7 := Real.sq_sqrt (show (0:ℝ) ≤ 7 by norm_num)
  have ht := Real.sq_sqrt (show (0:ℝ) ≤ 4+x by linarith)
  have ht0 : 0 < Real.sqrt (4+x) := Real.sqrt_pos.mpr (by linarith)
  rcases hx.eq_or_lt with hx0 | hxpos
  · subst x
    refine ⟨1/2,by norm_num,by norm_num,?_⟩
    have h4 : Real.sqrt (4+0) = 2 := by
      rw [show (4:ℝ)+0 = 2^2 by norm_num,Real.sqrt_sq (by norm_num)]
    rw [h4]
    have hpos : 0 < 3*Real.sqrt 7 := by positivity
    rw [show (1/2:ℝ)/2*(1-(1/2)^2/(2*(1-1/2)^2)*0) = 1/4 by norm_num]
    rw [div_mul_div_comm,mul_one]
    apply (div_le_iff₀ (by positivity)).mpr
    nlinarith
  · let s := Real.sqrt (3*x/2)
    have hs0 : 0 < s := Real.sqrt_pos.mpr (by positivity)
    have hs2 : s^2 = 3*x/2 := Real.sq_sqrt (by positivity)
    refine ⟨1/(1+s),by positivity,?_,?_⟩
    · apply (div_lt_one (by positivity)).mpr
      linarith
    · have hb : 1-1/(1+s) = s/(1+s) := by field_simp; ring
      have hthird : (1/(1+s))^2/(2*(1-1/(1+s))^2)*x = 1/3 := by
        rw [hb]
        field_simp
        nlinarith [hs2]
      rw [hthird]
      have hrt : 2*(1+s) ≤ Real.sqrt 7*Real.sqrt (4+x) := by
        have hsq : (2*(1+s))^2 ≤ (Real.sqrt 7*Real.sqrt (4+x))^2 := by
          have he : (Real.sqrt 7*Real.sqrt (4+x))^2 = 7*(4+x) := by rw [mul_pow,hr7,ht]
          rw [he]
          nlinarith [sq_nonneg (s-6),hs2]
        exact (pow_le_pow_iff_left₀ (by positivity) (by positivity) (by norm_num)).mp hsq
      rw [div_mul_div_comm,mul_one]
      apply (div_le_iff₀ (by positivity)).mpr
      field_simp
      nlinarith [hrt]

/-- The square root of a finite-price dual ratio, as in midpoint_dual_root. -/
theorem dual_root (μ : Measure Gap) [IsProbabilityMeasure μ]
    (B : ℝ) (hB : 0 ≤ B) (N : ℕ) (Q : FourPriors) (hK : informationRatio μ N Q ≠ ⊤)
    (hgap : signMean μ Q.low.val ≤ signMean μ Q.high.val) :
    dualRatio μ B N Q ^ (1/(2:ℝ)) =
      ENNReal.ofReal ((signMean μ Q.high.val-signMean μ Q.low.val)/
        Real.sqrt (4+B*(informationRatio μ N Q).toReal)) := by
  let K := informationRatio μ N Q
  let Δ := signMean μ Q.high.val-signMean μ Q.low.val
  have hΔ : 0 ≤ Δ := sub_nonneg.mpr hgap
  have hx : 0 ≤ 4+B*K.toReal := by positivity
  have he : 4+ENNReal.ofReal B*K = ENNReal.ofReal (4+B*K.toReal) := by
    rw [ENNReal.ofReal_add (by norm_num) (by positivity),ENNReal.ofReal_mul hB,
      ENNReal.ofReal_toReal hK]
    norm_num
    rfl
  change (ENNReal.ofReal Δ^2/(4+ENNReal.ofReal B*K))^(1/(2:ℝ)) = _
  rw [he,← ENNReal.ofReal_pow hΔ,← ENNReal.ofReal_div_of_pos (by positivity : 0 < 4+B*K.toReal)]
  have hs : Δ^2/(4+B*K.toReal) = (Δ/Real.sqrt (4+B*K.toReal))^2 := by
    rw [div_pow,Real.sq_sqrt hx]
  rw [hs,ofReal_square_rpow_half _ (by positivity)]

/-- Every admissible quartet with finite ordinary price is a lower bound,
with the constant 2/(3√7), for any uniform prefix-risk bound T. -/
theorem quartet_modulus {R : Type} [MeasurableSpace R]
    (μ : Measure Gap) [IsProbabilityMeasure μ] (A : AdaptiveEstimator R)
    (ρ B : ℝ) (hB : 0 ≤ B) (hbudget : RareBudget μ A ρ B)
    (N : ℕ) (hN : 0 < N) (f : R × (Fin N → Option Bool) → ℝ) (hf : Measurable f)
    (T : ℝ≥0∞) (hT : ∀ u : SignLaw, RarePrior μ ρ u →
      rootMeanRisk (observablePrefixLaw μ A u N) f (signMean μ u.val) ≤ T)
    (Q : FourPriors) (hQ : Admissible μ ρ Q) (hK : informationRatio μ N Q ≠ ⊤) :
    ENNReal.ofReal (2/(3*Real.sqrt 7))*dualRatio μ B N Q^(1/(2:ℝ)) ≤ T := by
  by_cases hgap : signMean μ Q.low.val ≤ signMean μ Q.high.val
  swap
  · have he : ENNReal.ofReal (signMean μ Q.high.val-signMean μ Q.low.val) = 0 :=
      ENNReal.ofReal_eq_zero.mpr (by linarith)
    simp only [dualRatio,he,zero_pow (by norm_num : (2:ℕ) ≠ 0),
      ENNReal.zero_div,ENNReal.zero_rpow_of_pos (by norm_num : (0:ℝ) < 1/2),mul_zero]
    exact bot_le
  let K := (informationRatio μ N Q).toReal
  have hK0 : 0 ≤ K := ENNReal.toReal_nonneg
  obtain ⟨a,ha0,ha1,hineq⟩ := weight_choice (B*K) (mul_nonneg hB hK0)
  have ha : 0 ≤ a ∧ a ≤ 1 := ⟨ha0.le,ha1.le⟩
  have hrare := weighted_rare μ Q hQ a ha
  have hmid := mixPrior_rare μ _ _ hrare.1 hrare.2 (1/2) (by norm_num)
  have hw : expectedWork μ A (midpointPrior (weightedLow Q a ha) (weightedHigh Q a ha)) ≤
      ENNReal.ofReal B := hbudget _ hmid
  have hl := (weighted_prefix_risk μ A Q a ha ha1 N hN hK B hB hw hgap f hf).trans
    (max_le (hT _ hrare.1) (hT _ hrare.2))
  rw [dual_root μ B hB N Q hK hgap,← ENNReal.ofReal_mul (by positivity)]
  apply le_trans (ENNReal.ofReal_le_ofReal ?_) hl
  have hΔ : 0 ≤ signMean μ Q.high.val-signMean μ Q.low.val := sub_nonneg.mpr hgap
  have hh := mul_le_mul_of_nonneg_left hineq hΔ
  change 2/(3*Real.sqrt 7)*((signMean μ Q.high.val-signMean μ Q.low.val)/Real.sqrt (4+B*K)) ≤
    a*(signMean μ Q.high.val-signMean μ Q.low.val)/2*(1-a^2/(2*(1-a)^2)*K*B)
  calc
    _ = (signMean μ Q.high.val-signMean μ Q.low.val)*
        (2/(3*Real.sqrt 7)*(1/Real.sqrt (4+B*K))) := by ring
    _ ≤ (signMean μ Q.high.val-signMean μ Q.low.val)*(a/2*(1-a^2/(2*(1-a)^2)*(B*K))) := hh
    _ = _ := by ring

/-- The finite-cap program is at most 3√7/2 times any uniform prefix-risk
bound of a budget-feasible estimator. -/
theorem prefix_program_factor {R : Type} [MeasurableSpace R]
    (μ : Measure Gap) [IsProbabilityMeasure μ] (A : AdaptiveEstimator R)
    (ρ B : ℝ) (hρ : 0 < ρ) (hρhalf : ρ ≤ 1/2) (hB : 0 < B) (hbudget : RareBudget μ A ρ B)
    (N : ℕ) (hN : 0 < N) (f : R × (Fin N → Option Bool) → ℝ) (hf : Measurable f)
    (T : ℝ≥0∞) (hT : ∀ u : SignLaw, RarePrior μ ρ u →
      rootMeanRisk (observablePrefixLaw μ A u N) f (signMean μ u.val) ≤ T) :
    programValue μ ρ B N ≤ ENNReal.ofReal (3*Real.sqrt 7/2)*T := by
  obtain ⟨_,Q,hQ,hdual,_,hK⟩ := strong_four_prior_duality N μ hρ hρhalf hB
  have hm := quartet_modulus μ A ρ B hB.le hbudget N hN f hf T hT Q hQ hK.ne
  have h7 : 0 < Real.sqrt 7 := Real.sqrt_pos.mpr (by norm_num)
  have hc : ENNReal.ofReal (3*Real.sqrt 7/2)*ENNReal.ofReal (2/(3*Real.sqrt 7)) = 1 := by
    rw [← ENNReal.ofReal_mul (by positivity)]
    have he : 3*Real.sqrt 7/2*(2/(3*Real.sqrt 7)) = 1 := by field_simp
    rw [he,ENNReal.ofReal_one]
  calc
    programValue μ ρ B N = dualRatio μ B N Q^(1/(2:ℝ)) := by
      unfold programValue
      rw [hdual]
    _ = ENNReal.ofReal (3*Real.sqrt 7/2)*
        (ENNReal.ofReal (2/(3*Real.sqrt 7))*dualRatio μ B N Q^(1/(2:ℝ))) := by
      rw [← mul_assoc,hc,one_mul]
    _ ≤ _ := mul_le_mul_right hm _

theorem factor_ne_zero : ENNReal.ofReal (3*Real.sqrt 7/2) ≠ 0 :=
  (ENNReal.ofReal_pos.mpr (by positivity [Real.sqrt_pos.mpr (show (0:ℝ) < 7 by norm_num)])).ne'

theorem program_le_risk_truncation_factor {R : Type} [MeasurableSpace R]
    (μ : Measure Gap) [IsProbabilityMeasure μ] (A : AdaptiveEstimator R)
    (ρ B : ℝ) (hρ : 0 < ρ) (hρhalf : ρ ≤ 1/2) (hB : 0 < B)
    (hbudget : RareBudget μ A ρ B) (N : ℕ) (hN : 0 < N) :
    programValue μ ρ B N ≤ ENNReal.ofReal (3*Real.sqrt 7/2)*(rareRisk μ A ρ+
      ENNReal.ofReal (ρ/2*Real.sqrt (B/((N:ℝ)+1)))) := by
  apply prefix_program_factor μ A ρ B hρ hρhalf hB hbudget N hN
    (prefixTruncation A ρ N) (measurable_prefixTruncation A ρ N)
  intro q hq
  have hθ : 0 ≤ signMean μ q.val ∧ signMean μ q.val ≤ ρ :=
    ⟨integral_nonneg (fun d => (q.property.2 d).1),hq⟩
  exact (prefixTruncation_rmsRisk μ A q ρ (signMean μ q.val) B hρ.le hθ hB.le N
    (hbudget q hq)).trans (add_le_add
      (le_iSup_of_le q (le_iSup_of_le hq le_rfl)) le_rfl)

theorem program_le_minimax_truncation_factor (μ : Measure Gap) [IsProbabilityMeasure μ]
    (ρ B : ℝ) (hρ : 0 < ρ) (hρhalf : ρ ≤ 1/2) (hB : 0 < B) (N : ℕ) (hN : 0 < N) :
    programValue μ ρ B N ≤ ENNReal.ofReal (3*Real.sqrt 7/2)*(rareMinimaxRisk μ ρ B+
      ENNReal.ofReal (ρ/2*Real.sqrt (B/((N:ℝ)+1)))) := by
  let C := ENNReal.ofReal (3*Real.sqrt 7/2)
  have hC0 : C ≠ 0 := factor_ne_zero
  have hCt : C ≠ ⊤ := ENNReal.ofReal_ne_top
  let e := ENNReal.ofReal (ρ/2*Real.sqrt (B/((N:ℝ)+1)))
  have h : programValue μ ρ B N/C-e ≤ rareMinimaxRisk μ ρ B := by
    apply le_sInf
    rintro t ⟨R,mR,A,hbudget,rfl⟩
    apply tsub_le_iff_right.mpr
    apply (ENNReal.div_le_iff hC0 hCt).mpr
    simpa only [mul_comm] using program_le_risk_truncation_factor μ A ρ B hρ hρhalf hB hbudget N hN
  have hh := tsub_le_iff_right.mp h
  have hhh := (ENNReal.div_le_iff hC0 hCt).mp hh
  simpa only [mul_comm] using hhh

/-- The upper half of the main target. -/
theorem infinite_program_upper_factor (μ : Measure Gap) [IsProbabilityMeasure μ]
    (ρ B : ℝ) (hρ : 0 < ρ) (hρhalf : ρ ≤ 1/2) (hB : 0 < B) :
    ThresholdHC.Genie.infiniteProgramValue μ ρ B ≤
      ENNReal.ofReal (3*Real.sqrt 7/2)*rareMinimaxRisk μ ρ B := by
  let C := ENNReal.ofReal (3*Real.sqrt 7/2)
  have hC0 : C ≠ 0 := factor_ne_zero
  have hCt : C ≠ ⊤ := ENNReal.ofReal_ne_top
  have hbound (N : ℕ) : ThresholdHC.Genie.infiniteProgramValue μ ρ B/C ≤ rareMinimaxRisk μ ρ B+
      ENNReal.ofReal (ρ/2*Real.sqrt (B/(((N+1:ℕ):ℝ)+1))) := by
    apply (ENNReal.div_le_iff hC0 hCt).mpr
    have h := (iInf_le (fun n : ℕ => programValue μ ρ B (n+1)) N).trans
      (program_le_minimax_truncation_factor μ ρ B hρ hρhalf hB (N+1) (Nat.succ_pos N))
    simpa only [ThresholdHC.Genie.infiniteProgramValue,mul_comm] using h
  have he : Tendsto (fun N : ℕ => ENNReal.ofReal (ρ/2*Real.sqrt (B/(((N+1:ℕ):ℝ)+1))))
      atTop (𝓝 0) := (tendsto_add_atTop_iff_nat 1).mpr (truncation_error_tendsto ρ B)
  have ht : Tendsto (fun N : ℕ => rareMinimaxRisk μ ρ B+
      ENNReal.ofReal (ρ/2*Real.sqrt (B/(((N+1:ℕ):ℝ)+1)))) atTop (𝓝 (rareMinimaxRisk μ ρ B)) := by
    simpa only [add_zero] using tendsto_const_nhds.add he
  have hh := ge_of_tendsto ht (Eventually.of_forall hbound)
  have h := (ENNReal.div_le_iff hC0 hCt).mp hh
  simpa only [mul_comm] using h

end ThresholdHC.ProgramFactor
