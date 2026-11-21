import ThresholdHC.EarlyPilot.Law
import ThresholdHC.ArbitraryLawAdaptation.PilotOnset

/-! Easy laws: the early-stopping pilot when every gap is at least `a > 0`.

The work envelope of depth `j + 1` is then at most `1024 (j + 2)/a^2`, so the
expected work is at most `m M sum_(j<J) 1024 (j + 2)/a^2 = 512 m M J (J + 3)/a^2`.
The coin cap is `M ≤ (√(64/ρ) + 1) 2^J` and the authorized flips are
`m sum_j b_j ≥ m 4^J/2` for `J ≥ 1`, so for fixed `a`, `ρ` and `ε` the ratio drops below
`ε` once `J^2/2^J` is small, at a depth that does not depend on the gap law.
These bounds are derived here; the paper's remark is qualitative. -/

noncomputable section
open MeasureTheory Filter Topology
open scoped ENNReal
namespace ThresholdHC.EarlyPilot
open ThresholdHC.Tier6 ThresholdHC.ArbitraryLawAdaptation

theorem sum_range_add_two (J : ℕ) :
    ∑ j ∈ Finset.range J, ((j : ℝ) + 1 + 1) = (J : ℝ) * (J + 3) / 2 := by
  induction J with
  | zero => simp
  | succ J ih =>
    rw [Finset.sum_range_succ, ih]
    push_cast
    ring

theorem easy_law_work_holds : EasyLawWorkStatement := by
  intro J m ρ A hA μ _ q i a ha hae
  refine (early_pilot_work_holds J m ρ A hA μ q i).trans (ENNReal.ofReal_le_ofReal ?_)
  have hW : ∀ j : ℕ, ∫ d : Gap, tailWorkEnvelope (j + 1) d ∂μ ≤
      1024 * ((j : ℝ) + 1 + 1) / a ^ 2 := by
    intro j
    calc ∫ d : Gap, tailWorkEnvelope (j + 1) d ∂μ
        ≤ ∫ _d : Gap, 1024 * (((j + 1 : ℕ) : ℝ) + 1) / a ^ 2 ∂μ :=
          integral_mono_ae (integrable_tailWorkEnvelope μ (j + 1)) (integrable_const _)
            (hae.mono fun d hd => tailWorkEnvelope_le_core (j + 1) ha d hd)
      _ = 1024 * ((j : ℝ) + 1 + 1) / a ^ 2 := by
          simp
  have hterm : ∀ j : ℕ, min (pilotBudget J (j + 1) : ℝ)
      ((pilotCoinCap J ρ : ℝ) * ∫ d : Gap, tailWorkEnvelope (j + 1) d ∂μ) ≤
        (pilotCoinCap J ρ : ℝ) * (1024 * ((j : ℝ) + 1 + 1) / a ^ 2) := fun j =>
    (min_le_right _ _).trans (mul_le_mul_of_nonneg_left (hW j) (Nat.cast_nonneg _))
  calc (m : ℝ) * ∑ j ∈ Finset.range J, min (pilotBudget J (j + 1) : ℝ)
        ((pilotCoinCap J ρ : ℝ) * ∫ d : Gap, tailWorkEnvelope (j + 1) d ∂μ)
      ≤ (m : ℝ) * ∑ j ∈ Finset.range J,
          (pilotCoinCap J ρ : ℝ) * (1024 * ((j : ℝ) + 1 + 1) / a ^ 2) :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun j _ => hterm j) (Nat.cast_nonneg _)
    _ = (m : ℝ) * ((pilotCoinCap J ρ : ℝ) * 1024 / a ^ 2 *
          ∑ j ∈ Finset.range J, ((j : ℝ) + 1 + 1)) := by
        congr 1
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        ring
    _ = 512 * m * pilotCoinCap J ρ * J * (J + 3) / a ^ 2 := by
        rw [sum_range_add_two]
        ring

/-- The coin cap grows like `2^J`: `M ≤ (√(64/ρ) + 1) 2^J`. -/
theorem pilotCoinCap_le (J : ℕ) {ρ : ℝ} (hρ : 0 < ρ) :
    (pilotCoinCap J ρ : ℝ) ≤ (Real.sqrt (64 / ρ) + 1) * 2 ^ J := by
  have h4 : (4 : ℝ) ^ J = 2 ^ J * 2 ^ J := by
    rw [← mul_pow]
    norm_num
  have hs : Real.sqrt (64 * (4 : ℝ) ^ J / ρ) = Real.sqrt (64 / ρ) * 2 ^ J := by
    have he : 64 * (4 : ℝ) ^ J / ρ = 64 / ρ * (2 ^ J * 2 ^ J) := by
      rw [h4]
      ring
    rw [he, Real.sqrt_mul (by positivity), Real.sqrt_mul_self (by positivity)]
  have hceil : (pilotCoinCap J ρ : ℝ) ≤ Real.sqrt (64 * (4 : ℝ) ^ J / ρ) + 1 :=
    (Nat.ceil_lt_add_one (Real.sqrt_nonneg _)).le
  have h1 : (1 : ℝ) ≤ 2 ^ J := one_le_pow₀ (by norm_num)
  rw [hs] at hceil
  linarith

theorem easy_law_vanishing_holds : EasyLawVanishingStatement := by
  intro a ρ ε ha hρ hε
  have hc0 : 0 ≤ Real.sqrt (64 / ρ) := Real.sqrt_nonneg _
  have hδ : 0 < ε * a ^ 2 / (4096 * (Real.sqrt (64 / ρ) + 1)) := by positivity
  have hlim := tendsto_pow_const_div_const_pow_of_one_lt 2 (one_lt_two : (1 : ℝ) < 2)
  obtain ⟨N, hN⟩ := eventually_atTop.1 ((tendsto_order.1 hlim).2 _ hδ)
  refine ⟨max N 1, fun μ _ hae J m A hJ hA q i => ?_⟩
  refine (easy_law_work_holds J m ρ A hA μ q i a ha hae).trans (ENNReal.ofReal_le_ofReal ?_)
  have hJ1 : 1 ≤ J := le_of_max_le_right hJ
  have hsmall : (J : ℝ) ^ 2 / 2 ^ J < ε * a ^ 2 / (4096 * (Real.sqrt (64 / ρ) + 1)) :=
    hN J (le_of_max_le_left hJ)
  have hpow : (0 : ℝ) < 2 ^ J := by positivity
  have hsq : (J : ℝ) ^ 2 ≤ ε * a ^ 2 / (4096 * (Real.sqrt (64 / ρ) + 1)) * 2 ^ J :=
    ((div_lt_iff₀ hpow).1 hsmall).le
  have hc1 : (0 : ℝ) < 4096 * (Real.sqrt (64 / ρ) + 1) := by positivity
  have h2 : 4096 * (Real.sqrt (64 / ρ) + 1) * (J : ℝ) ^ 2 ≤ ε * a ^ 2 * 2 ^ J := by
    calc 4096 * (Real.sqrt (64 / ρ) + 1) * (J : ℝ) ^ 2
        ≤ 4096 * (Real.sqrt (64 / ρ) + 1) *
            (ε * a ^ 2 / (4096 * (Real.sqrt (64 / ρ) + 1)) * 2 ^ J) := by gcongr
      _ = ε * a ^ 2 * 2 ^ J := by
          field_simp
  have hM := pilotCoinCap_le J hρ
  have hJ3 : (J : ℝ) + 3 ≤ 4 * J := by
    have : (1 : ℝ) ≤ J := by exact_mod_cast hJ1
    linarith
  have hspan : (4 : ℝ) ^ J ≤ 2 * pilotSpan J := by exact_mod_cast le_two_mul_pilotSpan hJ1
  have h4 : (4 : ℝ) ^ J = 2 ^ J * 2 ^ J := by
    rw [← mul_pow]
    norm_num
  have hcost : (pilotCost J m : ℝ) = m * pilotSpan J := by
    rw [pilotCost_eq]
    push_cast
    ring
  have key : 512 * (pilotCoinCap J ρ : ℝ) * J * (J + 3) ≤ ε * pilotSpan J * a ^ 2 := by
    calc 512 * (pilotCoinCap J ρ : ℝ) * J * (J + 3)
        ≤ 512 * ((Real.sqrt (64 / ρ) + 1) * 2 ^ J) * J * (4 * J) := by gcongr
      _ = (4096 * (Real.sqrt (64 / ρ) + 1) * (J : ℝ) ^ 2) * 2 ^ J / 2 := by ring
      _ ≤ (ε * a ^ 2 * 2 ^ J) * 2 ^ J / 2 := by gcongr
      _ = ε * a ^ 2 * 4 ^ J / 2 := by rw [h4]; ring
      _ ≤ ε * a ^ 2 * (2 * pilotSpan J) / 2 := by gcongr
      _ = ε * pilotSpan J * a ^ 2 := by ring
  rw [hcost, div_le_iff₀ (by positivity)]
  calc 512 * (m : ℝ) * pilotCoinCap J ρ * J * (J + 3)
      = m * (512 * (pilotCoinCap J ρ : ℝ) * J * (J + 3)) := by ring
    _ ≤ m * (ε * pilotSpan J * a ^ 2) := mul_le_mul_of_nonneg_left key (Nat.cast_nonneg _)
    _ = ε * (m * pilotSpan J) * a ^ 2 := by ring

end ThresholdHC.EarlyPilot
