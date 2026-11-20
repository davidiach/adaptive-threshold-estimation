import ThresholdHC.PaperStatements.Specification
import ThresholdHC.CriticalWindow.Full
import ThresholdHC.HardBudget.CriticalTransport
import ThresholdHC.CriticalPsi.Full
import ThresholdHC.PaperCorollaries.PsiSequence

/-! The critical law of the critical theorem with explicit constants.

The density `32d` on `(0,1/4]` is the exact power law `F(d) = (4d)^2`, and the
critical theorem's minimax risk is the rare-event minimax risk of that law, by the
budget and risk transport of `HardBudget`. The quadratic-law target of the
critical window then gives explicit constants. Along `ρ_n = exp(-exp n)`,
`B_n = ρ_n^{-2}`, the rate is `ρ √(ρ L H)` and `Ψ ≤ 16 ρ √(ρ L)` by the closed
form of `CriticalPsi`, so the ratio is at least `10^{-18} √H / 16`. -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace ThresholdHC.PaperStatements
open ThresholdHC.Tier6 ThresholdHC.RareAboveTwo ThresholdHC.CriticalEntropy
open ThresholdHC.ConfidenceTransfer

theorem critical_power_law : ExactPowerLaw criticalPositiveLaw 2 (1/4) := by
  intro x hx
  have hmeas : MeasurableSet {d : ℝ | d ≤ x} := measurableSet_Iic
  have hmap : criticalPositiveLaw.real {d : Gap | (d : ℝ) ≤ x} =
      criticalGapLaw.real {d : ℝ | d ≤ x} := by
    rw [← criticalPositiveLaw_map, Measure.real, Measure.real,
      Measure.map_apply measurable_subtype_coe hmeas]
    rfl
  rw [hmap]
  by_cases hx4 : x ≤ 1/4
  · rw [CriticalPsi.criticalGap_Iic_mass x hx.le hx4]
    have h16 : (x/(1/4))^(2:ℝ) = 16*x^2 := by rw [Real.rpow_two]; ring
    rw [h16, min_eq_right]
    nlinarith
  · push Not at hx4
    have h1 : criticalGapLaw.real {d : ℝ | d ≤ 1/4} = 1 := by
      rw [CriticalPsi.criticalGap_Iic_mass (1/4) (by norm_num) le_rfl]; norm_num
    have hle : criticalGapLaw.real {d : ℝ | d ≤ 1/4} ≤ criticalGapLaw.real {d : ℝ | d ≤ x} :=
      measureReal_mono (fun d (hd : d ≤ 1/4) => show d ≤ x by linarith)
    have hle1 : criticalGapLaw.real {d : ℝ | d ≤ x} ≤ 1 := measureReal_le_one
    have hgt : 1 < x/(1/4) := by rw [lt_div_iff₀ (by norm_num)]; linarith
    rw [Real.rpow_two, min_eq_left (by nlinarith)]
    linarith

theorem critical_minimax_eq (ρ B : ℝ) :
    criticalMinimaxRisk ρ B = rareMinimaxRisk criticalPositiveLaw ρ B := by
  unfold criticalMinimaxRisk rareMinimaxRisk
  congr 1
  ext t
  constructor
  · rintro ⟨R, _, A, hA, rfl⟩
    exact ⟨R, _, A, (HardBudget.critical_budget_equivalence A ρ B).1 hA,
      HardBudget.critical_risk_equivalence A ρ⟩
  · rintro ⟨R, _, A, hA, rfl⟩
    exact ⟨R, _, A, (HardBudget.critical_budget_equivalence A ρ B).2 hA,
      (HardBudget.critical_risk_equivalence A ρ).symm⟩

theorem critical_explicit (ρ B : ℝ) (hρ : 0 < ρ) (hρ4 : ρ ≤ 1/4) (hB : 0 < B) :
    let C := Real.sqrt (ρ * criticalLogFactor ρ / B)
    ENNReal.ofReal ((10 : ℝ)⁻¹ ^ 18 * min ρ C) ≤ criticalMinimaxRisk ρ B ∧
    criticalMinimaxRisk ρ B ≤ ENNReal.ofReal (1360000 * min ρ C) := by
  intro C
  rw [critical_minimax_eq]
  exact CriticalWindow.window_quadratic_risk criticalPositiveLaw ρ B hρ hρ4 hB critical_power_law

theorem log_ten_lt : Real.log 10 < 230304/100000 := by
  have h : (10 : ℝ) ^ 31 < 2 ^ 103 := by norm_num
  have hl := Real.log_lt_log (by positivity) h
  rw [Real.log_pow, Real.log_pow] at hl
  have h2 := Real.log_two_lt_d9
  push_cast at hl
  nlinarith

theorem slow_divergence (ρ : ℝ) (hρ : (10 : ℝ)⁻¹ ^ 100 ≤ ρ) (hρ4 : ρ ≤ 1/4) :
    Real.sqrt (1 + Real.log (1 + Real.log (1/ρ))) < 127/50 := by
  have hρ0 : 0 < ρ := lt_of_lt_of_le (by positivity) hρ
  have hinv : 1/ρ ≤ (10 : ℝ) ^ 100 := by
    rw [div_le_iff₀ hρ0]
    have : (10 : ℝ) ^ 100 * (10 : ℝ)⁻¹ ^ 100 = 1 := by
      rw [← mul_pow]; norm_num
    nlinarith [pow_pos (show (0:ℝ) < 10 by norm_num) 100]
  have hlog : Real.log (1/ρ) ≤ 100 * Real.log 10 := by
    have := Real.log_le_log (by positivity) hinv
    rw [Real.log_pow] at this; push_cast at this; linarith
  have hlog0 : 0 ≤ Real.log (1/ρ) :=
    Real.log_nonneg (by rw [le_div_iff₀ hρ0]; linarith)
  have h10 := log_ten_lt
  set L := 1 + Real.log (1/ρ) with hL
  have hLup : L < 23131/100 := by linarith
  have hL1 : 1 ≤ L := by linarith
  have hlogL : Real.log L < 54516/10000 := by
    have h256 : Real.log L = Real.log 256 + Real.log (L/256) := by
      rw [← Real.log_mul (by norm_num) (by positivity)]; congr 1; ring
    have hq := Real.log_le_sub_one_of_pos (show 0 < L/256 by positivity)
    have h8 : Real.log 256 = 8 * Real.log 2 := by
      rw [show (256 : ℝ) = 2 ^ 8 by norm_num, Real.log_pow]; norm_num
    have h2 := Real.log_two_lt_d9
    rw [h256, h8]
    have : L/256 - 1 < 23131/100/256 - 1 := by linarith
    norm_num at h2 this ⊢
    linarith
  rw [Real.sqrt_lt' (by norm_num)]
  norm_num
  linarith

theorem critical_psi_sequence (n : ℕ) (hn : 3 ≤ n) :
    ENNReal.ofReal ((10 : ℝ)⁻¹ ^ 18 / 16 *
        Real.sqrt (1 + Real.log (1 + Real.log (1 / Real.exp (-Real.exp n)))) *
        CriticalPsi.criticalPsi (Real.exp (-Real.exp n))
          (1 / Real.sqrt (1 / Real.exp (-Real.exp n) ^ 2))) ≤
      criticalMinimaxRisk (Real.exp (-Real.exp n)) (1 / Real.exp (-Real.exp n) ^ 2) ∧
    Real.sqrt (1 + n) ≤ Real.sqrt (1 + Real.log (1 + Real.log (1 / Real.exp (-Real.exp n)))) := by
  set ℓ := Real.exp (n : ℝ) with hℓdef
  set ρ := Real.exp (-ℓ) with hρdef
  have hρ : 0 < ρ := Real.exp_pos _
  have hlog : Real.log (1/ρ) = ℓ := by rw [hρdef, one_div, Real.log_inv, Real.log_exp, neg_neg]
  have hℓ20 : 20 ≤ ℓ := by
    rw [hℓdef]
    exact PaperCorollaries.exp_three_ge.trans (Real.exp_le_exp.2 (by exact_mod_cast hn))
  have hρ4 : ρ ≤ 1/4 := by
    have h1 : ρ ≤ Real.exp (-2) := Real.exp_le_exp.2 (by linarith)
    have h2 : Real.exp (-2) ≤ 1/4 := by
      rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos 2) (by norm_num)]
      have h3 : Real.exp 2 = Real.exp 1 ^ 2 := by rw [← Real.exp_nat_mul]; norm_num
      have he := Real.exp_one_gt_d9
      nlinarith
    linarith
  set B := 1 / ρ ^ 2 with hBdef
  have hB : 0 < B := by positivity
  have hsB : Real.sqrt B = 1 / ρ := by
    rw [hBdef, Real.sqrt_div' _ (sq_nonneg ρ), Real.sqrt_one, Real.sqrt_sq hρ.le]
  have hh : 1 / Real.sqrt B = ρ := by rw [hsB]; field_simp
  set H := 1 + Real.log (1 + ℓ) with hHdef
  have hlogℓ0 : 0 ≤ Real.log (1 + ℓ) := Real.log_nonneg (by linarith)
  have hH0 : 0 ≤ H := by linarith
  have hHup : H ≤ 1 + ℓ := by
    have := Real.log_le_sub_one_of_pos (show 0 < 1 + ℓ by linarith); linarith
  set s := Real.sqrt (ρ * (1 + ℓ)) with hsdef
  set t := Real.sqrt H with htdef
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have ht0 : 0 ≤ t := Real.sqrt_nonneg _
  have hs2 : s ^ 2 = ρ * (1 + ℓ) := Real.sq_sqrt (by positivity)
  have ht2 : t ^ 2 = H := Real.sq_sqrt hH0
  -- the critical rate is ρ s t, and s t ≤ 1
  have hfac : criticalLogFactor ρ = (1 + ℓ) * H := by
    unfold criticalLogFactor; rw [hlog]
  have hC : Real.sqrt (ρ * criticalLogFactor ρ / B) = ρ * s * t := by
    rw [hfac, hBdef]
    have : ρ * ((1 + ℓ) * H) / (1 / ρ ^ 2) = (ρ * s * t) ^ 2 := by
      rw [mul_pow, mul_pow, hs2, ht2]; field_simp
    rw [this, Real.sqrt_sq (by positivity)]
  have hst : s * t ≤ 1 := by
    have he := PaperCorollaries.sixteen_le_exp hℓ20
    have hρe : ρ * Real.exp ℓ = 1 := by rw [hρdef, ← Real.exp_add]; simp
    have h1 : (s * t) ^ 2 ≤ 1 := by
      rw [mul_pow, hs2, ht2]
      have h2 : ρ * (1 + ℓ) * H ≤ ρ * (1 + ℓ) * (1 + ℓ) :=
        mul_le_mul_of_nonneg_left hHup (by positivity)
      have h3 : 16 * (ρ * (ℓ * (1 + ℓ))) ≤ ρ * Real.exp ℓ := by
        have := mul_le_mul_of_nonneg_left he hρ.le; nlinarith
      nlinarith
    nlinarith [mul_nonneg hs0 ht0]
  have hmin : min ρ (ρ * s * t) = ρ * s * t := by
    apply min_eq_right
    have := mul_le_mul_of_nonneg_left hst hρ.le
    linarith [show ρ * s * t = ρ * (s * t) by ring]
  obtain ⟨hlo, -⟩ := critical_explicit ρ B hρ hρ4 hB
  rw [hC, hmin] at hlo
  -- Ψ ≤ 16 ρ s
  obtain ⟨-, hpsi⟩ := CriticalPsi.critical_psi_rate ρ (1 / Real.sqrt B) hρ hρ4 (by rw [hh]; exact hρ)
  rw [hh, hlog] at hpsi
  have hpsi' : CriticalPsi.criticalPsi ρ ρ ≤ 16 * (ρ * s) :=
    hpsi.trans (by gcongr; exact min_le_right _ _)
  rw [hlog, hh]
  constructor
  · refine le_trans (ENNReal.ofReal_le_ofReal ?_) hlo
    calc (10 : ℝ)⁻¹ ^ 18 / 16 * t * CriticalPsi.criticalPsi ρ ρ
        ≤ (10 : ℝ)⁻¹ ^ 18 / 16 * t * (16 * (ρ * s)) :=
          mul_le_mul_of_nonneg_left hpsi' (by positivity)
      _ = (10 : ℝ)⁻¹ ^ 18 * (ρ * s * t) := by ring
  · apply Real.sqrt_le_sqrt
    have h1 : (n : ℝ) ≤ Real.log (1 + ℓ) := by
      rw [show (n : ℝ) = Real.log ℓ by rw [hℓdef, Real.log_exp]]
      exact Real.log_le_log (by positivity) (by linarith)
    linarith

end ThresholdHC.PaperStatements
