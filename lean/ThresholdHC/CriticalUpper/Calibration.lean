import ThresholdHC.CriticalUpper.Parameters

/-! Summable classifier errors and polynomial per-level population work. -/

noncomputable section
namespace ThresholdHC.CriticalUpper
open MeasureTheory Set ThresholdHC.CriticalEntropy ThresholdHC.Uniform713
open scoped ENNReal

theorem calibratedScreen_parameter_bounds (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (j : ℕ) :
    let ℓ := 1+Real.log (1/ρ)
    let H := 1+Real.log ℓ
    let n := (j : ℝ)+1
    screenThreshold (screenLevel ρ j) (screenAccuracy j) ≤ 32*H*n ∧
    screenThreshold (screenLevel ρ j) (screenAccuracy j)+Real.log (1/ρ) ≤ 33*ℓ*H*n ∧
    Real.log (cap (screenLevel ρ j)) ≤ 46*ℓ*n ∧
    Real.log (cap (screenLevel ρ j)*ρ) ≤ 46*n := by
  let ℓ := 1+Real.log (1/ρ)
  let H := 1+Real.log ℓ
  let n := (j : ℝ)+1
  change _ ≤ 32*H*n ∧ _ ≤ 33*ℓ*H*n ∧ _ ≤ 46*ℓ*n ∧ _ ≤ 46*n
  have hlogρ := Real.log_nonneg ((one_le_div hρ).mpr hρ1)
  have hℓ : 1 ≤ ℓ := by dsimp [ℓ]; linarith
  have hℓ0 : 0 < ℓ := by linarith
  have hlogℓ : 0 ≤ Real.log ℓ := Real.log_nonneg hℓ
  have hH : 1 ≤ H := by dsimp [H]; linarith
  have hn : 1 ≤ n := by dsimp [n]; linarith [Nat.cast_nonneg (α := ℝ) j]
  have hn0 : 0 < n := by linarith
  have hH0 : 0 < H := by linarith
  have hℓn : ℓ ≤ ℓ*n := le_mul_of_one_le_right hℓ0.le hn
  have hnℓ : n ≤ ℓ*n := le_mul_of_one_le_left hn0.le hℓ
  have hℓn1 : 1 ≤ ℓ*n := hℓ.trans hℓn
  have hHn : H ≤ H*n := le_mul_of_one_le_right hH0.le hn
  have hnH : n ≤ H*n := le_mul_of_one_le_left hn0.le hH
  have hHn1 : 1 ≤ H*n := hH.trans hHn
  have h12 := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 12)
  have h16 := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 16)
  have h32 := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 32)
  have h16n := mul_le_mul_of_nonneg_left h16 hn0.le
  have hlogn := Real.log_le_sub_one_of_pos hn0
  have hm := Real.log_le_log (by positivity : 0 < (2 : ℝ)^(rarityLevel ρ))
    (rarityLevel_bounds ρ hρ hρ1).1
  rw [Real.log_pow] at hm
  have htwo := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
  norm_num at htwo
  have hm' := mul_le_mul_of_nonneg_left htwo (Nat.cast_nonneg (α := ℝ) (rarityLevel ρ))
  have hmℓ : (rarityLevel ρ : ℝ) ≤ 2*ℓ := by dsimp [ℓ]; nlinarith
  have hJ : (screenLevel ρ j : ℝ)+1 ≤ 12*ℓ*n := by
    simp only [screenLevel,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_one]
    change (rarityLevel ρ : ℝ)+4*n+5+1 ≤ 12*ℓ*n
    nlinarith only [hmℓ,hℓn,hnℓ,hℓn1]
  have hlogJ := Real.log_le_log (by positivity : 0 < (screenLevel ρ j : ℝ)+1) hJ
  rw [Real.log_mul (by positivity : 12*ℓ ≠ 0) hn0.ne',
    Real.log_mul (by norm_num : (12 : ℝ) ≠ 0) hℓ0.ne'] at hlogJ
  have hAeq : screenThreshold (screenLevel ρ j) (screenAccuracy j) =
      1+Real.log ((screenLevel ρ j : ℝ)+1)+n*Real.log 16 := by
    unfold screenThreshold screenAccuracy
    rw [div_inv_eq_mul,Real.log_mul (by positivity) (by positivity),Real.log_pow]
    simp only [Nat.cast_add,Nat.cast_one]
    dsimp [n]
    ring
  have hA : screenThreshold (screenLevel ρ j) (screenAccuracy j) ≤ 32*H*n := by
    have hHdef : H = 1+Real.log ℓ := rfl
    nlinarith only [hAeq,hlogJ,h12,h16n,hlogn,hHdef,hHn,hnH,hHn1]
  have hHnℓ : H*n ≤ ℓ*(H*n) := le_mul_of_one_le_left (by positivity) hℓ
  have hℓHn : ℓ ≤ ℓ*(H*n) := le_mul_of_one_le_right hℓ0.le hHn1
  have hA₁ : screenThreshold (screenLevel ρ j) (screenAccuracy j)+Real.log (1/ρ) ≤ 33*ℓ*H*n := by
    have hℓdef : ℓ = 1+Real.log (1/ρ) := rfl
    nlinarith only [hA,hℓdef,hHnℓ,hℓHn]
  have hN : Real.log (cap (screenLevel ρ j)) ≤ 46*ℓ*n := by
    rw [screenLevel_cap,Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by norm_num) (by positivity),Real.log_pow,Real.log_pow]
    simp only [Nat.cast_add,Nat.cast_one]
    change Real.log 32+(rarityLevel ρ : ℝ)*Real.log 2+n*Real.log 16 ≤ 46*ℓ*n
    have hℓdef : ℓ = 1+Real.log (1/ρ) := rfl
    nlinarith only [h32,hm,h16n,hℓdef,hℓn,hnℓ,hℓn1]
  have hNρ : cap (screenLevel ρ j)*ρ ≤ 32*(16 : ℝ)^(j+1) := by
    have hmρ := (le_div_iff₀ hρ).mp (rarityLevel_bounds ρ hρ hρ1).1
    calc
      _ = (32*(16 : ℝ)^(j+1))*((2 : ℝ)^(rarityLevel ρ)*ρ) := by rw [screenLevel_cap]; ring
      _ ≤ (32*(16 : ℝ)^(j+1))*1 := mul_le_mul_of_nonneg_left hmρ (by positivity)
      _ = _ := mul_one _
  have hlogNρ := Real.log_le_log (mul_pos (cap_pos _) hρ) hNρ
  rw [Real.log_mul (by norm_num : (32 : ℝ) ≠ 0)
    (by positivity : (16 : ℝ)^(j+1) ≠ 0),Real.log_pow] at hlogNρ
  simp only [Nat.cast_add,Nat.cast_one] at hlogNρ
  change Real.log (cap (screenLevel ρ j)*ρ) ≤ Real.log 32+n*Real.log 16 at hlogNρ
  refine ⟨hA,hA₁,hN,?_⟩
  nlinarith only [hlogNρ,h32,h16n,hn]

theorem calibratedScreen_work (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (j : ℕ)
    (q : ℝ → unitInterval) (hq : Measurable q)
    (hmass : (∫ d, (q d : ℝ) ∂criticalGapLaw) ≤ ρ) :
    populationExpectedWork criticalGapLaw (Measure.dirac ())
      (fun d => criticalParameter d false) (fun d => criticalParameter d true) q (calibratedScreen ρ j) ≤
    ENNReal.ofReal (500000*criticalLogFactor ρ*((j : ℝ)+1)^2) := by
  let ℓ := 1+Real.log (1/ρ)
  let H := 1+Real.log ℓ
  let n := (j : ℝ)+1
  let A₀ := screenThreshold (screenLevel ρ j) (screenAccuracy j)
  let A₁ := A₀+Real.log (1/ρ)
  have hlogρ := Real.log_nonneg ((one_le_div hρ).mpr hρ1)
  have hℓ : 1 ≤ ℓ := by dsimp [ℓ]; linarith
  have hℓ0 : 0 < ℓ := by linarith
  have hH : 1 ≤ H := by dsimp [H]; linarith [Real.log_nonneg hℓ]
  have hH0 : 0 < H := by linarith
  have hn : 1 ≤ n := by dsimp [n]; linarith [Nat.cast_nonneg (α := ℝ) j]
  have hn0 : 0 < n := by linarith
  have hℓn1 : 1 ≤ ℓ*n := hℓ.trans (le_mul_of_one_le_right hℓ0.le hn)
  have hA₀ : 1 ≤ A₀ := screenThreshold_ge_one _ _ (screenAccuracy_pos j) (screenAccuracy_le_one j)
  have hA₁ : 1 ≤ A₁ := by dsimp [A₁]; linarith
  have hA₀0 : 0 < A₀ := by linarith
  have hA₁0 : 0 < A₁ := by linarith
  have hK₀ : 1 ≤ 160*A₀ := by linarith
  have hK₁ : 1 ≤ 160*A₁ := by linarith
  obtain ⟨hA,hA',hN,hNρ⟩ := calibratedScreen_parameter_bounds ρ hρ hρ1 j
  change A₀ ≤ 32*H*n at hA
  change A₁ ≤ 33*ℓ*H*n at hA'
  change Real.log (cap (screenLevel ρ j)) ≤ 46*ℓ*n at hN
  change Real.log (cap (screenLevel ρ j)*ρ) ≤ 46*n at hNρ
  have hl₀ := (Real.log_le_log (div_pos (cap_pos _) (mul_pos (by norm_num) hA₀0))
    (div_le_self (cap_pos _).le hK₀)).trans hN
  have hl₁ := (Real.log_le_log (div_pos (mul_pos (cap_pos _) hρ) (mul_pos (by norm_num) hA₁0))
    (div_le_self (mul_pos (cap_pos _) hρ).le hK₁)).trans hNρ
  have hc₀ : 2+max 0 (Real.log (cap (screenLevel ρ j)/(160*A₀))) ≤ 48*ℓ*n := by
    have hm := max_le (by positivity : 0 ≤ 46*ℓ*n) hl₀
    nlinarith only [hm,hℓn1]
  have hc₁ : 2+max 0 (Real.log (cap (screenLevel ρ j)*ρ/(160*A₁))) ≤ 48*n := by
    have hm := max_le (by positivity : 0 ≤ 46*n) hl₁
    nlinarith only [hm,hn]
  have hb₀ := mul_le_mul (mul_le_mul_of_nonneg_left hA (by norm_num : (0 : ℝ) ≤ 160)) hc₀
    (by positivity : 0 ≤ 2+max 0 (Real.log (cap (screenLevel ρ j)/(160*A₀)))) (by positivity)
  have hb₁ := mul_le_mul (mul_le_mul_of_nonneg_left hA' (by norm_num : (0 : ℝ) ≤ 160)) hc₁
    (by positivity : 0 ≤ 2+max 0 (Real.log (cap (screenLevel ρ j)*ρ/(160*A₁)))) (by positivity)
  have hb := screen_population_work_le A₀ A₁ hA₀ hA₁ (screenLevel ρ j) ρ hρ hρ1 q hq hmass
  apply hb.trans
  apply ENNReal.ofReal_le_ofReal
  change _ ≤ 500000*(ℓ*H)*n^2
  calc
    _ ≤ 160*(32*H*n)*(48*ℓ*n)+160*(33*ℓ*H*n)*(48*n) := add_le_add hb₀ hb₁
    _ = 499200*(ℓ*H)*n^2 := by ring
    _ ≤ _ := by nlinarith [sq_nonneg n,mul_pos hℓ0 hH0]

end ThresholdHC.CriticalUpper
