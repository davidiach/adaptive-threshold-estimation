import ThresholdHC.AnytimeLower.TestingSchedule

/-!
The constant-sign testing schedule.

The base sign law is the constant `3 rho/4`; the `k`-th alternative is the
constant `3 rho/4 + rho/(4 3^k)`. The budget `N_k` is the largest integer
whose chi-square information `N_k a_k^2/(theta(1-theta))` stays below
`(1-delta) log(k+2)`. The floor and the drift of `log log N_k` are absorbed
eventually by the slack `39/27` between `theta(1-theta) >= 39 rho/64` and the
target coefficient `3 rho/64 = 27 rho/576`.
-/

noncomputable section
open Real Filter
open scoped Topology
namespace ThresholdHC.BernoulliTimeUniform
open ThresholdHC.AnytimeLower

/-- The displacement of the `k`-th alternative mean. -/
def meanShift (ρ : ℝ) (k : ℕ) : ℝ := ρ/(4*3^k)

/-- The Bernoulli variance of the base constant sign law `3 rho/4`. -/
def baseVar (ρ : ℝ) : ℝ := (3*ρ/4)*(1-3*ρ/4)

/-- The displacement in chi-square units. -/
def shiftScale (ρ : ℝ) (k : ℕ) : ℝ := meanShift ρ k/Real.sqrt (baseVar ρ)

/-- The observation budget at which the `k`-th alternative is tested. -/
def scheduleBudget (ρ δ : ℝ) (k : ℕ) : ℕ := testingBudget (2*δ-1) (shiftScale ρ) k

theorem meanShift_pos {ρ : ℝ} (hρ : 0 < ρ) (k : ℕ) : 0 < meanShift ρ k := by
  unfold meanShift; positivity

theorem meanShift_le {ρ : ℝ} (hρ : 0 < ρ) (k : ℕ) : meanShift ρ k ≤ ρ/4 := by
  unfold meanShift
  apply div_le_div_of_nonneg_left hρ.le (by norm_num)
  have : (1:ℝ) ≤ 3^k := one_le_pow₀ (by norm_num)
  linarith

theorem meanShift_antitone {ρ : ℝ} (hρ : 0 < ρ) : Antitone (meanShift ρ) := by
  intro i j hij
  unfold meanShift
  apply div_le_div_of_nonneg_left hρ.le (by positivity)
  have : (3:ℝ)^i ≤ 3^j := pow_le_pow_right₀ (by norm_num) hij
  linarith

theorem meanShift_sep {ρ : ℝ} (hρ : 0 < ρ) (i k : ℕ) (hik : i < k) :
    3*meanShift ρ k ≤ meanShift ρ i := by
  unfold meanShift
  have h : (3:ℝ)*3^i ≤ 3^k := by
    rw [← pow_succ']; exact pow_le_pow_right₀ (by norm_num) hik
  rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by positivity)]
  have h3 : (0:ℝ) < 3^i := by positivity
  nlinarith

theorem baseVar_pos {ρ : ℝ} (hρ : 0 < ρ) (hρ4 : ρ ≤ 1/4) : 0 < baseVar ρ := by
  unfold baseVar
  exact mul_pos (by positivity) (by linarith)

theorem baseVar_lower {ρ : ℝ} (hρ : 0 < ρ) (hρ4 : ρ ≤ 1/4) : 39*ρ/64 ≤ baseVar ρ := by
  unfold baseVar
  nlinarith [mul_nonneg hρ.le (sub_nonneg.mpr hρ4)]

theorem shiftScale_pos {ρ : ℝ} (hρ : 0 < ρ) (hρ4 : ρ ≤ 1/4) (k : ℕ) : 0 < shiftScale ρ k :=
  div_pos (meanShift_pos hρ k) (Real.sqrt_pos.mpr (baseVar_pos hρ hρ4))

theorem shiftScale_antitone {ρ : ℝ} (hρ : 0 < ρ) : Antitone (shiftScale ρ) := by
  intro i j hij
  exact div_le_div_of_nonneg_right (meanShift_antitone hρ hij) (Real.sqrt_nonneg _)

theorem shiftScale_sq {ρ : ℝ} (hρ : 0 < ρ) (hρ4 : ρ ≤ 1/4) (k : ℕ) :
    (shiftScale ρ k)^2 = (meanShift ρ k)^2/baseVar ρ := by
  rw [shiftScale, div_pow, Real.sq_sqrt (baseVar_pos hρ hρ4).le]

theorem scheduleBudget_mono {ρ δ : ℝ} (hρ : 0 < ρ) (hρ4 : ρ ≤ 1/4) (hδ : δ < 1) :
    Monotone (scheduleBudget ρ δ) :=
  testingBudget_mono (by linarith) _ (shiftScale_pos hρ hρ4) (shiftScale_antitone hρ)

theorem scheduleBudget_tendsto {ρ δ : ℝ} (hρ : 0 < ρ) (hρ4 : ρ ≤ 1/4) (hδ : δ < 1) :
    Tendsto (scheduleBudget ρ δ) atTop atTop :=
  testingBudget_tendsto (by linarith) _ (shiftScale_pos hρ hρ4) (shiftScale_antitone hρ)

/-- The tested alternative never carries more than `(1-delta) log(k+2)`
chi-square units. -/
theorem scheduleBudget_information {ρ δ : ℝ} (hρ : 0 < ρ) (hρ4 : ρ ≤ 1/4) (hδ : δ < 1)
    (k : ℕ) :
    (scheduleBudget ρ δ k:ℝ)*(meanShift ρ k)^2/baseVar ρ ≤ (1-δ)*log ((k:ℝ)+2) := by
  have h := testingBudget_information (δ := 2*δ-1) (by linarith) (shiftScale ρ)
    (shiftScale_pos hρ hρ4) k
  rw [shiftScale_sq hρ hρ4, show (1-(2*δ-1))/2 = 1-δ by ring] at h
  rw [mul_div_assoc]
  exact h

/-- The floor loses at most one observation. -/
theorem scheduleBudget_lower {ρ δ : ℝ} (hρ : 0 < ρ) (hρ4 : ρ ≤ 1/4) (k : ℕ) :
    (1-δ)*log ((k:ℝ)+2)*baseVar ρ < ((scheduleBudget ρ δ k:ℝ)+1)*(meanShift ρ k)^2 := by
  have h := Nat.lt_floor_add_one (((1-(2*δ-1))/2)*log ((k:ℝ)+2)/(shiftScale ρ k)^2)
  have he : scheduleBudget ρ δ k =
      ⌊((1-(2*δ-1))/2)*log ((k:ℝ)+2)/(shiftScale ρ k)^2⌋₊ := rfl
  rw [← he, shiftScale_sq hρ hρ4, show (1-(2*δ-1))/2 = 1-δ by ring, div_div_eq_mul_div,
    div_lt_iff₀ (pow_pos (meanShift_pos hρ k) 2)] at h
  exact h

/-- The budget grows at most geometrically. -/
theorem scheduleBudget_upper {ρ δ : ℝ} (hρ : 0 < ρ) (hρ4 : ρ ≤ 1/4) (hδ : δ < 1) (k : ℕ) :
    (scheduleBudget ρ δ k:ℝ) ≤
      (16*(1-δ)*baseVar ρ/ρ^2)*((3:ℝ)^k)^2*log ((k:ℝ)+2) := by
  have hx : 0 ≤ ((1-(2*δ-1))/2)*log ((k:ℝ)+2)/(shiftScale ρ k)^2 :=
    div_nonneg (mul_nonneg (by linarith) (shifted_log_nonneg k)) (sq_nonneg _)
  have h := Nat.floor_le hx
  have he : scheduleBudget ρ δ k =
      ⌊((1-(2*δ-1))/2)*log ((k:ℝ)+2)/(shiftScale ρ k)^2⌋₊ := rfl
  rw [← he] at h
  refine h.trans (le_of_eq ?_)
  rw [shiftScale_sq hρ hρ4]
  have hV := (baseVar_pos hρ hρ4).ne'
  unfold meanShift
  field_simp
  ring

theorem scheduleBudget_log_upper {ρ δ : ℝ} (hρ : 0 < ρ) (hρ4 : ρ ≤ 1/4) (hδ : δ < 1)
    (k : ℕ) (hk : 1 ≤ scheduleBudget ρ δ k) :
    log (scheduleBudget ρ δ k:ℝ) ≤
      (|log (16*(1-δ)*baseVar ρ/ρ^2)|+5)*((k:ℝ)+2) := by
  set C := 16*(1-δ)*baseVar ρ/ρ^2 with hCdef
  have hC : 0 < C := by
    have := baseVar_pos hρ hρ4
    have : 0 < 1-δ := by linarith
    positivity
  have hk0 : (0:ℝ) ≤ k := Nat.cast_nonneg k
  have hL : 0 < log ((k:ℝ)+2) := log_pos (by linarith)
  have hN : (0:ℝ) < scheduleBudget ρ δ k := by exact_mod_cast hk
  have h3 : (0:ℝ) < ((3:ℝ)^k)^2 := by positivity
  have hl := log_le_log hN (scheduleBudget_upper hρ hρ4 hδ k)
  rw [log_mul (mul_pos hC h3).ne' hL.ne', log_mul hC.ne' h3.ne', log_pow, log_pow] at hl
  have hlog3 : log (3:ℝ) ≤ 2 := by
    linarith [log_le_sub_one_of_pos (show (0:ℝ) < 3 by norm_num)]
  have hlogL : log (log ((k:ℝ)+2)) ≤ k := by
    have h1 := log_le_sub_one_of_pos hL
    have h2 := log_le_sub_one_of_pos (show (0:ℝ) < (k:ℝ)+2 by linarith)
    linarith
  have hab := le_abs_self (log C)
  have habs := abs_nonneg (log C)
  push_cast at hl
  nlinarith [mul_le_mul_of_nonneg_left hlog3 hk0, mul_nonneg habs (show (0:ℝ) ≤ (k:ℝ)+1 by linarith)]

theorem scheduleBudget_loglog_upper {ρ δ : ℝ} (hρ : 0 < ρ) (hρ4 : ρ ≤ 1/4) (hδ : δ < 1)
    (k : ℕ) (hk : 2 ≤ scheduleBudget ρ δ k) :
    log (log (scheduleBudget ρ δ k:ℝ)) ≤
      log (|log (16*(1-δ)*baseVar ρ/ρ^2)|+5)+log ((k:ℝ)+2) := by
  have hN : (1:ℝ) < scheduleBudget ρ δ k := by exact_mod_cast hk
  have hD : 0 < |log (16*(1-δ)*baseVar ρ/ρ^2)|+5 := by positivity
  have hk2 : (0:ℝ) < (k:ℝ)+2 := by positivity
  have h := log_le_log (log_pos hN) (scheduleBudget_log_upper hρ hρ4 hδ k (by omega))
  rwa [log_mul hD.ne' hk2.ne'] at h

/-- A testing schedule whose information stays below `(1-delta) log(k+2)`
is not summable after exponentiation. -/
theorem not_summable_information {δ : ℝ} (hδ : δ < 1) (K : ℕ → ℝ)
    (hK : ∀ k, K k ≤ (1-δ)*log ((k:ℝ)+2)) :
    ¬Summable (fun k => exp (-(K k+log 2)/(1-δ))) := by
  intro h
  have hε : 0 < 1-δ := by linarith
  have hc : exp (-log 2/(1-δ)) ≠ 0 := (exp_pos _).ne'
  have hh : Summable (fun k : ℕ => exp (-log 2/(1-δ))*(1/((k:ℝ)+2))) := by
    apply h.of_nonneg_of_le (fun k => by positivity)
    intro k
    have hx : 0 < (k:ℝ)+2 := by positivity
    have he : exp (-log 2/(1-δ))*(1/((k:ℝ)+2)) =
        exp (-log 2/(1-δ)+-log ((k:ℝ)+2)) := by
      rw [exp_add, exp_neg (log _), exp_log hx, one_div]
    rw [he]
    apply exp_le_exp.mpr
    have hd : -(K k+log 2)/(1-δ) = -log 2/(1-δ)+-(K k/(1-δ)) := by ring
    rw [hd]
    have hK' : K k/(1-δ) ≤ log ((k:ℝ)+2) := by
      rw [div_le_iff₀ hε]; linarith [hK k]
    linarith
  have hh' := (summable_mul_left_iff hc).mp hh
  have hh'' : Summable (fun k : ℕ => 1/((k+2:ℕ):ℝ)) := by
    simpa only [Nat.cast_add,Nat.cast_ofNat] using hh'
  exact Real.not_summable_one_div_natCast ((summable_nat_add_iff 2).mp hh'')

/-- Eventually the budget is large and its information dominates the
iterated logarithm with the target coefficient. -/
theorem schedule_eventually {ρ δ : ℝ} (hρ : 0 < ρ) (hρ4 : ρ ≤ 1/4) (hδ : δ < 1) (M : ℕ) :
    ∀ᶠ k in atTop, max M 3 ≤ scheduleBudget ρ δ k ∧
      27*(1-δ)*ρ*log (log (scheduleBudget ρ δ k:ℝ)) ≤
        64*(scheduleBudget ρ δ k:ℝ)*(meanShift ρ k)^2 := by
  set D := |log (16*(1-δ)*baseVar ρ/ρ^2)|+5 with hDdef
  have hl : Tendsto (fun k : ℕ => log ((k:ℝ)+2)) atTop atTop :=
    tendsto_log_atTop.comp (tendsto_atTop_add_const_right atTop (2:ℝ) tendsto_natCast_atTop_atTop)
  filter_upwards [(scheduleBudget_tendsto hρ hρ4 hδ).eventually (eventually_ge_atTop (max M 27)),
    hl.eventually (eventually_ge_atTop (5*log D))] with k hN hL
  have hN27 : 27 ≤ scheduleBudget ρ δ k := le_of_max_le_right hN
  refine ⟨le_trans (max_le_max le_rfl (by norm_num)) hN, ?_⟩
  set n : ℝ := (scheduleBudget ρ δ k:ℝ) with hndef
  set L := log ((k:ℝ)+2) with hLdef
  set a := meanShift ρ k with hadef
  have hn27 : (27:ℝ) ≤ n := by rw [hndef]; exact_mod_cast hN27
  have hD5 : (5:ℝ) ≤ D := by rw [hDdef]; linarith [abs_nonneg (log (16*(1-δ)*baseVar ρ/ρ^2))]
  have hlD : 0 ≤ log D := log_nonneg (by linarith)
  have hX := scheduleBudget_loglog_upper hρ hρ4 hδ k (by omega)
  rw [← hDdef, ← hndef, ← hLdef] at hX
  have hfloor := scheduleBudget_lower (δ := δ) hρ hρ4 k
  rw [← hndef, ← hLdef, ← hadef] at hfloor
  have hV := baseVar_lower hρ hρ4
  have hε : 0 < 1-δ := by linarith
  have hερ : 0 < (1-δ)*ρ := mul_pos hε hρ
  have hL0 : 0 ≤ L := by rw [hLdef]; exact shifted_log_nonneg k
  have h1 : (1-δ)*ρ*(39/64)*L ≤ (n+1)*a^2 := by
    have := mul_le_mul_of_nonneg_left hV (mul_nonneg hε.le hL0)
    nlinarith
  have hA : 27*(log D+L)*(n+1) ≤ 39*L*n := by nlinarith
  have hB : 27*((1-δ)*ρ)*(log D+L)*(n+1) ≤ 64*n*a^2*(n+1) := by
    have h2 := mul_le_mul_of_nonneg_left hA hερ.le
    have h3 := mul_le_mul_of_nonneg_left h1 (show (0:ℝ) ≤ 64*n by linarith)
    nlinarith
  have hC : 27*((1-δ)*ρ)*(log D+L) ≤ 64*n*a^2 :=
    le_of_mul_le_mul_right hB (by linarith)
  have hX' := mul_le_mul_of_nonneg_left hX (show (0:ℝ) ≤ 27*((1-δ)*ρ) by positivity)
  nlinarith

end ThresholdHC.BernoulliTimeUniform
