import ThresholdHC.RepeatedCheck.Row

/-! The kernel certificate for display (29) of
`research/2026-10-30-confidence-transfer/ANYTIME.md`: the survivor weight of
row `512` is the explicit 1024-bit integer `survivorTotal`, checked by kernel
evaluation of `survivorRow 512` (one pass per row, pure kernel reduction). The
repeated-check probability `1 - survivorTotal / 4^512` then lies strictly
between `0.4280910097010513` and `0.4280910097010514`; it is
`0.4280910097010513377…`, below the paper's floating-point display
`0.42809100970105135`. -/

namespace ThresholdHC.RepeatedCheck

/-- The total survivor weight after `512` steps. -/
def survivorTotal : ℕ :=
  102811686562645883769230177379917934569512580375660239789514999499376877266927083603187381836380958331762078348042904563155347083655670761638074156975414013748915934930832012094353637785070816108506429315684819564532872083164780140588802962893568356280890542994041302867046729122210377189392337047820112374555

theorem survivorRow_sum_512 : (survivorRow 512).sum = survivorTotal := by
  decide +kernel

theorem survivorTotal_lower_nat :
    survivorTotal * 10 ^ 16 < 5719089902989487 * 4 ^ 512 := by
  decide +kernel

theorem survivorTotal_upper_nat :
    5719089902989486 * 4 ^ 512 < survivorTotal * 10 ^ 16 := by
  decide +kernel

theorem survivorTotal_lower :
    (4280910097010513 : ℝ) / 10 ^ 16 < 1 - (survivorTotal : ℝ) / 4 ^ 512 := by
  have hr := (Nat.cast_lt (α := ℝ)).mpr survivorTotal_lower_nat
  simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] at hr
  have hD : (0 : ℝ) < 4 ^ 512 := by positivity
  have key : (survivorTotal : ℝ) / 4 ^ 512 < 5719089902989487 / 10 ^ 16 := by
    rw [div_lt_div_iff₀ hD (by norm_num)]
    exact hr
  have he : (4280910097010513 : ℝ) / 10 ^ 16 = 1 - 5719089902989487 / 10 ^ 16 := by
    norm_num
  rw [he]
  exact sub_lt_sub_left key 1

theorem survivorTotal_upper :
    1 - (survivorTotal : ℝ) / 4 ^ 512 < (4280910097010514 : ℝ) / 10 ^ 16 := by
  have hr := (Nat.cast_lt (α := ℝ)).mpr survivorTotal_upper_nat
  simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] at hr
  have hD : (0 : ℝ) < 4 ^ 512 := by positivity
  have key : (5719089902989486 : ℝ) / 10 ^ 16 < (survivorTotal : ℝ) / 4 ^ 512 := by
    rw [div_lt_div_iff₀ (by norm_num) hD]
    exact hr
  have he : (4280910097010514 : ℝ) / 10 ^ 16 = 1 - 5719089902989486 / 10 ^ 16 := by
    norm_num
  rw [he]
  exact sub_lt_sub_left key 1

end ThresholdHC.RepeatedCheck
