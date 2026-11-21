import ThresholdHC.ReservoirTermination.Specification

/-!
Finite first-passage algebra of the stopped walk, with no measure theory.

`walkOp r` is one step of the walk that moves up with probability `r` and is absorbed
once its value equals one, acting on functions of the history. `walkExp r n g` is the
expectation of `g` at the history after `n` steps. Two exact identities, for the gap
`1 - walk` and its square, show that the gap is summable when `r > 1/2`, which gives
the expected work `1/(2r-1)` and absorption. A likelihood-ratio tilt with ratio
`(1-r)/r` per upward step transfers the law to the parameter `1-r`, where the walk
survives forever with probability `1 - (1-r)/r`.
-/

noncomputable section
open Filter
open scoped Topology
namespace ThresholdHC.ReservoirTermination

/-- One step of the walk, absorbed at one, acting on functions of the history. -/
def walkOp (r : ℝ) (g : List Bool → ℝ) (xs : List Bool) : ℝ :=
  if walkValue xs = 1 then g xs else r * g (xs ++ [true]) + (1 - r) * g (xs ++ [false])

/-- Expectation of `g` at the history after `n` steps from the empty history. -/
def walkExp (r : ℝ) (n : ℕ) (g : List Bool → ℝ) : ℝ := (walkOp r)^[n] g []

/-- Indicator that the walk has not stopped. -/
def walkAlive (xs : List Bool) : ℝ := if walkValue xs = 1 then 0 else 1

theorem walkValue_nil : walkValue [] = 0 := by simp [walkValue]

theorem walkValue_append_true (xs : List Bool) :
    walkValue (xs ++ [true]) = walkValue xs + 1 := by
  simp [walkValue, List.count_append]
  ring

theorem walkValue_append_false (xs : List Bool) :
    walkValue (xs ++ [false]) = walkValue xs - 1 := by
  simp [walkValue, List.count_append]
  ring

theorem neg_length_le_walkValue (xs : List Bool) : -(xs.length : ℤ) ≤ walkValue xs := by
  have h : xs.count false ≤ xs.length := List.count_le_length
  unfold walkValue
  omega

theorem walkExp_zero (r : ℝ) (g : List Bool → ℝ) : walkExp r 0 g = g [] := rfl

theorem walkExp_succ (r : ℝ) (n : ℕ) (g : List Bool → ℝ) :
    walkExp r (n+1) g = walkExp r n (walkOp r g) := by
  simp only [walkExp, Function.iterate_succ_apply]

theorem iterate_walkOp_linear (r a b : ℝ) (n : ℕ) : ∀ (g h : List Bool → ℝ),
    (walkOp r)^[n] (fun xs => a * g xs + b * h xs) =
      fun xs => a * (walkOp r)^[n] g xs + b * (walkOp r)^[n] h xs := by
  induction n with
  | zero => intro g h; rfl
  | succ n ih =>
    intro g h
    have hop : walkOp r (fun xs => a * g xs + b * h xs) =
        fun xs => a * walkOp r g xs + b * walkOp r h xs := by
      funext xs
      unfold walkOp
      split_ifs <;> ring
    rw [Function.iterate_succ_apply, hop, ih, Function.iterate_succ_apply,
      Function.iterate_succ_apply]

theorem walkExp_linear (r a b : ℝ) (n : ℕ) (g h f : List Bool → ℝ)
    (hf : ∀ xs, f xs = a * g xs + b * h xs) :
    walkExp r n f = a * walkExp r n g + b * walkExp r n h := by
  rw [show f = fun xs => a * g xs + b * h xs from funext hf]
  unfold walkExp
  rw [iterate_walkOp_linear]

theorem iterate_walkOp_const (r c : ℝ) (n : ℕ) :
    (walkOp r)^[n] (fun _ => c) = fun _ => c := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hop : walkOp r (fun _ => c) = fun _ => c := by
      funext xs
      unfold walkOp
      split_ifs <;> ring
    rw [Function.iterate_succ_apply, hop, ih]

theorem walkExp_const (r c : ℝ) (n : ℕ) : walkExp r n (fun _ => c) = c := by
  unfold walkExp
  rw [iterate_walkOp_const]

/-- Monotonicity on histories whose walk value is at most one, the only histories
the walk reaches. -/
theorem iterate_walkOp_mono (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (n : ℕ) :
    ∀ (g h : List Bool → ℝ), (∀ xs, walkValue xs ≤ 1 → g xs ≤ h xs) →
      ∀ xs, walkValue xs ≤ 1 → (walkOp r)^[n] g xs ≤ (walkOp r)^[n] h xs := by
  induction n with
  | zero => intro g h hgh; exact hgh
  | succ n ih =>
    intro g h hgh
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply]
    apply ih
    intro xs hxs
    unfold walkOp
    split_ifs with hv
    · exact hgh xs hxs
    · have h0 : walkValue xs ≤ 0 := by omega
      have ht := hgh (xs ++ [true]) (by rw [walkValue_append_true]; omega)
      have hf := hgh (xs ++ [false]) (by rw [walkValue_append_false]; omega)
      have h1r : 0 ≤ 1 - r := by linarith
      nlinarith [mul_le_mul_of_nonneg_left ht hr0, mul_le_mul_of_nonneg_left hf h1r]

theorem walkExp_mono (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (n : ℕ) (g h : List Bool → ℝ)
    (hgh : ∀ xs, walkValue xs ≤ 1 → g xs ≤ h xs) : walkExp r n g ≤ walkExp r n h :=
  iterate_walkOp_mono r hr0 hr1 n g h hgh [] (by simp [walkValue_nil])

theorem walkExp_nonneg (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (n : ℕ) (g : List Bool → ℝ)
    (hg : ∀ xs, walkValue xs ≤ 1 → 0 ≤ g xs) : 0 ≤ walkExp r n g := by
  have h := walkExp_mono r hr0 hr1 n (fun _ => 0) g hg
  rwa [walkExp_const] at h

theorem walkOp_length (r : ℝ) :
    walkOp r (fun xs => (xs.length : ℝ)) = fun xs => (xs.length : ℝ) + walkAlive xs := by
  funext xs
  unfold walkOp walkAlive
  split_ifs
  · ring
  · simp only [List.length_append, List.length_singleton, Nat.cast_add, Nat.cast_one]
    ring

theorem walkOp_gap (r : ℝ) : walkOp r (fun xs => 1 - (walkValue xs : ℝ)) =
    fun xs => (1 - (walkValue xs : ℝ)) - (2*r-1) * walkAlive xs := by
  funext xs
  unfold walkOp walkAlive
  dsimp only
  split_ifs
  · ring
  · rw [walkValue_append_true, walkValue_append_false]
    push_cast
    ring

theorem walkOp_gap_sq (r : ℝ) : walkOp r (fun xs => (1 - (walkValue xs : ℝ))^2) =
    fun xs => (1 - (walkValue xs : ℝ))^2 + walkAlive xs -
      2*(2*r-1) * (1 - (walkValue xs : ℝ)) := by
  funext xs
  unfold walkOp walkAlive
  dsimp only
  split_ifs with h
  · rw [h]
    norm_num
  · rw [walkValue_append_true, walkValue_append_false]
    push_cast
    ring

theorem walkOp_tilt (r : ℝ) (hr0 : r ≠ 0) (hr1 : r ≠ 1) (g : List Bool → ℝ) :
    walkOp r (fun xs => g xs * ((1-r)/r)^(walkValue xs)) =
      fun xs => walkOp (1-r) g xs * ((1-r)/r)^(walkValue xs) := by
  have h1 : 1 - r ≠ 0 := sub_ne_zero.mpr (Ne.symm hr1)
  have hρ : (1-r)/r ≠ 0 := div_ne_zero h1 hr0
  funext xs
  unfold walkOp
  dsimp only
  split_ifs
  · rfl
  · rw [walkValue_append_true, walkValue_append_false, zpow_add₀ hρ, zpow_sub₀ hρ, zpow_one]
    field_simp
    ring

theorem iterate_walkOp_tilt (r : ℝ) (hr0 : r ≠ 0) (hr1 : r ≠ 1) (n : ℕ) :
    ∀ g : List Bool → ℝ,
    (walkOp r)^[n] (fun xs => g xs * ((1-r)/r)^(walkValue xs)) =
      fun xs => (walkOp (1-r))^[n] g xs * ((1-r)/r)^(walkValue xs) := by
  induction n with
  | zero => intro g; rfl
  | succ n ih =>
    intro g
    rw [Function.iterate_succ_apply, walkOp_tilt r hr0 hr1, ih, Function.iterate_succ_apply]

/-- The likelihood-ratio tilt between the parameters `1-r` and `r`. -/
theorem walkExp_tilt (r : ℝ) (hr0 : r ≠ 0) (hr1 : r ≠ 1) (n : ℕ) (g : List Bool → ℝ) :
    walkExp (1-r) n g = walkExp r n (fun xs => g xs * ((1-r)/r)^(walkValue xs)) := by
  unfold walkExp
  rw [iterate_walkOp_tilt r hr0 hr1]
  simp [walkValue_nil]

theorem walkExp_length_succ (r : ℝ) (n : ℕ) :
    walkExp r (n+1) (fun xs => (xs.length : ℝ)) =
      walkExp r n (fun xs => (xs.length : ℝ)) + walkExp r n walkAlive := by
  rw [walkExp_succ, walkOp_length]
  simpa using walkExp_linear r 1 1 n (fun xs => (xs.length : ℝ)) walkAlive
    (fun xs => (xs.length : ℝ) + walkAlive xs) (fun xs => by ring)

theorem walkExp_length_mono (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    Monotone (fun n => walkExp r n (fun xs => (xs.length : ℝ))) := by
  apply monotone_nat_of_le_succ
  intro n
  rw [walkExp_length_succ]
  have := walkExp_nonneg r hr0 hr1 n walkAlive (fun xs _ => by unfold walkAlive; split_ifs <;> norm_num)
  linarith

theorem walkExp_alive_nonneg (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (n : ℕ) :
    0 ≤ walkExp r n walkAlive :=
  walkExp_nonneg r hr0 hr1 n walkAlive (fun xs _ => by unfold walkAlive; split_ifs <;> norm_num)

theorem walkExp_gap_eq (r : ℝ) (n : ℕ) :
    walkExp r n (fun xs => 1 - (walkValue xs : ℝ)) =
      1 - (2*r-1) * walkExp r n (fun xs => (xs.length : ℝ)) := by
  induction n with
  | zero => simp [walkExp_zero, walkValue_nil]
  | succ n ih =>
    rw [walkExp_succ, walkOp_gap, walkExp_linear r 1 (-(2*r-1)) n
      (fun xs => 1 - (walkValue xs : ℝ)) walkAlive
      (fun xs => (1 - (walkValue xs : ℝ)) - (2*r-1) * walkAlive xs) (fun xs => by ring), ih,
      walkExp_length_succ]
    ring

theorem walkExp_gap_sq_eq (r : ℝ) (n : ℕ) :
    walkExp r n (fun xs => (1 - (walkValue xs : ℝ))^2) =
      1 + walkExp r n (fun xs => (xs.length : ℝ)) -
        2*(2*r-1) * ∑ k ∈ Finset.range n, walkExp r k (fun xs => 1 - (walkValue xs : ℝ)) := by
  induction n with
  | zero => simp [walkExp_zero, walkValue_nil]
  | succ n ih =>
    have hlin : walkExp r n (fun xs => (1 - (walkValue xs : ℝ))^2 + walkAlive xs -
        2*(2*r-1) * (1 - (walkValue xs : ℝ))) =
        walkExp r n (fun xs => (1 - (walkValue xs : ℝ))^2) + walkExp r n walkAlive -
          2*(2*r-1) * walkExp r n (fun xs => 1 - (walkValue xs : ℝ)) := by
      have h1 := walkExp_linear r 1 1 n (fun xs => (1 - (walkValue xs : ℝ))^2) walkAlive
        (fun xs => (1 - (walkValue xs : ℝ))^2 + walkAlive xs) (fun xs => by ring)
      have h2 := walkExp_linear r 1 (-(2*(2*r-1))) n
        (fun xs => (1 - (walkValue xs : ℝ))^2 + walkAlive xs)
        (fun xs => 1 - (walkValue xs : ℝ))
        (fun xs => (1 - (walkValue xs : ℝ))^2 + walkAlive xs -
          2*(2*r-1) * (1 - (walkValue xs : ℝ))) (fun xs => by ring)
      rw [h2, h1]
      ring
    rw [walkExp_succ, walkOp_gap_sq, hlin, ih, walkExp_length_succ, Finset.sum_range_succ]
    ring

/-- The plus-side walk: expected work `1/(2r-1)` and absorption. -/
theorem walk_plus_limits (r : ℝ) (hr : 1/2 < r) (hr1 : r ≤ 1) :
    Tendsto (fun n => walkExp r n (fun xs => (xs.length : ℝ))) atTop (𝓝 (1/(2*r-1))) ∧
    Tendsto (fun n => walkExp r n walkAlive) atTop (𝓝 0) := by
  have hr0 : 0 ≤ r := by linarith
  have hc : 0 < 2*r-1 := by linarith
  set W := fun n => walkExp r n (fun xs => (xs.length : ℝ)) with hW
  set U := fun n => walkExp r n (fun xs => 1 - (walkValue xs : ℝ)) with hU
  have hUnn (n : ℕ) : 0 ≤ U n :=
    walkExp_nonneg r hr0 hr1 n _ (fun xs hxs => by
      have : (walkValue xs : ℝ) ≤ 1 := by exact_mod_cast hxs
      linarith)
  have hWle (n : ℕ) : W n ≤ 1/(2*r-1) := by
    have h := hUnn n
    simp only [hU, walkExp_gap_eq] at h
    rw [le_div_iff₀ hc]
    linarith
  have hsum (n : ℕ) : ∑ k ∈ Finset.range n, U k ≤ (1 + 1/(2*r-1)) / (2*(2*r-1)) := by
    have hY := walkExp_nonneg r hr0 hr1 n (fun xs => (1 - (walkValue xs : ℝ))^2)
      (fun xs _ => sq_nonneg _)
    rw [walkExp_gap_sq_eq] at hY
    rw [le_div_iff₀ (by linarith)]
    have := hWle n
    simp only [hU, hW] at this ⊢
    linarith
  have hUlim : Tendsto U atTop (𝓝 0) :=
    (summable_of_sum_range_le hUnn hsum).tendsto_atTop_zero
  constructor
  · have hWeq : W = fun n => (1 - U n) / (2*r-1) := by
      funext n
      simp only [hU, hW, walkExp_gap_eq]
      field_simp
      ring
    rw [hWeq]
    have := (tendsto_const_nhds (x := (1:ℝ))).sub hUlim |>.div_const (2*r-1)
    simpa using this
  · apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hUlim
    · intro n
      exact walkExp_alive_nonneg r hr0 hr1 n
    · intro n
      apply walkExp_mono r hr0 hr1 n
      intro xs hxs
      unfold walkAlive
      split_ifs with h
      · simp [h]
      · have : walkValue xs ≤ 0 := by omega
        have : (walkValue xs : ℝ) ≤ 0 := by exact_mod_cast this
        linarith

/-- The minus-side walk survives with probability `1 - (1-r)/r` and has unbounded
expected work. -/
theorem walk_minus_limits (r : ℝ) (hr : 1/2 < r) (hr1 : r < 1) :
    Tendsto (fun n => walkExp (1-r) n walkAlive) atTop (𝓝 (1 - (1-r)/r)) ∧
    ∀ n : ℕ, (n : ℝ) * (1 - (1-r)/r) ≤ walkExp (1-r) n (fun xs => (xs.length : ℝ)) := by
  have hr0 : r ≠ 0 := by intro h; linarith
  have hr1' : r ≠ 1 := ne_of_lt hr1
  have hρ0 : 0 < (1-r)/r := div_pos (by linarith) (by linarith)
  have hA (n : ℕ) : walkExp (1-r) n walkAlive = 1 - (1-r)/r + (1-r)/r * walkExp r n walkAlive := by
    have h1 := walkExp_linear (1-r) 1 (-1) n (fun _ => 1) walkAlive (fun xs => 1 - walkAlive xs)
      (fun xs => by ring)
    rw [walkExp_const, walkExp_tilt r hr0 hr1'] at h1
    have h2 := walkExp_linear r ((1-r)/r) (-((1-r)/r)) n (fun _ => 1) walkAlive
      (fun xs => (1 - walkAlive xs) * ((1-r)/r)^(walkValue xs)) (fun xs => by
        unfold walkAlive
        split_ifs with h
        · rw [h, zpow_one]; ring
        · ring)
    rw [walkExp_const] at h2
    linarith
  constructor
  · have hlim := (walk_plus_limits r hr hr1.le).2
    have := (tendsto_const_nhds (x := 1 - (1-r)/r)).add (hlim.const_mul ((1-r)/r))
    simp only [mul_zero, add_zero] at this
    exact this.congr (fun n => (hA n).symm)
  · intro n
    induction n with
    | zero => simp [walkExp_zero]
    | succ n ih =>
      rw [walkExp_length_succ, hA n]
      have := walkExp_alive_nonneg r (by linarith) hr1.le n
      push_cast
      nlinarith

end ThresholdHC.ReservoirTermination
