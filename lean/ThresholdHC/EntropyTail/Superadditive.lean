import ThresholdHC.EntropyTail.Entropy

/-! The cost entropy is homogeneous of degree one, superadditive and coordinatewise
increasing on nonnegative vectors, so it dominates nonnegative mixtures. The
coordinate step is the two-term log-sum inequality. -/
noncomputable section
namespace ThresholdHC.EntropyTail

theorem costEntropy_nonneg {n : ℕ} (a : Fin n → ℝ) (ha : ∀ j, 0 ≤ a j) :
    0 ≤ costEntropy a :=
  (Finset.sum_nonneg fun j _ => ha j).trans (sum_le_costEntropy a ha)

/-- Two-term log-sum inequality, from concavity of the logarithm. -/
theorem logsum_two {x₁ x₂ X₁ X₂ : ℝ} (hx₁ : 0 ≤ x₁) (hx₂ : 0 ≤ x₂) (h₁ : x₁ ≤ X₁)
    (h₂ : x₂ ≤ X₂) :
    x₁ * Real.log (X₁ / x₁) + x₂ * Real.log (X₂ / x₂) ≤
      (x₁ + x₂) * Real.log ((X₁ + X₂) / (x₁ + x₂)) := by
  rcases hx₁.eq_or_lt with h | hp₁
  · rw [← h, zero_mul, zero_add, zero_add]
    rcases hx₂.eq_or_lt with h' | hp₂
    · rw [← h', zero_mul, zero_mul]
    · refine mul_le_mul_of_nonneg_left (Real.log_le_log (div_pos (by linarith) hp₂) ?_) hx₂
      exact div_le_div_of_nonneg_right (by linarith) hx₂
  rcases hx₂.eq_or_lt with h | hp₂
  · rw [← h, zero_mul, add_zero, add_zero]
    refine mul_le_mul_of_nonneg_left (Real.log_le_log (div_pos (by linarith) hp₁) ?_) hx₁
    exact div_le_div_of_nonneg_right (by linarith) hx₁
  have hX₁ : 0 < X₁ := lt_of_lt_of_le hp₁ h₁
  have hX₂ : 0 < X₂ := lt_of_lt_of_le hp₂ h₂
  have hs : 0 < x₁ + x₂ := add_pos hp₁ hp₂
  have hc := strictConcaveOn_log_Ioi.concaveOn.2 (Set.mem_Ioi.2 (div_pos hX₁ hp₁))
    (Set.mem_Ioi.2 (div_pos hX₂ hp₂)) (div_nonneg hx₁ hs.le) (div_nonneg hx₂ hs.le)
    (by rw [← add_div, div_self hs.ne'])
  simp only [smul_eq_mul] at hc
  have harg : x₁ / (x₁ + x₂) * (X₁ / x₁) + x₂ / (x₁ + x₂) * (X₂ / x₂) =
      (X₁ + X₂) / (x₁ + x₂) := by
    rw [div_mul_div_comm, div_mul_div_comm, mul_comm x₁ X₁, mul_comm x₂ X₂,
      mul_div_mul_right _ _ hp₁.ne', mul_div_mul_right _ _ hp₂.ne', ← add_div]
  rw [harg] at hc
  have hmul := mul_le_mul_of_nonneg_left hc hs.le
  have hsplit : (x₁ + x₂) * (x₁ / (x₁ + x₂) * Real.log (X₁ / x₁) +
      x₂ / (x₁ + x₂) * Real.log (X₂ / x₂)) =
      x₁ * Real.log (X₁ / x₁) + x₂ * Real.log (X₂ / x₂) := by
    field_simp
  linarith

/-- `G(a) + G(b) ≤ G(a+b)` on nonnegative vectors. -/
theorem costEntropy_add {n : ℕ} (a b : Fin n → ℝ) (ha : ∀ j, 0 ≤ a j) (hb : ∀ j, 0 ≤ b j) :
    costEntropy a + costEntropy b ≤ costEntropy (a + b) := by
  unfold costEntropy
  simp only [Pi.add_apply]
  have hsum : ∑ i, (a i + b i) = ∑ i, a i + ∑ i, b i := Finset.sum_add_distrib
  rw [hsum]
  have key : ∀ j, a j * Real.log ((∑ i, a i) / a j) + b j * Real.log ((∑ i, b i) / b j) ≤
      (a j + b j) * Real.log ((∑ i, a i + ∑ i, b i) / (a j + b j)) := fun j =>
    logsum_two (ha j) (hb j) (Finset.single_le_sum (fun i _ => ha i) (Finset.mem_univ j))
      (Finset.single_le_sum (fun i _ => hb i) (Finset.mem_univ j))
  have hle := Finset.sum_le_sum fun j (_ : j ∈ Finset.univ) => key j
  rw [Finset.sum_add_distrib] at hle
  linarith

/-- `G(c a) = c G(a)` for `c ≥ 0`. -/
theorem costEntropy_smul {n : ℕ} (a : Fin n → ℝ) {c : ℝ} (hc : 0 ≤ c) :
    costEntropy (c • a) = c * costEntropy a := by
  unfold costEntropy
  simp only [Pi.smul_apply, smul_eq_mul]
  rcases hc.eq_or_lt with h | hc
  · simp [← h]
  · have hS : ∑ i, c * a i = c * ∑ i, a i := (Finset.mul_sum _ _ _).symm
    have hT : ∀ j, c * a j * Real.log ((∑ i, c * a i) / (c * a j)) =
        c * (a j * Real.log ((∑ i, a i) / a j)) := by
      intro j
      rw [hS, mul_div_mul_left _ _ hc.ne']
      ring
    rw [Finset.sum_congr rfl fun j _ => hT j, hS, ← Finset.mul_sum, mul_add]

/-- `G` is coordinatewise increasing on nonnegative vectors. -/
theorem costEntropy_mono {n : ℕ} {a b : Fin n → ℝ} (ha : ∀ j, 0 ≤ a j) (hab : ∀ j, a j ≤ b j) :
    costEntropy a ≤ costEntropy b := by
  have hd : ∀ j, 0 ≤ (b - a) j := fun j => by simp [hab j]
  have h := costEntropy_add a (b - a) ha hd
  rw [add_sub_cancel] at h
  linarith [costEntropy_nonneg (b - a) hd]

/-- A nonnegative mixture dominates the mixture of entropies. -/
theorem sum_smul_costEntropy_le {ι : Type*} (s : Finset ι) {n : ℕ} (w : ι → ℝ)
    (a : ι → Fin n → ℝ) (hw : ∀ k ∈ s, 0 ≤ w k) (ha : ∀ k ∈ s, ∀ j, 0 ≤ a k j) :
    ∑ k ∈ s, w k * costEntropy (a k) ≤ costEntropy (∑ k ∈ s, w k • a k) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [costEntropy]
  | @insert k s hk ih =>
    rw [Finset.sum_insert hk, Finset.sum_insert hk]
    have hk' := hw k (Finset.mem_insert_self k s)
    have ih' := ih (fun i hi => hw i (Finset.mem_insert_of_mem hi))
      (fun i hi => ha i (Finset.mem_insert_of_mem hi))
    have hrest : ∀ j, 0 ≤ (∑ i ∈ s, w i • a i) j := fun j => by
      rw [Finset.sum_apply]
      exact Finset.sum_nonneg fun i hi => mul_nonneg (hw i (Finset.mem_insert_of_mem hi))
        (ha i (Finset.mem_insert_of_mem hi) j)
    calc w k * costEntropy (a k) + ∑ i ∈ s, w i * costEntropy (a i)
        ≤ costEntropy (w k • a k) + costEntropy (∑ i ∈ s, w i • a i) := by
          rw [costEntropy_smul _ hk']
          linarith
      _ ≤ costEntropy (w k • a k + ∑ i ∈ s, w i • a i) :=
          costEntropy_add _ _ (fun j => mul_nonneg hk' (ha k (Finset.mem_insert_self k s) j))
            hrest

end ThresholdHC.EntropyTail
