import ThresholdHC.FiniteBayesAllocation.Kernel

/-! The evidence-weighted posterior-variance step and the word enumeration. For nonnegative
weights `a_k`, `Σ a_k (Z - t_k)^2 = A Z^2 - 2 B Z + C` with the moments
`A, B, C`; its minimum over `Z` is `(A C - B^2)/A`, attained at the posterior
mean `B/A`. A word that passed the kernel check therefore has an
evidence-weighted posterior variance between its floor and ceiling terms. Sums over the ordered words
`Fin n → Bool` are sums over the list `allWords n`. -/

namespace ThresholdHC.FiniteBayesAllocation

theorem sum_allWords {M : Type*} [AddCommMonoid M] (n : ℕ) (F : List Bool → M) :
    ∑ u : Fin n → Bool, F (List.ofFn u) = ((allWords n).map F).sum := by
  induction n generalizing F with
  | zero =>
    rw [Fintype.sum_unique]
    simp [allWords]
  | succ n ih =>
    rw [← (Fin.consEquiv (fun _ : Fin (n + 1) => Bool)).sum_comp, Fintype.sum_prod_type,
      Fintype.sum_bool]
    simp only [Fin.consEquiv_apply, List.ofFn_succ, Fin.cons_zero, Fin.cons_succ]
    rw [ih (fun xs => F (true :: xs)), ih (fun xs => F (false :: xs))]
    simp only [allWords, List.map_append, List.map_map, List.sum_append, Function.comp_def]
    exact add_comm _ _

theorem statsOf_eq {J K : ℕ} (C : Code J K) (cs : List (ℕ × ℕ)) :
    statsOf C cs = (∑ k, wordNat C k cs, ∑ k, wordNat C k cs * C.tt k,
      ∑ k, wordNat C k cs * C.tt k * C.tt k) := by
  simp only [statsOf, List.map_ofFn, List.sum_ofFn, Function.comp_def]

theorem quad_identity {K : ℕ} (a t : Fin K → ℝ) (Z : ℝ) :
    ∑ k, a k * (Z - t k)^2 =
      (∑ k, a k) * Z^2 - 2 * (∑ k, a k * t k) * Z + ∑ k, a k * t k * t k := by
  rw [Finset.sum_mul, Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k _
  ring

/-- Posterior mean of a word, `B / (16 A)`. -/
noncomputable def postMean {J K : ℕ} (C : Code J K) (cs : List (ℕ × ℕ)) : ℝ :=
  ((statsOf C cs).2.1 : ℝ) / (16 * ((statsOf C cs).1 : ℝ))

private theorem weighted_sum {J K : ℕ} (C : Code J K) (cs : List (ℕ × ℕ)) (hden : 0 < C.den) (Y : ℝ) :
    ∑ k, (wordNat C k cs : ℝ) / ((C.den : ℝ) * 32 ^ 8) ^ 8 * (Y - (C.tt k : ℝ) / 16)^2 =
      (((statsOf C cs).1 : ℝ) * (16 * Y)^2 - 2 * ((statsOf C cs).2.1 : ℝ) * (16 * Y) +
        ((statsOf C cs).2.2 : ℝ)) / (scaleOf C : ℝ) := by
  rw [statsOf_eq]
  push_cast
  rw [← quad_identity, scaleOf, Finset.sum_div]
  push_cast
  apply Finset.sum_congr rfl
  intro k _
  have hd : (0 : ℝ) < C.den := by exact_mod_cast hden
  field_simp
  ring

/-- A checked word: its floor term is below the weighted squared error of any
estimate `Y`. -/
theorem word_lower {J K : ℕ} (C : Code J K) (cs : List (ℕ × ℕ))
    (hok : wordOK (scaleOf C) (statsOf C cs) = true) (hden : 0 < C.den) (Y : ℝ) :
    (lowerTerm (scaleOf C) (statsOf C cs) : ℝ) / prec ≤
      ∑ k, (wordNat C k cs : ℝ) / ((C.den : ℝ) * 32 ^ 8) ^ 8 * (Y - (C.tt k : ℝ) / 16)^2 := by
  obtain ⟨hA, hlo, -⟩ := wordOK_spec hok
  have hA' : (0 : ℝ) < ((statsOf C cs).1 : ℝ) := by exact_mod_cast hA
  have hc : (0 : ℝ) < (scaleOf C : ℝ) := by
    have : 0 < scaleOf C := by unfold scaleOf; positivity
    exact_mod_cast this
  have hlo' : ((lowerTerm (scaleOf C) (statsOf C cs) : ℕ) : ℝ) * ((scaleOf C : ℝ) * ((statsOf C cs).1 : ℝ)) +
      (prec : ℝ) * (((statsOf C cs).2.1 : ℝ) * ((statsOf C cs).2.1 : ℝ)) ≤
      (prec : ℝ) * (((statsOf C cs).1 : ℝ) * ((statsOf C cs).2.2 : ℝ)) := by exact_mod_cast hlo
  rw [weighted_sum C cs hden]
  set A : ℝ := ((statsOf C cs).1 : ℝ)
  set B : ℝ := ((statsOf C cs).2.1 : ℝ)
  set Cc : ℝ := ((statsOf C cs).2.2 : ℝ)
  set c : ℝ := (scaleOf C : ℝ)
  set lt : ℝ := (lowerTerm (scaleOf C) (statsOf C cs) : ℝ)
  set P : ℝ := (prec : ℝ)
  have hP : 0 < P := by simp only [P, prec]; positivity
  set Z := 16 * Y
  have key : 0 ≤ A * (P * (A * Z^2 - 2 * B * Z + Cc) - lt * c) := by
    have e : A * (P * (A * Z^2 - 2 * B * Z + Cc) - lt * c) =
        P * (A * Z - B)^2 + (P * (A * Cc) - (lt * (c * A) + P * (B * B))) := by ring
    rw [e]
    have := sq_nonneg (A * Z - B)
    have h2 : 0 ≤ P * (A * Cc) - (lt * (c * A) + P * (B * B)) := by linarith
    positivity
  have key2 : lt * c ≤ P * (A * Z^2 - 2 * B * Z + Cc) := by
    have := (mul_nonneg_iff_of_pos_left hA').mp key
    linarith
  rw [div_le_div_iff₀ hP hc]
  linarith

/-- A checked word: the posterior mean has weighted squared error below the
ceiling term. -/
theorem word_upper {J K : ℕ} (C : Code J K) (cs : List (ℕ × ℕ))
    (hok : wordOK (scaleOf C) (statsOf C cs) = true) (hden : 0 < C.den) :
    ∑ k, (wordNat C k cs : ℝ) / ((C.den : ℝ) * 32 ^ 8) ^ 8 * (postMean C cs - (C.tt k : ℝ) / 16)^2 ≤
      (upperTerm (scaleOf C) (statsOf C cs) : ℝ) / prec := by
  obtain ⟨hA, -, hhi⟩ := wordOK_spec hok
  have hA' : (0 : ℝ) < ((statsOf C cs).1 : ℝ) := by exact_mod_cast hA
  have hc : (0 : ℝ) < (scaleOf C : ℝ) := by
    have : 0 < scaleOf C := by unfold scaleOf; positivity
    exact_mod_cast this
  have hhi' : (prec : ℝ) * (((statsOf C cs).1 : ℝ) * ((statsOf C cs).2.2 : ℝ)) ≤
      ((upperTerm (scaleOf C) (statsOf C cs) : ℕ) : ℝ) * ((scaleOf C : ℝ) * ((statsOf C cs).1 : ℝ)) +
      (prec : ℝ) * (((statsOf C cs).2.1 : ℝ) * ((statsOf C cs).2.1 : ℝ)) := by exact_mod_cast hhi
  rw [weighted_sum C cs hden]
  unfold postMean
  set A : ℝ := ((statsOf C cs).1 : ℝ)
  set B : ℝ := ((statsOf C cs).2.1 : ℝ)
  set Cc : ℝ := ((statsOf C cs).2.2 : ℝ)
  set c : ℝ := (scaleOf C : ℝ)
  set ut : ℝ := (upperTerm (scaleOf C) (statsOf C cs) : ℝ)
  set P : ℝ := (prec : ℝ)
  have hP : 0 < P := by simp only [P, prec]; positivity
  have e : A * (16 * (B / (16 * A)))^2 - 2 * B * (16 * (B / (16 * A))) + Cc = (A * Cc - B * B) / A := by
    field_simp
    ring
  rw [e, div_div, div_le_div_iff₀ (mul_pos hA' hc) hP]
  nlinarith

end ThresholdHC.FiniteBayesAllocation
