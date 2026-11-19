import ThresholdHC.Proofs.Tier2.ClassifierProbability

/-! The majority votes after `n` and `2*n` flips change sign with probability at
most one half, for every coin and every even `n`.

With `N₁` the number of successes among the first `n` flips and `N₂` among the
next `n`, the votes are `m < N₁` and `2*m < N₁ + N₂` for `n = 2*m`. They differ
only if `m < N₁` and `N₂ < m`, or `N₁ ≤ m` and `m < N₂`. The two counts are
independent and have the same law, so with `a = P(m < N₁)` the probability is at
most `a*(1 - a) + (1 - a)*a ≤ 1/2`. -/
noncomputable section
namespace ThresholdHC.UpperSign
open MeasureTheory ProbabilityTheory Finset ThresholdHC.Tier2

/-- The number of successes among the `n` flips starting at `s`. -/
def successes (s n : ℕ) (ω : ℕ → Bool) : ℕ := ∑ i ∈ range n, if ω (s + i) then 1 else 0

theorem measurable_successes (s n : ℕ) : Measurable (successes s n) := by
  unfold successes
  apply Finset.measurable_sum
  intro i _
  exact Measurable.ite (measurableSet_eq_fun (measurable_pi_apply (s + i)) measurable_const)
    measurable_const measurable_const

/-- The shift by `s` flips preserves the tape law. -/
theorem shift_measurePreserving (s : ℕ) (p : unitInterval) :
    MeasurePreserving (fun ω : ℕ → Bool => fun i => ω (s + i)) (tapeMeasure p) (tapeMeasure p) := by
  refine ⟨by fun_prop, ?_⟩
  exact Measure.map_infinitePi_infinitePi_of_inj (fun i j h => by simpa using h)

theorem successes_shift (s n : ℕ) (ω : ℕ → Bool) :
    successes s n ω = successes 0 n (fun i => ω (s + i)) := by
  simp [successes]

/-- The two blocks of `n` flips are independent. -/
theorem successes_indep (n : ℕ) (p : unitInterval) :
    IndepFun (successes 0 n) (successes n n) (tapeMeasure p) := by
  have hco : iIndepFun (fun i (ω : ℕ → Bool) => ω i) (tapeMeasure p) :=
    iIndepFun_infinitePi (X := fun _ b => b) (fun _ => measurable_id)
  have hdis : Disjoint (range n) (Finset.Ico n (n + n)) := by
    rw [Finset.disjoint_left]
    intro a ha hb
    simp only [mem_range, Finset.mem_Ico] at ha hb
    omega
  have hind := hco.indepFun_finset (range n) (Finset.Ico n (n + n)) hdis (fun _ => measurable_pi_apply _)
  let φ : (range n → Bool) → ℕ := fun x => ∑ i : range n, if x i then 1 else 0
  let ψ : (Finset.Ico n (n + n) → Bool) → ℕ := fun x => ∑ i : Finset.Ico n (n + n), if x i then 1 else 0
  have hφ : Measurable φ := measurable_of_finite φ
  have hψ : Measurable ψ := measurable_of_finite ψ
  have h := hind.comp hφ hψ
  have e1 : successes 0 n = φ ∘ (fun ω (i : range n) => ω i) := by
    funext ω
    simp only [successes, zero_add, Function.comp, φ]
    exact (Finset.sum_coe_sort (range n) (fun i => if ω i then 1 else 0)).symm
  have e2 : successes n n = ψ ∘ (fun ω (i : Finset.Ico n (n + n)) => ω i) := by
    funext ω
    simp only [successes, Function.comp, ψ]
    rw [Finset.sum_coe_sort (Finset.Ico n (n + n)) (fun i => if ω i then 1 else 0),
      Finset.sum_Ico_eq_sum_range]
    simp
  rw [e1, e2]
  exact h

/-- The second block has the law of the first. -/
theorem successes_law (n : ℕ) (p : unitInterval) (A : Set ℕ) :
    (tapeMeasure p).real (successes n n ⁻¹' A) = (tapeMeasure p).real (successes 0 n ⁻¹' A) := by
  have hm := shift_measurePreserving n p
  have hs : successes n n ⁻¹' A = (fun ω : ℕ → Bool => fun i => ω (n + i)) ⁻¹' (successes 0 n ⁻¹' A) := by
    ext ω
    simp only [Set.mem_preimage]
    rw [successes_shift]
  rw [hs, measureReal_def, measureReal_def,
    hm.measure_preimage (measurable_successes 0 n ((Set.to_countable A).measurableSet)).nullMeasurableSet]

/-- The sign-change bound for the counts. -/
theorem count_signChange_le (m : ℕ) (p : unitInterval) :
    (tapeMeasure p).real {ω | (m < successes 0 (2 * m) ω ∧ successes (2 * m) (2 * m) ω < m) ∨
      (successes 0 (2 * m) ω ≤ m ∧ m < successes (2 * m) (2 * m) ω)} ≤ 1 / 2 := by
  set μ := tapeMeasure p
  set N₁ := successes 0 (2 * m)
  set N₂ := successes (2 * m) (2 * m)
  have hind : IndepFun N₁ N₂ μ := by
    have := successes_indep (2 * m) p
    simpa [N₁, N₂] using this
  have hmeas : ∀ A : Set ℕ, MeasurableSet A := fun A => (Set.to_countable A).measurableSet
  have hmul : ∀ A B : Set ℕ, μ.real (N₁ ⁻¹' A ∩ N₂ ⁻¹' B) = μ.real (N₁ ⁻¹' A) * μ.real (N₂ ⁻¹' B) := by
    intro A B
    rw [measureReal_def, measureReal_def, measureReal_def,
      hind.measure_inter_preimage_eq_mul A B (hmeas A) (hmeas B), ENNReal.toReal_mul]
  have hlaw : ∀ A : Set ℕ, μ.real (N₂ ⁻¹' A) = μ.real (N₁ ⁻¹' A) := fun A =>
    successes_law (2 * m) p A
  set a := μ.real (N₁ ⁻¹' {k | m < k})
  have hcompl : μ.real (N₁ ⁻¹' {k | k ≤ m}) = 1 - a := by
    have h := measureReal_compl (μ := μ) ((measurable_successes 0 (2 * m)) (hmeas {k | m < k}))
    have he : (N₁ ⁻¹' {k | m < k})ᶜ = N₁ ⁻¹' {k | k ≤ m} := by
      ext ω
      simp
    rw [he] at h
    simp only [probReal_univ] at h
    exact h
  have hlow : μ.real (N₁ ⁻¹' {k | k < m}) ≤ 1 - a := by
    rw [← hcompl]
    refine measureReal_mono ?_ (measure_ne_top _ _)
    intro ω hω
    simp only [Set.mem_preimage, Set.mem_ofPred_eq] at hω ⊢
    omega
  have hset : {ω | (m < N₁ ω ∧ N₂ ω < m) ∨ (N₁ ω ≤ m ∧ m < N₂ ω)} =
      (N₁ ⁻¹' {k | m < k} ∩ N₂ ⁻¹' {k | k < m}) ∪ (N₁ ⁻¹' {k | k ≤ m} ∩ N₂ ⁻¹' {k | m < k}) := by
    ext ω
    simp
  rw [hset]
  have ha0 : 0 ≤ a := measureReal_nonneg
  have ha1 : a ≤ 1 := measureReal_le_one
  calc
    _ ≤ μ.real (N₁ ⁻¹' {k | m < k} ∩ N₂ ⁻¹' {k | k < m}) +
        μ.real (N₁ ⁻¹' {k | k ≤ m} ∩ N₂ ⁻¹' {k | m < k}) := measureReal_union_le _ _
    _ = a * μ.real (N₁ ⁻¹' {k | k < m}) + (1 - a) * a := by
      rw [hmul, hmul, hlaw, hlaw, hcompl]
    _ ≤ a * (1 - a) + (1 - a) * a := by gcongr
    _ ≤ 1 / 2 := by nlinarith [sq_nonneg (a - 1 / 2)]

end ThresholdHC.UpperSign
