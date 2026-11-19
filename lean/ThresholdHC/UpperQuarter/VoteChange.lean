import ThresholdHC.UpperSign.SignChange

/-! The majority votes after `n` and `2*n` flips change sign with probability
exactly `a*(1 - a) ≤ 1/4`, for every coin and every `n`.

With `N₁` the number of successes among the first `n` flips and `N₂` among the
next `n`, the votes are `n < 2*N₁` and `n < N₁ + N₂`. The two counts are
independent and have the same law, so their joint law is invariant under the
swap of coordinates. The vote change and its swap are disjoint, and together
they are the event that exactly one of `N₁` and `N₂` is above `n/2`, which has
probability `2*a*(1 - a)` with `a = P(n < 2*N₁)`. -/
noncomputable section
namespace ThresholdHC.UpperQuarter
open MeasureTheory ProbabilityTheory Finset ThresholdHC.Tier2 ThresholdHC.UpperSign

/-- The second block of `n` flips has the law of the first. -/
theorem map_successes_shift (n : ℕ) (p : unitInterval) :
    (tapeMeasure p).map (successes n n) = (tapeMeasure p).map (successes 0 n) := by
  have hm := shift_measurePreserving n p
  have he : successes n n = successes 0 n ∘ (fun ω : ℕ → Bool => fun i => ω (n + i)) := by
    funext ω
    exact successes_shift n n ω
  rw [he, ← Measure.map_map (measurable_successes 0 n) hm.measurable, hm.map_eq]

/-- The joint law of the two blocks is the product of one law with itself. -/
theorem map_successes_pair (n : ℕ) (p : unitInterval) :
    (tapeMeasure p).map (fun ω => (successes 0 n ω, successes n n ω)) =
      ((tapeMeasure p).map (successes 0 n)).prod ((tapeMeasure p).map (successes 0 n)) := by
  have hind := successes_indep n p
  rw [(indepFun_iff_map_prod_eq_prod_map_map (measurable_successes 0 n).aemeasurable
    (measurable_successes n n).aemeasurable).1 hind, map_successes_shift]

/-- The vote change of the two blocks has probability at most one quarter. -/
theorem count_voteChange_le (n : ℕ) (p : unitInterval) :
    (tapeMeasure p).real {ω | (n < 2 * successes 0 n ω ∧ successes 0 n ω + successes n n ω ≤ n) ∨
      (2 * successes 0 n ω ≤ n ∧ n < successes 0 n ω + successes n n ω)} ≤ 1 / 4 := by
  set μ := tapeMeasure p
  set ν := μ.map (successes 0 n)
  have : IsProbabilityMeasure ν :=
    (Measure.isProbabilityMeasure_map_iff (measurable_successes 0 n).aemeasurable).2 inferInstance
  set ρ := ν.prod ν
  have hmeasP : ∀ s : Set (ℕ × ℕ), MeasurableSet s := fun s => (Set.to_countable s).measurableSet
  have hmeasN : ∀ s : Set ℕ, MeasurableSet s := fun s => (Set.to_countable s).measurableSet
  set E : Set (ℕ × ℕ) := {q | (n < 2 * q.1 ∧ q.1 + q.2 ≤ n) ∨ (2 * q.1 ≤ n ∧ n < q.1 + q.2)} with hE
  have hpair : Measurable (fun ω => (successes 0 n ω, successes n n ω)) :=
    (measurable_successes 0 n).prodMk (measurable_successes n n)
  have hev : {ω | (n < 2 * successes 0 n ω ∧ successes 0 n ω + successes n n ω ≤ n) ∨
      (2 * successes 0 n ω ≤ n ∧ n < successes 0 n ω + successes n n ω)} =
      (fun ω => (successes 0 n ω, successes n n ω)) ⁻¹' E := by
    ext ω
    simp [hE]
  have hρE : μ.real ((fun ω => (successes 0 n ω, successes n n ω)) ⁻¹' E) = ρ.real E := by
    rw [measureReal_def, measureReal_def, ← Measure.map_apply hpair (hmeasP E), map_successes_pair]
  rw [hev, hρE]
  have hswap : ρ.map Prod.swap = ρ := Measure.prod_swap
  have hsym : ρ.real (Prod.swap ⁻¹' E) = ρ.real E := by
    rw [measureReal_def, measureReal_def, ← Measure.map_apply measurable_swap (hmeasP E), hswap]
  set A : Set ℕ := {j | n < 2 * j} with hA
  have hdisj : Disjoint E (Prod.swap ⁻¹' E) := by
    rw [Set.disjoint_left]
    intro q h1 h2
    simp only [hE, Set.mem_preimage, Prod.fst_swap, Prod.snd_swap, Set.mem_ofPred_eq] at h1 h2
    omega
  have hunion : E ∪ Prod.swap ⁻¹' E = A ×ˢ Aᶜ ∪ Aᶜ ×ˢ A := by
    ext q
    simp only [hE, hA, Set.mem_union, Set.mem_preimage, Prod.fst_swap, Prod.snd_swap,
      Set.mem_ofPred_eq, Set.mem_prod, Set.mem_compl_iff]
    omega
  have hdisj2 : Disjoint (A ×ˢ Aᶜ) (Aᶜ ×ˢ A) := by
    rw [Set.disjoint_left]
    intro q h1 h2
    simp only [Set.mem_prod, Set.mem_compl_iff] at h1 h2
    exact h1.2 h2.2
  set a := ν.real A
  have hac : ν.real Aᶜ = 1 - a := by
    rw [measureReal_compl (hmeasN A), probReal_univ]
  have hprod : ∀ s t : Set ℕ, ρ.real (s ×ˢ t) = ν.real s * ν.real t := by
    intro s t
    rw [measureReal_def, Measure.prod_prod, ENNReal.toReal_mul]
    rfl
  have htwo : 2 * ρ.real E = 2 * (a * (1 - a)) := by
    calc
      2 * ρ.real E = ρ.real E + ρ.real (Prod.swap ⁻¹' E) := by rw [hsym]; ring
      _ = ρ.real (E ∪ Prod.swap ⁻¹' E) := (measureReal_union hdisj (hmeasP _)).symm
      _ = ρ.real (A ×ˢ Aᶜ) + ρ.real (Aᶜ ×ˢ A) := by
        rw [hunion, measureReal_union hdisj2 (hmeasP _)]
      _ = 2 * (a * (1 - a)) := by rw [hprod, hprod, hac]; ring
  have hEq : ρ.real E = a * (1 - a) := by linarith
  rw [hEq]
  nlinarith [sq_nonneg (a - 1 / 2)]

end ThresholdHC.UpperQuarter
