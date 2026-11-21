import ThresholdHC.DepthObstruction.Specification
import ThresholdHC.ObservableSimulation.PopulationPath

/-! Pointwise facts about the population simulation. The whole simulation, flip
counts and observed word, depends on each coin tape only through the flips it
actually charges to that coin, even with arbitrary interleaving and feedback.
Under a per-coin cap `N`, replacing every coin tape by its first `N` flips,
completed by `false`, leaves the observed population path unchanged. -/

noncomputable section
namespace ThresholdHC.DepthObstruction
open ThresholdHC.CriticalEntropy ThresholdHC.ObservableSimulation

/-- The simulation is determined by the charged flips of each coin. -/
theorem populationSimulation_prefix_ext {I : Type} [DecidableEq I]
    (n : ℕ) (pol : List Bool → Option I) (s s' : I → ℕ → Bool)
    (h : ∀ i k, k < (populationSimulation pol n s).1 i → s i k = s' i k) :
    populationSimulation pol n s = populationSimulation pol n s' := by
  induction n generalizing pol s s' with
  | zero => rfl
  | succ n ih =>
    cases hp : pol [] with
    | none => simp [populationSimulation, hp]
    | some j =>
      have h0 : s j 0 = s' j 0 := h j 0 (by simp [populationSimulation, hp])
      simp only [populationSimulation, hp] at h ⊢
      rw [← h0]
      have hrec := ih (fun xs => pol (s j 0 :: xs)) (Function.update s j (tapeDrop 1 (s j)))
        (Function.update s' j (tapeDrop 1 (s' j))) (by
          intro i k hk
          by_cases hij : i = j
          · subst hij
            simp only [Function.update_self, tapeDrop]
            exact h i (1+k) (by simp only [ite_true]; omega)
          · simp only [Function.update_of_ne hij]
            exact h i k (by simp only [Ne.symm hij, ite_false, add_zero]; exact hk))
      rw [hrec]

/-- Every coin tape cut to its first `N` flips and completed by `false`. -/
def capTapes (N : ℕ) (s : ℕ → ℕ → Bool) : ℕ → ℕ → Bool :=
  fun i => completePrefix N (Tier2.tapePrefix N (s i))

theorem measurable_capTapes (N : ℕ) : Measurable (capTapes N) :=
  Measurable.of_eval (fun i =>
    (measurable_completePrefix N).comp ((Tier2.measurable_prefix N).comp (measurable_pi_apply i)))

/-- Under a per-coin cap, cutting every tape at the cap does not change the path. -/
theorem populationPath_capTapes {pol : List Bool → Option ℕ} {N : ℕ}
    (hcap : ∀ n s i, (populationSimulation pol n s).1 i ≤ N) (s : ℕ → ℕ → Bool) :
    populationPath pol (capTapes N s) = populationPath pol s := by
  funext k
  unfold populationPath
  rw [populationSimulation_prefix_ext (k+1) pol s (capTapes N s) (fun i m hm => ?_)]
  have hmN : m < N := lt_of_lt_of_le hm (hcap (k+1) s i)
  simp [capTapes, completePrefix, Tier2.tapePrefix, hmN]

end ThresholdHC.DepthObstruction
