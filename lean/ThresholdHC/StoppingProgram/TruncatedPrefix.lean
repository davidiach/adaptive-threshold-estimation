import ThresholdHC.RareAboveTwo.TerminalInformation

/-! A measurable finite-prefix estimate returns the original output when the
policy has stopped, and the center of the rare-mean interval otherwise. -/

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace ThresholdHC.StoppingProgram
open ThresholdHC.Tier3 ThresholdHC.Tier4 ThresholdHC.Tier6 ThresholdHC.RareAboveTwo

theorem valid_path_halt_reconstruction (pol : List Bool → Option ℕ) (x : ProcessTape)
    (hv : ∀ k, (x k).isSome = (pol (processHistory x k)).isSome)
    (N : ℕ) (hN : pol (processHistory x N) = none) :
    padPrefix N (processPrefix N x) = x := by
  let p : List Bool → Option (Fin 1) := fun xs => (pol xs).map (fun _ => 0)
  have hp : ∀ k, (x k).isSome = (p (processHistory x k)).isSome := by
    intro k
    simpa only [p,Option.isSome_map] using hv k
  have hstop : p (processHistory x N) = none := by simp [p,hN]
  exact padPrefix_eq_of_tail_none x N (stopped_valid_tail p x hp N hstop)

theorem valid_path_continuation_work (pol : List Bool → Option ℕ) (x : ProcessTape)
    (hv : ∀ k, (x k).isSome = (pol (processHistory x k)).isSome)
    (N : ℕ) (hN : pol (processHistory x N) ≠ none) :
    ENNReal.ofReal ((N:ℝ)+1) ≤ totalProcessWork x := by
  let p : List Bool → Option (Fin 1) := fun xs => (pol xs).map (fun _ => 0)
  have hp : ∀ k, (x k).isSome = (p (processHistory x k)).isSome := by
    intro k
    simpa only [p,Option.isSome_map] using hv k
  have hsome (k : ℕ) (hk : k ≤ N) : (x k).isSome = true := by
    cases hcase : x k with
    | some b => rfl
    | none =>
      have hpk : p (processHistory x k) = none := by
        have hh := hp k
        simp only [hcase,Option.isSome_none] at hh
        cases he : p (processHistory x k) <;> simp_all
      have hxN := stopped_valid_tail p x hp k hpk N hk
      have hh := hv N
      simp only [hxN,Option.isSome_none] at hh
      cases he : pol (processHistory x N) <;> simp_all
  have he : ThresholdHC.workOf (processPrefix (N+1) x) = (N:ℝ)+1 := by
    simp [ThresholdHC.workOf,processPrefix,fun i : Fin (N+1) => hsome i.val (by omega)]
  rw [← he]
  exact le_iSup (fun n => ENNReal.ofReal (ThresholdHC.workOf (processPrefix n x))) (N+1)

def prefixTruncation {R : Type} [MeasurableSpace R] (A : AdaptiveEstimator R)
    (ρ : ℝ) (N : ℕ) (z : R × (Fin N → Option Bool)) : ℝ :=
  if A.policy z.1 (ThresholdHC.Proofs.fullHist z.2) = none then
    A.output (z.1,padPrefix N z.2) else ρ/2

theorem measurable_prefixTruncation {R : Type} [MeasurableSpace R]
    (A : AdaptiveEstimator R) (ρ : ℝ) (N : ℕ) : Measurable (prefixTruncation A ρ N) := by
  have hm : Measurable (fun z : R × (Fin N → Option Bool) =>
      A.policy z.1 (ThresholdHC.Proofs.fullHist z.2)) :=
    measurable_from_prod_countable_left (fun w =>
      measurable_to_countable' (A.policy_measurable (ThresholdHC.Proofs.fullHist w)))
  exact (A.output_measurable.comp (measurable_padJoint N)).ite
    (measurableSet_eq_fun hm measurable_const) measurable_const

theorem original_path_valid {R : Type} [MeasurableSpace R]
    (μ : Measure Gap) [IsProbabilityMeasure μ] (A : AdaptiveEstimator R) (q : SignLaw) :
    ∀ᵐ z ∂experimentLaw μ A q, ∀ k,
      (z.2 k).isSome = (A.policy z.1.1 (processHistory z.2 k)).isSome :=
  ae_all_iff.mpr (fun k => ThresholdHC.Tier5.realized_creation_valid_step
    (populationSeedLaw μ A) (experimentLaw μ A q) Prod.fst Prod.snd
    (populationPolicy A) populationGap (populationPrior q) measurable_fst
    observable_tape_measurable (measurable_populationPolicy A) (population_realization R μ A q).2 k)

theorem prefixTruncation_loss {R : Type} [MeasurableSpace R]
    (A : AdaptiveEstimator R) (ρ θ : ℝ) (hθ : 0 ≤ θ ∧ θ ≤ ρ)
    (N : ℕ) (r : R) (x : ProcessTape)
    (hv : ∀ k, (x k).isSome = (A.policy r (processHistory x k)).isSome) :
    (prefixTruncation A ρ N (r,processPrefix N x)-θ)^2 ≤
      (A.output (r,x)-θ)^2 + (ρ/2)^2 *
        (if A.policy r (processHistory x N) = none then 0 else 1) := by
  have he : ThresholdHC.Proofs.fullHist (processPrefix N x) = processHistory x N := rfl
  by_cases hN : A.policy r (processHistory x N) = none
  · have hx := valid_path_halt_reconstruction (A.policy r) x hv N hN
    simp [prefixTruncation,he,hN,hx]
  · simp only [prefixTruncation,he,hN,ite_false,mul_one]
    nlinarith [sq_nonneg (A.output (r,x)-θ),mul_nonneg hθ.1 (sub_nonneg.mpr hθ.2)]

end ThresholdHC.StoppingProgram
