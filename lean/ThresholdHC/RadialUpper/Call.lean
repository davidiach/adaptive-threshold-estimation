import ThresholdHC.RadialUpper.Walk
import ThresholdHC.RadialUpper.Specification
import ThresholdHC.RareAboveTwo.PopulationError

/-! The capped walk as one observable call on a fresh coin, and its expectations
under the population mixture of the original experiment.

The call reads the coin's tape, runs the walk from state `1` with boundaries `0`
and `K` for at most `N` flips, and returns `alpha` after an upper hit and `beta`
otherwise. Under a sign law `q`, the expectation of any statistic of the run is the
`mu`-average of `q(d) E_{1/2+d} + (1-q(d)) E_{1/2-d}`. -/

noncomputable section
namespace ThresholdHC.RadialUpper
open MeasureTheory ThresholdHC.Tier6 ThresholdHC.ObservableSimulation

/-- Value of a final state: `alpha` after an upper hit, `beta` otherwise. -/
def hitValue (K : ℕ) (α β : ℝ) (k : ℕ) : ℝ := if K ≤ k then α else β

theorem hitValue_eq (K : ℕ) (α β : ℝ) (k : ℕ) : hitValue K α β k = β + (α-β) * walkHit K k := by
  unfold hitValue walkHit; split <;> ring

theorem hitValue_sq (K : ℕ) (α β : ℝ) (k : ℕ) :
    hitValue K α β k ^ 2 = β^2 + (α^2-β^2) * walkHit K k := by
  unfold hitValue walkHit; split <;> ring

theorem abs_hitValue_le (K : ℕ) (α β : ℝ) (k : ℕ) : |hitValue K α β k| ≤ |α| + |β| := by
  unfold hitValue; split
  · linarith [abs_nonneg β]
  · linarith [abs_nonneg α]

/-- The capped two-boundary walk as a finite observable call. -/
def walkCall (K N : ℕ) (hK : 2 ≤ K) (hN : 0 < N) (α β : ℝ) : EntropyTailExecution.FiniteCall where
  cost ω := (walkRun K N 1 (Tier2.tapePrefix N ω)).1
  value ω := hitValue K α β (walkRun K N 1 (Tier2.tapePrefix N ω)).2
  measurable_cost := (measurable_of_countable (fun w : Fin N → Bool => (walkRun K N 1 w).1)).comp
    (Tier2.measurable_prefix N)
  measurable_value := (measurable_of_countable
    (fun w : Fin N → Bool => hitValue K α β (walkRun K N 1 w).2)).comp (Tier2.measurable_prefix N)
  positive ω := walkRun_steps_pos K N 1 _ ⟨one_pos, by omega⟩ hN
  prefix_ext ω ω' h := by
    have hw : walkRun K N 1 (Tier2.tapePrefix N ω') = walkRun K N 1 (Tier2.tapePrefix N ω) :=
      walkRun_prefix K N 1 _ _ (fun i hi => congrFun h ⟨i.val, hi⟩)
    exact ⟨by rw [hw], by rw [hw]⟩

theorem walkCall_cost (K N : ℕ) (hK : 2 ≤ K) (hN : 0 < N) (α β : ℝ) (ω : ℕ → Bool) :
    (walkCall K N hK hN α β).cost ω = (walkRun K N 1 (Tier2.tapePrefix N ω)).1 := rfl

theorem walkCall_value (K N : ℕ) (hK : 2 ≤ K) (hN : 0 < N) (α β : ℝ) (ω : ℕ → Bool) :
    (walkCall K N hK hN α β).value ω = hitValue K α β (walkRun K N 1 (Tier2.tapePrefix N ω)).2 :=
  rfl

theorem walkCall_cost_le (K N : ℕ) (hK : 2 ≤ K) (hN : 0 < N) (α β : ℝ) (ω : ℕ → Bool) :
    (walkCall K N hK hN α β).cost ω ≤ N := walkRun_steps_le K N 1 _

theorem walkCall_value_le (K N : ℕ) (hK : 2 ≤ K) (hN : 0 < N) (α β : ℝ) (ω : ℕ → Bool) :
    |(walkCall K N hK hN α β).value ω| ≤ |α| + |β| := abs_hitValue_le K α β _

theorem continuous_walkSum (K n k : ℕ) (g : ℕ × ℕ → ℝ) : Continuous (fun p => walkSum p K n k g) := by
  unfold walkSum streamProb
  refine continuous_finsetSum _ fun w _ => (continuous_finsetProd _ fun i _ => ?_).mul continuous_const
  rcases Bool.eq_false_or_eq_true (w i) with h | h <;> simp only [h, Bool.false_eq_true, ite_false, ite_true] <;> fun_prop

theorem walk_tape_integral (p : unitInterval) (K N : ℕ) (Φ : ℕ × ℕ → ℝ) :
    (∫ ω, Φ (walkRun K N 1 (Tier2.tapePrefix N ω)) ∂Tier2.tapeMeasure p) = walkSum p K N 1 Φ :=
  Tier2.integral_prefix p (fun w => Φ (walkRun K N 1 w))

theorem gapParameter_true_val (d : Gap) : ((gapParameter true d : unitInterval) : ℝ) = 1/2+d := by
  simp [gapParameter]

theorem gapParameter_false_val (d : Gap) : ((gapParameter false d : unitInterval) : ℝ) = 1/2-d := by
  simp [gapParameter]; ring

theorem measurable_walkStat (K N : ℕ) (Φ : ℕ × ℕ → ℝ) :
    Measurable (fun ω => Φ (walkRun K N 1 (Tier2.tapePrefix N ω))) :=
  (measurable_of_countable (fun w : Fin N → Bool => Φ (walkRun K N 1 w))).comp
    (Tier2.measurable_prefix N)

/-- The population mixture of a statistic of the capped walk. -/
theorem walk_population_integral (μ : Measure Gap) [IsProbabilityMeasure μ] (q : SignLaw)
    (K N : ℕ) (Φ : ℕ × ℕ → ℝ) :
    (∫ ω, Φ (walkRun K N 1 (Tier2.tapePrefix N ω)) ∂originalPopulationTapeLaw μ q) =
      ∫ d, (q.val d * walkSum (1/2+(d:ℝ)) K N 1 Φ +
        (1-q.val d) * walkSum (1/2-(d:ℝ)) K N 1 Φ) ∂μ := by
  rw [RareAboveTwo.originalTape_integral_mixture μ q _ (measurable_walkStat K N Φ)
    (∑ w : Fin N → Bool, |Φ (walkRun K N 1 w)|) (fun ω => Finset.single_le_sum
      (f := fun w => |Φ (walkRun K N 1 w)|) (fun w _ => abs_nonneg _) (Finset.mem_univ _))]
  congr 1
  funext d
  rw [walk_tape_integral, walk_tape_integral, gapParameter_true_val, gapParameter_false_val]

/-- Expectations of the call value under any probability law of the tape, through the
upper-hit probability. -/
theorem walkCall_moments (P : Measure (ℕ → Bool)) [IsProbabilityMeasure P]
    (K N : ℕ) (hK : 2 ≤ K) (hN : 0 < N) (α β : ℝ) :
    (∫ ω, (walkCall K N hK hN α β).value ω ∂P) =
        β + (α-β) * ∫ ω, walkHit K (walkRun K N 1 (Tier2.tapePrefix N ω)).2 ∂P ∧
      (∫ ω, ((walkCall K N hK hN α β).value ω)^2 ∂P) =
        β^2 + (α^2-β^2) * ∫ ω, walkHit K (walkRun K N 1 (Tier2.tapePrefix N ω)).2 ∂P := by
  have hm := measurable_walkStat K N (fun r => walkHit K r.2)
  have hi : Integrable (fun ω => walkHit K (walkRun K N 1 (Tier2.tapePrefix N ω)).2) P :=
    Integrable.of_bound hm.aestronglyMeasurable 1 (ae_of_all _ fun ω => by
      rw [Real.norm_eq_abs, abs_of_nonneg (walkHit_nonneg _ _)]; exact walkHit_le_one _ _)
  constructor
  · simp only [walkCall_value, hitValue_eq]
    rw [integral_add (integrable_const _) (hi.const_mul _), integral_const_mul]
    simp
  · simp only [walkCall_value, hitValue_sq]
    rw [integral_add (integrable_const _) (hi.const_mul _), integral_const_mul]
    simp

end ThresholdHC.RadialUpper
