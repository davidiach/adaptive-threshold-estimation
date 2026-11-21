import ThresholdHC.Proofs.Tier2.ClassifierExpectations

/-! The misclassification probability `errProbK k1 k2 L d S` at general threshold
coefficients, written as a probability on the infinite Bernoulli tape. This is the
coefficient-generic form of `Tier2.errProbK_eq_measure`, which is stated at
`k1 = k2 = 1` only. -/
noncomputable section
namespace ThresholdHC.BiasAudit
open MeasureTheory ProbabilityTheory Real
open ThresholdHC ThresholdHC.Tier2 ThresholdHC.Uniform713

/-- The decision of a first-crossing classifier with any boundary is measurable. -/
theorem measurable_firstDecision {Ω : Type*} [MeasurableSpace Ω] (b : ℕ → ℕ → ℝ)
    (m : ℕ → Ω → ℝ) (hm : ∀ k, Measurable (m k)) (L : ℕ) :
    Measurable (fun ω => firstDecision b (fun k => m k ω) L) := by
  have hmean : Measurable (fun ω => m (firstStop b (fun k => m k ω) L) ω) :=
    (measurable_from_prod_countable_left (f := fun p : Ω × ℕ => m p.2 p.1)
      (fun k => hm k)).comp
      (measurable_id.prodMk (measurable_firstStop b m hm L))
  exact Measurable.ite (measurableSet_lt measurable_const hmean)
    measurable_const measurable_const

/-- On a long enough tape prefix, the frozen classifier output is the first-crossing
decision with boundary `finiteBoundary k1 k2` applied to the dyadic tape means. -/
theorem zK_prefix_gen (k1 k2 : ℝ) (L : ℕ) {M : ℕ} (hM : 2 ^ L ≤ M) (ω : ℕ → Bool) :
    zK k1 k2 L (tapePrefix M ω) =
      firstDecision (finiteBoundary k1 k2) (fun j => dyadicMean observations j ω) L := by
  rw [zK_eq_firstDecision]
  apply firstDecision_congr_prefix
  intro k hk
  exact finiteMean_prefix ((Nat.pow_le_pow_right (by omega : 0 < 2) hk).trans hM) ω

/-- The error set of the tape classifier is measurable. -/
theorem measurableSet_error (k1 k2 : ℝ) (L : ℕ) (s : ℝ) :
    MeasurableSet
      {ω : ℕ → Bool |
        firstDecision (finiteBoundary k1 k2) (fun j => dyadicMean observations j ω) L ≠ s} :=
  (measurableSet_eq_fun
    (measurable_firstDecision (finiteBoundary k1 k2) (dyadicMean observations)
      (fun k => measurable_prefixMean measurable_observations (2 ^ k)) L)
    measurable_const).compl

/-- `errProbK` at any coefficients is the tape probability of a wrong decision. -/
theorem errProbK_eq_measure_gen (k1 k2 : ℝ) (L : ℕ) (d : ℝ) (S : Bool) (hd : 0 < d)
    (hdmax : d ≤ 1/2) :
    errProbK k1 k2 L d S = (tapeMeasure (coinParameter d S hd hdmax)).real
      {ω | firstDecision (finiteBoundary k1 k2) (fun j => dyadicMean observations j ω) L ≠
        bit S} := by
  classical
  let p := coinParameter d S hd hdmax
  have heq : (fun ω => if (classifyK k1 k2 L (tapePrefix (2 ^ L) ω)).1 = S then (0:ℝ) else 1) =
      {ω | firstDecision (finiteBoundary k1 k2) (fun j => dyadicMean observations j ω) L ≠
        bit S}.indicator (fun _ => (1:ℝ)) := by
    funext ω
    simp only [Set.indicator, Set.mem_ofPred_eq]
    rw [← zK_prefix_gen k1 k2 L le_rfl ω]
    cases h : (classifyK k1 k2 L (tapePrefix (2 ^ L) ω)).1 <;> cases S <;>
      simp [h, zK, bit]
  change (∑ x : Fin (2 ^ L) → Bool, streamProb (p : ℝ) x *
    (if (classifyK k1 k2 L x).1 = S then 0 else 1)) = _
  rw [← integral_prefix, heq, integral_indicator_const (1:ℝ) (measurableSet_error k1 k2 L _)]
  simp [p]

end ThresholdHC.BiasAudit
