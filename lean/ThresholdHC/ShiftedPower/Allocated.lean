import ThresholdHC.ShiftedPower.Geometric

noncomputable section
open MeasureTheory Real
open scoped ENNReal
namespace ThresholdHC.ShiftedPower
open ThresholdHC.Tier6 ThresholdHC.RareAboveTwo ThresholdHC.EntropyTailExecution
open ThresholdHC.EntropyTailUpper ThresholdHC.EntropyTailAssembly ThresholdHC.ObservableSimulation

def shiftedCall (k j : ℕ) : FiniteCall := incrementCall (fun l => classifierCall (k+l)) j
def varianceWeights (α a : ℝ) (k J : ℕ) (i : Fin (J+1)) : ℝ := 8*massBound α a (k+i.val)
def costWeights (α a : ℝ) (k J : ℕ) (i : Fin (J+1)) : ℝ := 2*workBound α a (k+i.val)

def shiftedEstimator (α a B : ℝ) (k J : ℕ) : AdaptiveEstimator (Fin (J+1) → ℕ) :=
  allocatedEstimator B (varianceWeights α a k J) (costWeights α a k J) (fun i => shiftedCall k i.val)

private theorem work_positive {α a : ℝ} (hα : 0 < α) (hu : α < 2) (ha : 0 < a) (k : ℕ) :
    0 < workBound α a k := by
  rw [work_formula]
  exact mul_pos (mul_pos (workConstant_pos hα hu) (by positivity)) (mass_positive ha k)

theorem increment_variance (ν : Measure Gap) [IsProbabilityMeasure ν] (q : SignLaw)
    {α a ρ : ℝ} (hα : 0 < α) (hu : α < 2) (ha : 0 < a) (hm : PowerMargin ν α a)
    (hq : RarePrior ν ρ q) (k : ℕ) (hk : ρ ≤ 2*massBound α a k) (j : ℕ) :
    (∫ ω, ((shiftedCall k j).value ω)^2 ∂originalPopulationTapeLaw ν q) ≤ 8*massBound α a (k+j) := by
  cases j with
  | zero =>
    have he : (fun ω => ((shiftedCall k 0).value ω)^2) = (classifierCall k).value := by
      funext ω; rcases classifierCall_binary k ω with h|h <;> simp [shiftedCall,incrementCall,h]
    rw [he]
    have hb := (abs_le.mp (population_classifier_bias ν q hα hu ha hm k)).2
    have he := error_le_mass ha hα hu k
    change signMean ν q.val ≤ ρ at hq
    simp only [Nat.add_zero]
    nlinarith [mass_positive (α := α) ha k]
  | succ j =>
    have hd := population_classifier_difference ν q hα hu ha hm (k+(j+1)) (k+j)
    have he₁ := error_le_mass ha hα hu (k+(j+1))
    have he₂ := error_le_mass ha hα hu (k+j)
    have hr := (decay_bounds hα hu).1
    have hp := mass_positive (α := α) ha (k+j)
    have hs := mass_succ (α := α) ha (k+j)
    have hprev : massBound α a (k+j) ≤ 2*massBound α a (k+(j+1)) := by
      rw [Nat.add_succ,hs]
      nlinarith [mul_le_mul_of_nonneg_left hr.le hp.le]
    change (∫ ω, ((classifierCall (k+(j+1))).value ω-(classifierCall (k+j)).value ω)^2
      ∂originalPopulationTapeLaw ν q) ≤ _
    linarith only [hd,he₁,he₂,hprev,le_of_lt (mass_positive (α := α) ha (k+(j+1)))]

/-- Positive Poisson allocation realizes every finite shifted telescope.
The estimator is fixed before the law and prior entering these bounds. -/
theorem shifted_bounds (ν : Measure Gap) [IsProbabilityMeasure ν] (q : SignLaw)
    {α a ρ B : ℝ} (hα : 0 < α) (hu : α < 2) (ha : 0 < a) (hB : 0 < B)
    (hm : PowerMargin ν α a) (hq : RarePrior ν ρ q) (k J : ℕ) (hk : ρ ≤ 2*massBound α a k) :
    expectedWork ν (shiftedEstimator α a B k J) q ≤ ENNReal.ofReal B ∧
    rootMeanRisk (experimentLaw ν (shiftedEstimator α a B k J) q)
      (populationOutput (shiftedEstimator α a B k J)) (signMean ν q.val) ≤
      ENNReal.ofReal (errorBound α a (k+J)+allocationCertificate (varianceWeights α a k J) (costWeights α a k J)/sqrt B) := by
  let A := fun j => classifierCall (k+j)
  let K := fun j => (2:ℝ)^(k+j)
  let D : Fin (J+1) → FiniteCall := fun i => shiftedCall k i.val
  let v := varianceWeights α a k J
  let c := costWeights α a k J
  have hv (i) : 0 < v i := mul_pos (by norm_num) (mass_positive ha _)
  have hc (i) : 0 < c i := mul_pos (by norm_num) (work_positive hα hu ha _)
  have hK (j ω) : ((A j).cost ω:ℝ) ≤ K j := classifierCall_cap _ _
  have hbin (j ω) := classifierCall_binary (k+j) ω
  have hcost (i : Fin (J+1)) : (∫ ω, ((D i).cost ω:ℝ) ∂originalPopulationTapeLaw ν q) ≤ c i := by
    have h := incrementCall_work_bound (originalPopulationTapeLaw ν q) A K (fun j => workBound α a (k+j)) hK
      (fun j => population_classifier_work ν q hα hu ha hm (k+j)) i.val
    apply h.trans
    dsimp only [adjacentCost,c,costWeights]
    split_ifs with hi
    · have hp := (work_positive hα hu ha (k+i.val)).le; linarith only [hp]
    · have hle := work_mono hα hu ha (show k+(i.val-1) ≤ k+i.val by omega)
      linarith only [hle]
  refine ⟨allocated_work_bound hB hv hc D (fun i ω => incrementCall_cost_bound A K hK i.val ω) ν q hcost,?_⟩
  have hb : 0 ≤ errorBound α a (k+J) := by
    exact div_nonneg (Real.rpow_nonneg (div_nonneg (resolution_pos _).le ha.le) _) (by linarith)
  apply allocated_rootRisk_bound hB hv hc D (fun _ => by norm_num)
    (fun i ω => incrementCall_bounded A hbin i.val ω) ν q _ (fun i => increment_variance ν q hα hu ha hm hq k hk i.val) hb
  change |(∑ i : Fin (J+1), ∫ ω, (incrementCall A i.val).value ω ∂originalPopulationTapeLaw ν q)-signMean ν q.val| ≤ _
  rw [incrementCall_mean_sum (originalPopulationTapeLaw ν q) A hbin J]
  exact population_classifier_bias ν q hα hu ha hm (k+J)

end ThresholdHC.ShiftedPower
