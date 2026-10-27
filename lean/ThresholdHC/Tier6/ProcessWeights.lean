import ThresholdHC.Tier5.FiniteCreation
import Mathlib.Probability.Kernel.IonescuTulcea.Traj

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace ThresholdHC.Tier6
open ThresholdHC.Tier3 ThresholdHC.Tier5

def creationTransition {n : ℕ} (pol : List Bool → Option ℕ) (d q : ℕ → ℝ)
    (w : Prefix n) (o : Option Bool) : ℝ :=
  if creationLaw pol d q w = 0 then (if o = none then 1 else 0)
  else creationLaw pol d q (Fin.snoc w o) / creationLaw pol d q w

theorem creationTransition_nonneg {n : ℕ} (pol : List Bool → Option ℕ) (d q : ℕ → ℝ)
    (hd : ∀ i, 0 ≤ d i ∧ d i ≤ 1/2) (hq : ∀ i, 0 ≤ q i ∧ q i ≤ 1)
    (w : Prefix n) (o : Option Bool) : 0 ≤ creationTransition pol d q w o := by
  unfold creationTransition
  split_ifs
  · norm_num
  · norm_num
  · exact div_nonneg ((creationLaw_total (n+1) pol d q hd hq).1 _)
      ((creationLaw_total n pol d q hd hq).1 _)

theorem creationTransition_sum {n : ℕ} (pol : List Bool → Option ℕ) (d q : ℕ → ℝ)
    (w : Prefix n) : (∑ o, creationTransition pol d q w o) = 1 := by
  classical
  by_cases hz : creationLaw pol d q w = 0
  · simp [creationTransition, hz]
  · simp only [creationTransition, hz, ite_false, ← Finset.sum_div,
      creationLaw_sum_extensions, div_self hz]

theorem creationTransition_mul {n : ℕ} (pol : List Bool → Option ℕ) (d q : ℕ → ℝ)
    (hd : ∀ i, 0 ≤ d i ∧ d i ≤ 1/2) (hq : ∀ i, 0 ≤ q i ∧ q i ≤ 1)
    (w : Prefix n) (o : Option Bool) :
    creationLaw pol d q w * creationTransition pol d q w o =
      creationLaw pol d q (Fin.snoc w o) := by
  classical
  by_cases hz : creationLaw pol d q w = 0
  · have hsum := creationLaw_sum_extensions pol d q w
    have hp : ∀ v : Option Bool, 0 ≤ creationLaw pol d q (Fin.snoc w v) :=
      fun v => (creationLaw_total (n+1) pol d q hd hq).1 _
    have hzero : creationLaw pol d q (Fin.snoc w o) = 0 := by
      apply le_antisymm _ (hp o)
      calc
        _ ≤ ∑ v : Option Bool, creationLaw pol d q (Fin.snoc w v) :=
          Finset.single_le_sum (fun v _ => hp v) (Finset.mem_univ o)
        _ = 0 := hsum.trans hz
    simp [hz, hzero]
  · simp only [creationTransition, hz, ite_false]
    exact mul_div_cancel₀ _ hz

theorem measurable_creationTransition {Seed : Type} [MeasurableSpace Seed] {n : ℕ}
    (pol : Seed → List Bool → Option ℕ) (hp : MeasurableCreationPolicy pol)
    (d q : Seed → ℕ → ℝ) (hdm : MeasurableEnvironment d) (hqm : MeasurableEnvironment q)
    (w : Prefix n) (o : Option Bool) :
    Measurable (fun u => creationTransition (pol u) (d u) (q u) w o) := by
  unfold creationTransition
  exact Measurable.ite (measurableSet_eq_fun (measurable_creationLaw pol hp d q hdm hqm w)
      measurable_const) measurable_const
    ((measurable_creationLaw pol hp d q hdm hqm (Fin.snoc w o)).div
      (measurable_creationLaw pol hp d q hdm hqm w))

def creationNextKernel {Seed : Type} [MeasurableSpace Seed]
    (pol : Seed → List Bool → Option ℕ) (d q : Seed → ℕ → ℝ)
    (hp : MeasurableCreationPolicy pol) (hdm : MeasurableEnvironment d)
    (hqm : MeasurableEnvironment q) (n : ℕ) : Kernel (Seed × Prefix n) (Option Bool) where
  toFun x := ∑ o : Option Bool,
    ENNReal.ofReal (creationTransition (pol x.1) (d x.1) (q x.1) x.2 o) • Measure.dirac o
  measurable' := by
    apply Measure.measurable_of_measurable_coe
    intro s hs
    simp only [Measure.finsetSum_apply, Measure.smul_apply, smul_eq_mul]
    apply Finset.measurable_sum
    intro o ho
    have hm : Measurable (fun x : Seed × Prefix n =>
        creationTransition (pol x.1) (d x.1) (q x.1) x.2 o) :=
      measurable_from_prod_countable_left
        (fun w => measurable_creationTransition pol hp d q hdm hqm w o)
    exact hm.ennreal_ofReal.mul measurable_const

theorem creationNextKernel_markov {Seed : Type} [MeasurableSpace Seed]
    (pol : Seed → List Bool → Option ℕ) (d q : Seed → ℕ → ℝ)
    (hp : MeasurableCreationPolicy pol) (hdm : MeasurableEnvironment d)
    (hqm : MeasurableEnvironment q)
    (hd : ∀ u i, 0 ≤ d u i ∧ d u i ≤ 1/2)
    (hq : ∀ u i, 0 ≤ q u i ∧ q u i ≤ 1) (n : ℕ) :
    IsMarkovKernel (creationNextKernel pol d q hp hdm hqm n) := by
  constructor
  intro x
  constructor
  simp only [creationNextKernel, Kernel.coe_mk, Measure.finsetSum_apply,
    Measure.smul_apply, Measure.dirac_apply_of_mem (Set.mem_univ _), smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun o _ =>
    creationTransition_nonneg _ _ _ (hd x.1) (hq x.1) x.2 o),
    creationTransition_sum, ENNReal.ofReal_one]

end ThresholdHC.Tier6
