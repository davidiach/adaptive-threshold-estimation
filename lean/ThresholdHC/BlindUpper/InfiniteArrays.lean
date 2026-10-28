import Mathlib.Probability.Independence.InfinitePi

noncomputable section
namespace ThresholdHC.BlindUpper
open MeasureTheory ProbabilityTheory Finset

/-- Independent seed and coin arrays can be paired coordinate by coordinate. -/
theorem infinitePi_zip {I X Y : Type} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : I → Measure X) (ν : I → Measure Y)
    [∀ i, IsProbabilityMeasure (μ i)] [∀ i, IsProbabilityMeasure (ν i)] :
    ((Measure.infinitePi μ).prod (Measure.infinitePi ν)).map
      (fun z i => (z.1 i,z.2 i)) = Measure.infinitePi (fun i => (μ i).prod (ν i)) := by
  apply (Measure.isProjectiveLimit_infinitePi (fun i => (μ i).prod (ν i))).unique ?_ |>.symm
  intro s
  let e := MeasurableEquiv.arrowProdEquivProdArrow X Y s
  have hfinite := (measurePreserving_arrowProdEquivProdArrow X Y s
    (fun i => μ i) (fun i => ν i)).symm e
  rw [Measure.map_map (measurable_restrict s) (by fun_prop)]
  change (((Measure.infinitePi μ).prod (Measure.infinitePi ν)).map
    (e.symm ∘ Prod.map s.restrict s.restrict)) = _
  rw [← Measure.map_map e.symm.measurable (by fun_prop),
    ← Measure.map_prod_map _ _ (measurable_restrict s) (measurable_restrict s),
    Measure.infinitePi_map_restrict,Measure.infinitePi_map_restrict]
  exact hfinite.map_eq

/-- Three fixed, distinct coordinates of an iid array have the product law. -/
theorem infinitePi_three {X : Type} [MeasurableSpace X]
    (ν : Measure X) [IsProbabilityMeasure ν] :
    (Measure.infinitePi (fun _ : ℕ => ν)).map (fun z => ((z 0,z 1),z 2)) =
      (ν.prod ν).prod ν := by
  have hi : iIndepFun (fun i : ℕ => fun z : ℕ → X => z i)
      (Measure.infinitePi (fun _ : ℕ => ν)) :=
    iIndepFun_infinitePi (fun _ => measurable_id)
  rw [(hi.indepFun_prodMk (fun i => measurable_pi_apply i) 0 1 2 (by omega) (by omega)).map_prod_eq_prod_map_map
    ((measurable_pi_apply 0).prodMk (measurable_pi_apply 1)).aemeasurable
    (measurable_pi_apply 2).aemeasurable]
  rw [Measure.infinitePi_map_eval_prod (by omega : (0 : ℕ) ≠ 1),Measure.infinitePi_map_eval]

def splitPairArray {X : Type} (z : ℕ → X) : ℕ → ℕ → X :=
  fun j i => z (Nat.pair j i)

theorem measurable_splitPairArray {X : Type} [MeasurableSpace X] :
    Measurable (splitPairArray (X := X)) := by
  apply Measurable.of_eval
  intro j
  exact Measurable.of_eval (fun i => measurable_pi_apply (Nat.pair j i))

/-- Pair-number labels supply independent streams, including unused streams. -/
theorem splitPairArray_map {X : Type} [MeasurableSpace X]
    (ν : Measure X) [IsProbabilityMeasure ν] :
    (Measure.infinitePi (fun _ : ℕ => ν)).map splitPairArray =
      Measure.infinitePi (fun _ : ℕ => Measure.infinitePi (fun _ : ℕ => ν)) := by
  let f : ℕ × ℕ → ℕ := fun z => Nat.pair z.1 z.2
  have hf : Function.Injective f := by
    intro a b hab
    exact Prod.ext (Nat.pair_eq_pair.mp hab).1 (Nat.pair_eq_pair.mp hab).2
  have hmap := Measure.map_infinitePi_infinitePi_of_inj (P := fun _ : ℕ => ν) hf
  change (Measure.infinitePi (fun _ : ℕ => ν)).map
    ((MeasurableEquiv.curry ℕ ℕ X) ∘ (fun z i => z (f i))) = _
  rw [← Measure.map_map (MeasurableEquiv.curry ℕ ℕ X).measurable (by fun_prop),hmap]
  exact Measure.infinitePi_map_curry (fun _ _ : ℕ => ν)

end ThresholdHC.BlindUpper
