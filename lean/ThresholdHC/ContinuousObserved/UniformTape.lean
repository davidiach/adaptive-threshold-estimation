import ThresholdHC.CriticalEntropy.UniformCoin

noncomputable section
open MeasureTheory ProbabilityTheory Set
namespace ThresholdHC.ContinuousObserved
open ThresholdHC.CriticalEntropy

def uniformTail (v : ℕ → ℝ) : ℕ → ℝ := fun k => v (k + 1)

theorem measurable_uniformTail : Measurable uniformTail :=
  Measurable.of_eval (fun k => measurable_pi_apply (k + 1))

theorem uniformTail_map : uniformTapeMeasure.map uniformTail = uniformTapeMeasure := by
  unfold uniformTapeMeasure uniformTail
  exact Measure.map_infinitePi_infinitePi_of_inj (fun a b h => Nat.add_right_cancel h)

theorem uniform_head_tail_independent :
    IndepFun (fun v : ℕ → ℝ => v 0) uniformTail uniformTapeMeasure := by
  have hi : iIndepFun (fun (i : ℕ) (v : ℕ → ℝ) => v i) uniformTapeMeasure :=
    iIndepFun_infinitePi (X := fun _ x => x) (fun _ => measurable_id)
  have hd : Disjoint ({0} : Set ℕ) (Ioi 0) := Set.disjoint_left.mpr (by
    intro k hk hp
    simp only [mem_singleton_iff] at hk
    subst k
    exact (lt_irrefl 0) hp)
  have hh := hi.indepFun_set ({0} : Set ℕ) (Ioi 0) hd (fun i => measurable_pi_apply i)
  have hf : Measurable (fun v : ({0} : Set ℕ) → ℝ => v ⟨0,rfl⟩) := measurable_pi_apply _
  have ht : Measurable (fun v : Ioi (0 : ℕ) → ℝ => fun k : ℕ => v ⟨k + 1,Nat.zero_lt_succ k⟩) :=
    Measurable.of_eval (fun _ => measurable_pi_apply _)
  exact hh.comp hf ht

theorem uniform_head_tail_preserving :
    MeasurePreserving (fun v : ℕ → ℝ => (v 0,uniformTail v)) uniformTapeMeasure
      (uniformUnitMeasure.prod uniformTapeMeasure) := by
  refine ⟨(measurable_pi_apply 0).prodMk measurable_uniformTail,?_⟩
  rw [uniform_head_tail_independent.map_prod_eq_prod_map_map
    (measurable_pi_apply 0).aemeasurable measurable_uniformTail.aemeasurable,
    uniformTail_map]
  congr 1
  exact (measurePreserving_eval_infinitePi (fun _ : ℕ => uniformUnitMeasure) 0).map_eq

end ThresholdHC.ContinuousObserved
