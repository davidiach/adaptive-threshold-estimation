import ThresholdHC.Tier5.Model
import ThresholdHC.Tier3.Examples
import Mathlib.Probability.ProductMeasure

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace ThresholdHC.Tier5
open ThresholdHC.Tier3

def freshBitLaw (q : unitInterval) : Measure (ℕ → Bool) :=
  Measure.infinitePi (fun _ : ℕ => bernoulliMeasure true false q)

instance freshBitLaw_probability (q : unitInterval) : IsProbabilityMeasure (freshBitLaw q) := by
  unfold freshBitLaw
  infer_instance

def freshProcessLaw (q : unitInterval) : Measure (ℕ × (ℕ → Bool)) :=
  exampleSeedLaw.prod (freshBitLaw q)

instance freshProcessLaw_probability (q : unitInterval) : IsProbabilityMeasure (freshProcessLaw q) := by
  unfold freshProcessLaw
  infer_instance

def freshTape (z : ℕ × (ℕ → Bool)) : ProcessTape :=
  fun k => if k < z.1+1 then some (z.2 k) else none

theorem measurable_freshTape : Measurable freshTape := by
  apply Measurable.of_eval
  intro k
  exact (measurable_of_countable (fun z : ℕ × Bool =>
    if k < z.1+1 then some z.2 else none)).comp
    (measurable_fst.prodMk ((measurable_pi_apply k).comp measurable_snd))

theorem freshBitLaw_map_prefix (q : unitInterval) (m : ℕ) :
    (freshBitLaw q).map (fun x => fun i : Fin m => x i.val) =
      Measure.pi (fun _ : Fin m => bernoulliMeasure true false q) := by
  classical
  apply Measure.ext_of_singleton
  intro s
  rw [Measure.map_apply (by fun_prop) (measurableSet_singleton s), Measure.pi_singleton]
  let t : ℕ → Set Bool := fun k => if hk : k < m then {s ⟨k,hk⟩} else Set.univ
  have hset : (fun x : ℕ → Bool => fun i : Fin m => x i.val) ⁻¹' {s} =
      Set.pi (Finset.range m) t := by
    ext x
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_pi]
    constructor
    · intro hx k hk
      have hkm : k < m := Finset.mem_range.mp hk
      simpa [t, hkm] using congrFun hx ⟨k,hkm⟩
    · intro hx
      funext i
      simpa [t, i.isLt] using hx i.val (Finset.mem_range.mpr i.isLt)
  rw [hset, freshBitLaw, Measure.infinitePi_pi _ (fun _ _ => (Set.to_countable _).measurableSet)]
  rw [Finset.prod_fin_eq_prod_range]
  apply Finset.prod_congr rfl
  intro i hi
  simp [t, Finset.mem_range.mp hi]

theorem bernoulli_real_singleton (q : unitInterval) (b : Bool) :
    (bernoulliMeasure true false q).real {b} = if b then (q : ℝ) else 1-q := by
  cases b <;> simp

theorem freshBitLaw_integral_prefix (q : unitInterval) (m : ℕ)
    (f : (Fin m → Bool) → ℝ) :
    (∫ x, f (fun i : Fin m => x i.val) ∂freshBitLaw q) =
      ∑ s : Fin m → Bool, (∏ i, if s i then (q:ℝ) else 1-q) * f s := by
  have hm : Measurable (fun x : ℕ → Bool => fun i : Fin m => x i.val) := by fun_prop
  rw [← integral_map hm.aemeasurable (measurable_of_countable f).aestronglyMeasurable,
    freshBitLaw_map_prefix, integral_fintype (Integrable.of_finite)]
  apply Finset.sum_congr rfl
  intro s hs
  simp only [smul_eq_mul]
  congr 1
  rw [measureReal_def, Measure.pi_singleton, ENNReal.toReal_prod]
  exact Finset.prod_congr rfl (fun i _ => bernoulli_real_singleton q (s i))

end ThresholdHC.Tier5
