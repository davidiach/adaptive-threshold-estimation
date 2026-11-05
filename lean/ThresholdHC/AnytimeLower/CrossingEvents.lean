import ThresholdHC.AnytimeLower.EventTesting
import Mathlib.Topology.Algebra.InfiniteSum.Real

noncomputable section
open MeasureTheory InformationTheory Real Set
open scoped ENNReal
namespace ThresholdHC.AnytimeLower

def firstCrossing {Ω : Type} (E : ℕ → Set Ω) (k : ℕ) : Set Ω :=
  E k \ ⋃ i < k, E i

@[simp] theorem mem_firstCrossing {Ω : Type} (E : ℕ → Set Ω) (k : ℕ) (x : Ω) :
    x ∈ firstCrossing E k ↔ x ∈ E k ∧ ∀ i < k, x ∉ E i := by
  simp [firstCrossing]

theorem measurableSet_firstCrossing {Ω : Type} [MeasurableSpace Ω]
    (E : ℕ → Set Ω) (hE : ∀ k, MeasurableSet (E k)) (k : ℕ) :
    MeasurableSet (firstCrossing E k) :=
  (hE k).diff (MeasurableSet.iUnion fun i => MeasurableSet.iUnion fun _ => hE i)

theorem firstCrossing_disjoint {Ω : Type} (E : ℕ → Set Ω) :
    Pairwise (fun i j : ℕ => Disjoint (firstCrossing E i) (firstCrossing E j)) := by
  intro i j hij
  apply Set.disjoint_left.mpr
  intro x hx hy
  rw [mem_firstCrossing] at hx hy
  rcases lt_or_gt_of_ne hij with h | h
  · exact hy.2 i h hx.1
  · exact hx.2 j h hy.1

theorem sum_firstCrossing_le {Ω : Type} [MeasurableSpace Ω]
    (Q : Measure Ω) [IsFiniteMeasure Q] (E : ℕ → Set Ω)
    (hE : ∀ k, MeasurableSet (E k)) (s : Finset ℕ) :
    ∑ k ∈ s, Q.real (firstCrossing E k) ≤ Q.real (⋃ k, E k) := by
  rw [← measureReal_biUnion_finset
    (fun i _ j _ hij => firstCrossing_disjoint E hij)
    (fun k _ => measurableSet_firstCrossing E hE k)]
  apply measureReal_mono (μ := Q) ?_ (measure_ne_top Q _)
  intro x hx
  obtain ⟨k,_,hk⟩ := Set.mem_iUnion₂.mp hx
  exact Set.mem_iUnion.mpr ⟨k,(mem_firstCrossing E k x).mp hk |>.1⟩

/-- Arbitrary dependent observations are allowed. Each first-crossing event
must be readable from its actual observed prefix; only that prefix's KL is
charged. The reference law is common to all the alternatives. -/
theorem firstCrossing_information_budget {Ω : Type} [MeasurableSpace Ω]
    {X : ℕ → Type} [∀ k, MeasurableSpace (X k)]
    (Q : Measure Ω) [IsProbabilityMeasure Q]
    (P : ℕ → Measure Ω) [∀ k, IsProbabilityMeasure (P k)]
    (E : ℕ → Set Ω) (hE : ∀ k, MeasurableSet (E k))
    (obs : ∀ k, Ω → X k) (hobs : ∀ k, Measurable (obs k))
    (A : ∀ k, Set (X k)) (hA : ∀ k, MeasurableSet (A k))
    (hread : ∀ k, obs k ⁻¹' A k = firstCrossing E k)
    {δ : ℝ} (hd : 0 ≤ δ ∧ δ ≤ 1/2) (K : ℕ → ℝ) (hK : ∀ k, 0 ≤ K k)
    (hpower : ∀ k, 1-δ ≤ (P k).real (firstCrossing E k))
    (herror : Q.real (⋃ k, E k) ≤ δ)
    (hkl : ∀ k, klDiv ((P k).map (obs k)) (Q.map (obs k)) ≤ ENNReal.ofReal (K k))
    (s : Finset ℕ) :
    ∑ k ∈ s, exp (-K k/(1-δ)) ≤ 4*δ := by
  have htest (k : ℕ) : exp (-K k/(1-δ))/4 ≤ Q.real (firstCrossing E k) := by
    let : IsProbabilityMeasure (Q.map (obs k)) :=
      (Measure.isProbabilityMeasure_map_iff (hobs k).aemeasurable).2 inferInstance
    let : IsProbabilityMeasure ((P k).map (obs k)) :=
      (Measure.isProbabilityMeasure_map_iff (hobs k).aemeasurable).2 inferInstance
    have hp : 1-δ ≤ ((P k).map (obs k)).real (A k) := by
      rw [map_measureReal_apply (hobs k) (hA k),hread k]
      exact hpower k
    have ht := event_probability_lower ((P k).map (obs k)) (Q.map (obs k))
      (A k) (hA k) hd (hK k) hp (hkl k)
    simpa [map_measureReal_apply (hobs k) (hA k),hread k] using ht
  have hs := (Finset.sum_le_sum (s := s) (fun k _ => htest k)).trans
    ((sum_firstCrossing_le Q E hE s).trans herror)
  rw [← Finset.sum_div] at hs
  linarith

theorem firstCrossing_information_summable {Ω : Type} [MeasurableSpace Ω]
    {X : ℕ → Type} [∀ k, MeasurableSpace (X k)]
    (Q : Measure Ω) [IsProbabilityMeasure Q]
    (P : ℕ → Measure Ω) [∀ k, IsProbabilityMeasure (P k)]
    (E : ℕ → Set Ω) (hE : ∀ k, MeasurableSet (E k))
    (obs : ∀ k, Ω → X k) (hobs : ∀ k, Measurable (obs k))
    (A : ∀ k, Set (X k)) (hA : ∀ k, MeasurableSet (A k))
    (hread : ∀ k, obs k ⁻¹' A k = firstCrossing E k)
    {δ : ℝ} (hd : 0 ≤ δ ∧ δ ≤ 1/2) (K : ℕ → ℝ) (hK : ∀ k, 0 ≤ K k)
    (hpower : ∀ k, 1-δ ≤ (P k).real (firstCrossing E k))
    (herror : Q.real (⋃ k, E k) ≤ δ)
    (hkl : ∀ k, klDiv ((P k).map (obs k)) (Q.map (obs k)) ≤ ENNReal.ofReal (K k)) :
    Summable (fun k => exp (-K k/(1-δ))) :=
  summable_of_sum_le (fun _ => (exp_pos _).le)
    (firstCrossing_information_budget Q P E hE obs hobs A hA hread hd K hK hpower herror hkl)

end ThresholdHC.AnytimeLower
