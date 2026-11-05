import ThresholdHC.QuantileSharpLaw.Concavity
import Mathlib.Analysis.Convex.Combination

noncomputable section
open Real
namespace ThresholdHC.QuantileSharpLaw
open ThresholdHC.EntropyTailQuantile

theorem exists_corePrice_vertex {ι : Type*} [Fintype ι] (e m w v : ι → ℝ)
    (he : ∀ i, 0 ≤ e i) (hv : v ∈ Set.Icc (0 : ι → ℝ) w) :
    ∃ z ∈ Set.Icc (0 : ι → ℝ) w, (∀ i, z i=0 ∨ z i=w i) ∧ corePrice e m w z ≤ corePrice e m w v := by
  have hw (i) : 0 ≤ w i := (hv.1 i).trans (hv.2 i)
  let corners : Set (ι → ℝ) := Set.univ.pi (fun i => ({0,w i} : Set ℝ))
  have hsub : corners ⊆ Set.Icc (0 : ι → ℝ) w := by
    intro z hz
    have hi (i) : z i=0 ∨ z i=w i := by simpa using hz i (Set.mem_univ i)
    constructor
    · intro i
      rcases hi i with h | h
      · exact h.symm.le
      · exact h.symm ▸ hw i
    · intro i
      rcases hi i with h | h
      · exact h.symm ▸ hw i
      · exact h.le
  have hmem : v ∈ convexHull ℝ corners := by
    apply mem_convexHull_pi
    intro i _
    rw [convexHull_pair,segment_eq_Icc (hw i)]
    exact ⟨hv.1 i,hv.2 i⟩
  obtain ⟨z,hz,hprice⟩ := (corePrice_concaveOn e m w he).exists_le_of_mem_convexHull hsub hmem
  refine ⟨z,hsub hz,?_,hprice⟩
  intro i
  simpa using hz i (Set.mem_univ i)

theorem exists_disjoint_core_split {ι : Type*} [Fintype ι] (e m v b : ι → ℝ)
    (he : ∀ i, 0 ≤ e i) (hv : ∀ i, 0 ≤ v i) (hb : ∀ i, 0 ≤ b i) :
    ∃ z d : ι → ℝ, (∀ i, 0 ≤ z i) ∧ (∀ i, 0 ≤ d i) ∧
      (∀ i, z i+d i=v i+b i) ∧ (∀ i, z i=0 ∨ d i=0) ∧
      sqrt (costEntropy (fun i => z i+e i))+(∑ i, m i*d i) ≤
        sqrt (costEntropy (fun i => v i+e i))+(∑ i, m i*b i) := by
  have hbox : v ∈ Set.Icc (0 : ι → ℝ) (fun i => v i+b i) :=
    ⟨hv,fun i => le_add_of_nonneg_right (hb i)⟩
  obtain ⟨z,hz,hcorner,hprice⟩ := exists_corePrice_vertex e m (fun i => v i+b i) v he hbox
  refine ⟨z,(fun i => v i+b i-z i),hz.1,?_,?_,?_,?_⟩
  · exact fun i => sub_nonneg.mpr (hz.2 i)
  · intro i
    ring
  · intro i
    rcases hcorner i with hi | hi
    · exact Or.inl hi
    · exact Or.inr (by change v i+b i-z i=0; rw [hi]; ring)
  · simpa only [corePrice,add_sub_cancel_left] using hprice

end ThresholdHC.QuantileSharpLaw
