import ThresholdHC.ObservedState.Design

noncomputable section
open MeasureTheory Set
namespace ThresholdHC.ObservedState
open ThresholdHC.Tier6

/-- The prescribed law is realized on a uniform observed state. Replication
makes the deterministic sign target concentrate under both testing priors. -/
theorem cell_design_exists (μ : Measure Gap) [IsProbabilityMeasure μ]
    (h : Gap) {δ : ℝ} (hδ : 0 < δ) : Nonempty (CellDesign μ h δ) := by
  classical
  obtain ⟨T,hm,hfinite,hup,hclip⟩ := finite_upward_rounding h
  obtain ⟨N,_,cap,label,hl,he⟩ := finite_range_labels T hm hfinite
  have : IsProbabilityMeasure (μ.map T) :=
    (Measure.isProbabilityMeasure_map_iff hm.aemeasurable).mpr inferInstance
  let Δ := (1 / 4 : ℝ) * modulus (μ.map T) h
  have hΔ : 0 < Δ := mul_pos (by norm_num) (modulus_pos (μ.map T) h.property.1)
  obtain ⟨M,hM,hcount⟩ := replication_count hΔ hδ
  have : NeZero M := ⟨Nat.ne_of_gt hM⟩
  obtain ⟨f,hf,hflaw⟩ := outer_source μ M
  let e : Fin N × Fin M ≃ Fin (N * M) := finProdFinEquiv
  let cell : unitInterval → Fin (N * M) := fun u => e (label (f u).1,(f u).2)
  let caps : Fin (N * M) → Gap := fun i => cap (e.symm i).1
  have hc : Measurable cell := (measurable_of_countable e).comp ((hl.comp hf.fst).prodMk hf.snd)
  have hcaps (i : Fin N × Fin M) : caps (e i) = cap i.1 := by simp [caps]
  have hcap (u : unitInterval) : caps (cell u) = T (f u).1 := by
    rw [show cell u = e (label (f u).1,(f u).2) from rfl,hcaps,he]
  have hw (i : Fin N × Fin M) :
      cellWeight cell (e i) = replicatedWeight (labelWeight μ label) M i := by
    have hset : {u : unitInterval | cell u = e i} =
        {u : unitInterval | label (f u).1 = i.1 ∧ (f u).2 = i.2} := by
      ext u
      simp only [cell,mem_ofPred_eq,Equiv.apply_eq_iff_eq,Prod.ext_iff]
    change volume.real {u : unitInterval | cell u = e i} = _
    rw [hset,cell_mass μ M label hl f hf hflaw i.1 i.2]
    rfl
  have hmoment : (∑ i, labelWeight μ label i * clippedGap h (cap i)) =
      modulus (μ.map T) h := by
    rw [← label_moment μ label hl cap (clippedGap h)]
    simp_rw [he]
    unfold modulus
    rw [integral_map hm.aemeasurable (measurable_clippedGap h).aestronglyMeasurable]
  have hdelta : cellDelta caps cell h = Δ := by
    unfold cellDelta
    rw [← e.sum_comp (fun i => cellWeight cell i * clippedGap h (caps i))]
    simp_rw [hw,hcaps]
    rw [replicated_moment (labelWeight μ label) (fun i => clippedGap h (cap i)) hM,hmoment]
  refine ⟨⟨N * M,caps,(fun u => (f u).1),cell,hf.fst,hc,
    outer_gap_law μ M f hf hflaw,?_,?_,?_⟩⟩
  · intro u
    rw [hcap]
    exact hup (f u).1
  · intro u
    rw [hcap]
    exact hclip (f u).1
  · rw [← e.sum_comp (fun i => (cellWeight cell i) ^ 2)]
    simp_rw [hw]
    exact (replicated_square_le (labelWeight μ label) (labelWeight_nonneg μ label)
      (labelWeight_sum μ label hl) hM).trans (hdelta.symm ▸ hcount)

end ThresholdHC.ObservedState
