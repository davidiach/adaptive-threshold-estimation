import ThresholdHC.ObservedState.Construction

/-! The replicated cell design of the proof of `prop:outer` (`paper/v6/core.tex`)
with the Hoeffding replication count `M = ⌈32 Δ⁻² log(2/δ)⌉₊`.

The construction is that of `ThresholdHC.ObservedState.cell_design_exists` with the
count chosen after the separation `Δ = ¼ ω_{T#μ}(h)`. The labels come from an
injective variant of `finite_range_labels`, so distinct labels carry distinct caps.
Separation, positivity and the envelope are read off an auxiliary `CellDesign` with
the same data, whose second-moment field holds with the parameter `16/Δ²`. -/
noncomputable section
open MeasureTheory Set
namespace ThresholdHC.ObservedHoeffding
open ThresholdHC.Tier6 ThresholdHC.ObservedState

/-- `finite_range_labels` with injective caps: every finite-range gap map has a finite
measurable labeling whose label caps are distinct and reconstruct the map exactly. -/
theorem injective_range_labels (T : Gap → Gap) (hm : Measurable T) (hF : (range T).Finite) :
    ∃ N : ℕ, 0 < N ∧ ∃ (cap : Fin N → Gap) (label : Gap → Fin N),
      Function.Injective cap ∧ Measurable label ∧ ∀ d, cap (label d) = T d := by
  classical
  let I := range T
  let : Fintype I := hF.fintype
  have : Nonempty I := ⟨⟨T ⟨1 / 2, by norm_num⟩, mem_range_self _⟩⟩
  let e := Fintype.equivFin I
  let cell (d : Gap) : I := ⟨T d, mem_range_self d⟩
  have hc : Measurable cell := hm.subtype_mk
  refine ⟨Fintype.card I, Fintype.card_pos, fun i => (e.symm i).val, e ∘ cell,
    Subtype.val_injective.comp e.symm.injective, (measurable_of_countable e).comp hc, ?_⟩
  intro d
  simp [cell]

/-- The replicated design with the Hoeffding count. Cell `(j,k)` has the cap `c j` of
its label and length `v j / M`, and `M = ⌈32 Δ⁻² log(2/δ)⌉₊` for `Δ = cellDelta`. -/
theorem hoeffding_design_exists (μ : Measure Gap) [IsProbabilityMeasure μ] (h : Gap)
    {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1 / 8) :
    ∃ (N M : ℕ) (c : Fin N → Gap) (v : Fin N → ℝ) (cap : Fin (N * M) → Gap)
      (gap : unitInterval → Gap) (cell : unitInterval → Fin (N * M)) (_ : Measurable cell),
      Measurable gap ∧ volume.map gap = μ ∧ (∀ u, gap u ≤ cap (cell u)) ∧
      Function.Injective c ∧ (∀ j, 0 ≤ v j) ∧ (∑ j, v j) = 1 ∧
      (∀ j k, cap (finProdFinEquiv (j, k)) = c j) ∧
      (∀ j k, cellWeight cell (finProdFinEquiv (j, k)) = v j / (M : ℝ)) ∧
      0 < M ∧ M = ⌈32 * Real.log (2 / δ) / (cellDelta cap cell h) ^ 2⌉₊ ∧
      (∑ i, (cellWeight cell i) ^ 2) ≤ 1 / (M : ℝ) ∧
      0 < cellDelta cap cell h ∧
      modulus μ h / 8 ≤ cellDelta cap cell h ∧
      (∀ x : ℝ, volume {u : unitInterval | (cap (cell u) : ℝ) ≤ x} ≤
        μ {d : Gap | (d : ℝ) ≤ x}) := by
  classical
  obtain ⟨T, hm, hfinite, hup, hclip⟩ := finite_upward_rounding h
  obtain ⟨N, _, cap, label, hinj, hl, he⟩ := injective_range_labels T hm hfinite
  have : IsProbabilityMeasure (μ.map T) :=
    (Measure.isProbabilityMeasure_map_iff hm.aemeasurable).mpr inferInstance
  let Δ := (1 / 4 : ℝ) * modulus (μ.map T) h
  have hΔ : 0 < Δ := mul_pos (by norm_num) (modulus_pos (μ.map T) h.property.1)
  have hlog : 0 < Real.log (2 / δ) := Real.log_pos (by rw [lt_div_iff₀ hδ]; linarith)
  let M := ⌈32 * Real.log (2 / δ) / Δ ^ 2⌉₊
  have hM : 0 < M := Nat.ceil_pos.mpr (by positivity)
  have : NeZero M := ⟨Nat.ne_of_gt hM⟩
  obtain ⟨f, hf, hflaw⟩ := outer_source μ M
  let e : Fin N × Fin M ≃ Fin (N * M) := finProdFinEquiv
  let cell : unitInterval → Fin (N * M) := fun u => e (label (f u).1, (f u).2)
  let caps : Fin (N * M) → Gap := fun i => cap (e.symm i).1
  have hc : Measurable cell := (measurable_of_countable e).comp ((hl.comp hf.fst).prodMk hf.snd)
  have hcaps (i : Fin N × Fin M) : caps (e i) = cap i.1 := by simp [caps]
  have hcap (u : unitInterval) : caps (cell u) = T (f u).1 := by
    rw [show cell u = e (label (f u).1, (f u).2) from rfl, hcaps, he]
  have hw (i : Fin N × Fin M) :
      cellWeight cell (e i) = replicatedWeight (labelWeight μ label) M i := by
    have hset : {u : unitInterval | cell u = e i} =
        {u : unitInterval | label (f u).1 = i.1 ∧ (f u).2 = i.2} := by
      ext u
      simp only [cell, mem_ofPred_eq, Equiv.apply_eq_iff_eq, Prod.ext_iff]
    change volume.real {u : unitInterval | cell u = e i} = _
    rw [hset, cell_mass μ M label hl f hf hflaw i.1 i.2]
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
    simp_rw [hw, hcaps]
    rw [replicated_moment (labelWeight μ label) (fun i => clippedGap h (cap i)) hM, hmoment]
  have hsq : (∑ i, (cellWeight cell i) ^ 2) ≤ 1 / (M : ℝ) := by
    rw [← e.sum_comp (fun i => (cellWeight cell i) ^ 2)]
    simp_rw [hw]
    exact replicated_square_le (labelWeight μ label) (labelWeight_nonneg μ label)
      (labelWeight_sum μ label hl) hM
  have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast hM
  let D : CellDesign μ h (16 / Δ ^ 2) := ⟨N * M, caps, (fun u => (f u).1), cell, hf.fst, hc,
    outer_gap_law μ M f hf hflaw, fun u => by rw [hcap]; exact hup (f u).1,
    fun u => by rw [hcap]; exact hclip (f u).1, by
      rw [hdelta, show 16 / Δ ^ 2 * Δ ^ 2 / 16 = 1 by field_simp]
      exact hsq.trans ((div_le_one (by positivity)).mpr hM1)⟩
  refine ⟨N, M, cap, labelWeight μ label, caps, (fun u => (f u).1), cell, hc, hf.fst,
    outer_gap_law μ M f hf hflaw, D.cap_bound, hinj, labelWeight_nonneg μ label,
    labelWeight_sum μ label hl, fun j k => hcaps (j, k), fun j k => hw (j, k), hM, ?_, hsq,
    design_delta_pos μ h _ D, design_separation μ h _ D, design_cdf μ h _ D⟩
  rw [hdelta]

end ThresholdHC.ObservedHoeffding
