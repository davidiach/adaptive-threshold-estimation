import ThresholdHC.BandwiseSuffix.Search
import ThresholdHC.EntropyTailQuantile.BandGeometry
import ThresholdHC.EntropyTail.Bridge
import Mathlib.MeasureTheory.Function.Floor

noncomputable section
open MeasureTheory Set Real
open scoped ENNReal
namespace ThresholdHC.SelectionStability
open ThresholdHC.Tier6 (Gap)
open ThresholdHC.EntropyTail
open ThresholdHC.BandwiseSuffix (bandIndex mem_index_band)
open ThresholdHC.EntropyTailQuantile (bandEdge bandEdge_pos bandEdge_antitone exists_band_cutoff)

/-- For a positive gap the containing band is unique, including its right endpoint. -/
theorem index_eq_iff (x : Gap) (j : ℕ) : bandIndex x = j ↔ x ∈ band j := by
  constructor
  · exact fun h => h ▸ mem_index_band x
  · intro hx
    by_contra hn
    exact Set.disjoint_left.mp (band_disjoint hn) (mem_index_band x) hx

theorem measurable_index : Measurable bandIndex := by
  apply measurable_to_countable'
  intro j
  have he : bandIndex ⁻¹' {j} = band j := Set.ext fun x => index_eq_iff x j
  rw [he]; exact measurableSet_band j

/-- Round onto an equally spaced mesh above t and cap each rounded value at its original
band edge. Gaps below t stay fixed, so the same map respects every band on the full space. -/
theorem finite_rounding_grid (t : Gap) {r : ℝ} (hr : 1 < r) :
    ∃ T : Gap → Gap, Measurable T ∧
      (∀ d : Gap, (d:ℝ) ≤ (T d:ℝ) ∧ (T d:ℝ) ≤ r*(d:ℝ)) ∧
      (∀ j, T ⁻¹' band j = band j) ∧ (T '' Ici t).Finite := by
  classical
  let step := (r-1)*(t:ℝ)
  have hstep : 0 < step := mul_pos (sub_pos.mpr hr) t.property.1
  let k := fun x : Gap => ⌈(x:ℝ)/step⌉₊
  let mesh := fun x : Gap => (k x:ℝ)*step
  let edge := fun x : Gap => bandEdge (bandIndex x)
  let val := fun x : Gap => if t ≤ x then min (edge x) (mesh x) else (x:ℝ)
  have hband (x : Gap) : edge x / 2 < (x:ℝ) ∧ (x:ℝ) ≤ edge x := by
    have hm := mem_index_band x
    rw [← quantile_band_eq] at hm
    exact hm
  have hbnd (x : Gap) : (x:ℝ) ≤ val x ∧ val x ≤ edge x ∧ val x ≤ r*(x:ℝ) := by
    have hxe := (hband x).2
    dsimp only [val]
    split_ifs with h
    · have h₁ := (div_le_iff₀ hstep).mp (Nat.le_ceil ((x:ℝ)/step))
      have h₂ := mul_le_mul_of_nonneg_right
        (Nat.ceil_lt_add_one (div_nonneg x.property.1.le hstep.le)).le hstep.le
      rw [add_mul, div_mul_cancel₀ _ hstep.ne', one_mul] at h₂
      refine ⟨le_min hxe h₁, min_le_left _ _, (min_le_right _ _).trans ?_⟩
      change (k x:ℝ)*step ≤ r*(x:ℝ)
      have h₃ := mul_le_mul_of_nonneg_left (show (t:ℝ) ≤ (x:ℝ) from h) (sub_nonneg.mpr hr.le)
      change (k x:ℝ)*step ≤ (x:ℝ)+step at h₂
      change step ≤ (r-1)*(x:ℝ) at h₃
      linarith only [h₂,h₃]
    · exact ⟨le_rfl,hxe,le_mul_of_one_le_left x.property.1.le hr.le⟩
  let T (x : Gap) : Gap := ⟨val x, x.property.1.trans_le (hbnd x).1,
    (hbnd x).2.1.trans ((bandEdge_antitone (Nat.zero_le _)).trans (by norm_num [bandEdge]))⟩
  have he : Measurable edge := (measurable_of_countable bandEdge).comp measurable_index
  have hk : Measurable k := Nat.measurable_ceil.comp (measurable_subtype_coe.div_const step)
  have hm : Measurable mesh := by dsimp only [mesh]; fun_prop
  refine ⟨T, ?_, fun x => ⟨(hbnd x).1,(hbnd x).2.2⟩, ?_, ?_⟩
  · apply Measurable.subtype_mk
    exact (he.min hm).ite measurableSet_Ici measurable_subtype_coe
  · intro j
    ext x
    have hb : T x ∈ band (bandIndex x) := by
      rw [← quantile_band_eq]
      exact ⟨(hband x).1.trans_le (hbnd x).1,(hbnd x).2.1⟩
    change T x ∈ band j ↔ x ∈ band j
    rw [← index_eq_iff, ← index_eq_iff, (index_eq_iff _ _).mpr hb]
  · obtain ⟨N,hN,_⟩ := exists_band_cutoff t.property.1
    let K := ⌈(1/2:ℝ)/step⌉₊
    let F := range (fun j : Fin N => bandEdge j) ∪ range (fun i : Fin (K+1) => (i:ℕ)*step)
    have hF : F.Finite := (finite_range _).union (finite_range _)
    apply (hF.preimage (f := (Subtype.val : Gap → ℝ)) Subtype.val_injective.injOn).subset
    rintro _ ⟨x,hx,rfl⟩
    change val x ∈ F
    simp only [val, ite_eq_left (show t ≤ x from hx)]
    by_cases h : edge x ≤ mesh x
    · rw [min_eq_left h]
      have hj : bandIndex x < N := by
        by_contra! hj
        exact (not_lt_of_ge ((show (t:ℝ) ≤ (x:ℝ) from hx).trans (hband x).2))
          ((bandEdge_antitone hj).trans_lt hN)
      exact Or.inl ⟨⟨_,hj⟩,rfl⟩
    · rw [min_eq_right (le_of_not_ge h)]
      have hkx : k x ≤ K := Nat.ceil_mono (div_le_div_of_nonneg_right x.property.2 hstep.le)
      exact Or.inr ⟨⟨_,Nat.lt_succ_of_le hkx⟩,rfl⟩

end ThresholdHC.SelectionStability
