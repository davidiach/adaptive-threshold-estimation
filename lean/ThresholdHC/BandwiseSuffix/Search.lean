import ThresholdHC.BandwiseSuffix.Full

noncomputable section
open MeasureTheory Set
open scoped BigOperators Classical
namespace ThresholdHC.BandwiseSuffix
open ThresholdHC.Tier6 (Gap)
open ThresholdHC.EntropyTail

/-- The canonical band of an atom. The bands are disjoint and cover the gap space. -/
def bandIndex (x : Gap) : ℕ := Classical.choose (exists_band x)

theorem mem_index_band (x : Gap) : x ∈ band (bandIndex x) := Classical.choose_spec (exists_band x)

def slice (F : Finset Gap) (j : ℕ) := F.filter (fun x => x ∈ band j)

def suffixChoices (F : Finset Gap) : Finset (Finset Gap) := by
  classical exact F.powerset.filter (fun S => IsBandSuffix F S)

theorem mem_suffixChoices {S F : Finset Gap} :
    S ∈ suffixChoices F ↔ S ⊆ F ∧ IsBandSuffix F S := by
  classical simp [suffixChoices]

/-- Two upward-closed selections in a single band are nested. -/
theorem slices_comparable {F S T : Finset Gap} (hS : S ∈ suffixChoices F) (hT : T ∈ suffixChoices F)
    (j : ℕ) : slice S j ⊆ slice T j ∨ slice T j ⊆ slice S j := by
  classical
  obtain ⟨sF,hs⟩ := mem_suffixChoices.mp hS
  obtain ⟨tF,ht⟩ := mem_suffixChoices.mp hT
  by_cases h : slice S j ⊆ slice T j
  · exact Or.inl h
  right
  obtain ⟨x,hxs,hxt⟩ := Finset.not_subset.mp h
  obtain ⟨hx,hxj⟩ := Finset.mem_filter.mp hxs
  intro y hy
  obtain ⟨hyt,hyj⟩ := Finset.mem_filter.mp hy
  refine Finset.mem_filter.mpr ⟨?_,hyj⟩
  rcases lt_trichotomy x y with hxy | rfl | hyx
  · exact hs j hx (tF hyt) hxj hyj hxy
  · exact hx
  · exact (hxt (Finset.mem_filter.mpr ⟨ht j hyt (sF hx) hyj hxj hyx, hxj⟩)).elim

/-- Encode a suffix by its selected cardinality in each occupied band. -/
theorem suffixChoices_card_le (F : Finset Gap) :
    (suffixChoices F).card ≤ ∏ j ∈ F.image bandIndex, ((slice F j).card + 1) := by
  classical
  let J := F.image bandIndex
  let code (S : ↥(suffixChoices F)) (j : J) : Fin ((slice F j).card + 1) :=
    ⟨(slice S.val j).card, Nat.lt_succ_of_le (Finset.card_le_card
      (Finset.filter_subset_filter _ (mem_suffixChoices.mp S.property).1))⟩
  have hi : Function.Injective code := by
    intro S T h
    have he {j : ℕ} (hj : j ∈ J) : slice S.val j = slice T.val j := by
      have hc := congrArg Fin.val (congrFun h ⟨j,hj⟩)
      change (slice S.val j).card = (slice T.val j).card at hc
      rcases slices_comparable S.property T.property j with hs | ht
      · exact Finset.eq_of_subset_of_card_le hs hc.ge
      · exact (Finset.eq_of_subset_of_card_le ht hc.le).symm
    apply Subtype.ext
    ext x
    have member (A : ↥(suffixChoices F)) (hx : x ∈ A.val) : bandIndex x ∈ J :=
      Finset.mem_image_of_mem _ ((mem_suffixChoices.mp A.property).1 hx)
    constructor
    · intro hx
      have hm : x ∈ slice S.val (bandIndex x) := Finset.mem_filter.mpr ⟨hx,mem_index_band x⟩
      rw [he (member S hx)] at hm
      exact (Finset.mem_filter.mp hm).1
    · intro hx
      have hm : x ∈ slice T.val (bandIndex x) := Finset.mem_filter.mpr ⟨hx,mem_index_band x⟩
      rw [← he (member T hx)] at hm
      exact (Finset.mem_filter.mp hm).1
  calc
    (suffixChoices F).card ≤ ∏ j : J, ((slice F j).card + 1) := by
      simpa only [Fintype.card_coe, Fintype.card_pi, Fintype.card_fin]
        using Fintype.card_le_of_injective code hi
    _ = _ := Finset.prod_coe_sort J (fun j => (slice F j).card + 1)

/-- The sufficient candidate family contains a minimizer against all submeasures. -/
theorem search_attains (μ : Measure Gap) [IsProbabilityMeasure μ] (hF : μ.support.Finite)
    {ρ B : ℝ} (hρ : 0 < ρ) (hr : ρ ≤ 1/4) (hB : 0 < B) :
    ∃ S ∈ suffixChoices hF.toFinset, ∀ σ : Measure Gap, σ ≤ μ →
      selectionObjective μ ρ B (μ.restrict S) ≤ selectionObjective μ ρ B σ := by
  obtain ⟨S,hs,hsuf,hmin,_⟩ := bandwise_suffix μ hF hρ hr hB
  refine ⟨S,mem_suffixChoices.mpr ⟨fun x hx => hF.mem_toFinset.mpr (hs hx), ?_⟩,hmin⟩
  simpa only [hF.coe_toFinset] using hsuf

end ThresholdHC.BandwiseSuffix
