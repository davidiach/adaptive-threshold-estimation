import ThresholdHC.BandwiseSuffix.Search
import ThresholdHC.BandCostSelection.Entropy

noncomputable section
open MeasureTheory
open scoped Classical
namespace ThresholdHC.GapLawMenus
open ThresholdHC.Tier6 ThresholdHC.EntropyTail ThresholdHC.BandwiseSuffix
open ThresholdHC.BandCostSelection

/-- One concrete menu per occupied band, containing exactly its upper-gap suffixes. -/
def menus (F : Finset Gap) (js : List ℕ) : List (Finset (Finset Gap)) :=
  js.map (fun j => suffixChoices (slice F j))

/-- A trace denotes the union of its actual selected atoms. -/
def traceSet : List (Finset Gap) → Finset Gap
  | [] => ∅
  | S::xs => S ∪ traceSet xs

theorem bandIndex_eq_of_mem {d : Gap} {j : ℕ} (hd : d ∈ band j) :
    bandIndex d = j := by
  by_contra h
  exact Set.disjoint_left.mp (band_disjoint h) (mem_index_band d) hd

theorem mem_traceSet {d : Gap} {xs : List (Finset Gap)} :
    d ∈ traceSet xs ↔ ∃ S ∈ xs, d ∈ S := by
  induction xs with
  | nil => simp [traceSet]
  | cons S xs ih => simp [traceSet,ih]

theorem suffix_slice {F S : Finset Gap} (hS : S ∈ suffixChoices F) (j : ℕ) :
    slice S j ∈ suffixChoices (slice F j) := by
  obtain ⟨hSF,hs⟩ := mem_suffixChoices.mp hS
  apply mem_suffixChoices.mpr
  refine ⟨Finset.filter_subset_filter _ hSF,?_⟩
  intro k x y hx hy hxk hyk hxy
  obtain ⟨hxS,hxj⟩ := Finset.mem_filter.mp hx
  obtain ⟨hyF,hyj⟩ := Finset.mem_filter.mp hy
  exact Finset.mem_filter.mpr ⟨hs k hxS hyF hxk hyk hxy,hyj⟩

theorem slice_suffix_global {F S : Finset Gap} {j : ℕ}
    (hS : S ∈ suffixChoices (slice F j)) : S ∈ suffixChoices F := by
  obtain ⟨hSF,hs⟩ := mem_suffixChoices.mp hS
  apply mem_suffixChoices.mpr
  refine ⟨hSF.trans (Finset.filter_subset _ _),?_⟩
  intro k x y hx hy hxk hyk hxy
  have hxj := (Finset.mem_filter.mp (hSF hx)).2
  have he : j=k := (bandIndex_eq_of_mem hxj).symm.trans (bandIndex_eq_of_mem hxk)
  subst k
  exact hs j hx (Finset.mem_filter.mpr ⟨hy,hyk⟩) hxj hyk hxy

theorem suffix_union {F S T : Finset Gap}
    (hS : S ∈ suffixChoices F) (hT : T ∈ suffixChoices F) :
    S ∪ T ∈ suffixChoices F := by
  obtain ⟨hSF,hs⟩ := mem_suffixChoices.mp hS
  obtain ⟨hTF,ht⟩ := mem_suffixChoices.mp hT
  apply mem_suffixChoices.mpr
  refine ⟨Finset.union_subset hSF hTF,?_⟩
  intro j x y hx hy hxj hyj hxy
  rcases Finset.mem_union.mp hx with hx|hx
  · exact Finset.mem_union_left _ (hs j hx hy hxj hyj hxy)
  · exact Finset.mem_union_right _ (ht j hx hy hxj hyj hxy)

/-- Every menu trace is a genuine global bandwise suffix on the supplied atoms. -/
theorem trace_suffix (F : Finset Gap) (js : List ℕ) {xs : List (Finset Gap)}
    (hx : xs ∈ enumerate (menus F js)) : traceSet xs ∈ suffixChoices F := by
  induction js generalizing xs with
  | nil =>
    have he : xs=[] := Finset.mem_singleton.mp hx
    subst xs
    apply mem_suffixChoices.mpr
    exact ⟨Finset.empty_subset _,fun _ _ _ hx => False.elim (Finset.notMem_empty _ hx)⟩
  | cons j js ih =>
    obtain ⟨tail,ht,S,hS,rfl⟩ := mem_extend.mp hx
    exact suffix_union (slice_suffix_global hS) (ih ht)

/-- The concrete trace obtained by slicing a global suffix is enumerated. -/
theorem slices_enumerated {F S : Finset Gap} (hS : S ∈ suffixChoices F) (js : List ℕ) :
    js.map (slice S) ∈ enumerate (menus F js) := by
  induction js with
  | nil => exact Finset.mem_singleton_self _
  | cons j js ih =>
    exact mem_extend.mpr ⟨_,ih,_,suffix_slice hS j,rfl⟩

theorem traceSet_slices {F S : Finset Gap} (hSF : S ⊆ F) (js : List ℕ)
    (hcover : ∀ d ∈ F, bandIndex d ∈ js) :
    traceSet (js.map (slice S)) = S := by
  ext d
  rw [mem_traceSet]
  constructor
  · rintro ⟨T,hT,hd⟩
    obtain ⟨j,_,rfl⟩ := List.mem_map.mp hT
    exact (Finset.mem_filter.mp hd).1
  · intro hd
    refine ⟨slice S (bandIndex d),List.mem_map.mpr ⟨_,hcover d (hSF hd),rfl⟩,?_⟩
    exact Finset.mem_filter.mpr ⟨hd,mem_index_band d⟩

/-- Concrete menu enumeration covers exactly all bandwise suffix selections. -/
theorem trace_image (F : Finset Gap) (js : List ℕ)
    (hcover : ∀ d ∈ F, bandIndex d ∈ js) :
    (enumerate (menus F js)).image traceSet = suffixChoices F := by
  ext S
  constructor
  · rintro h
    obtain ⟨xs,hxs,rfl⟩ := Finset.mem_image.mp h
    exact trace_suffix F js hxs
  · intro hS
    exact Finset.mem_image.mpr ⟨_,slices_enumerated hS js,
      traceSet_slices (mem_suffixChoices.mp hS).1 js hcover⟩

/-- Every selected atom belongs to one of the bands processed by the trace. -/
theorem trace_band_mem (F : Finset Gap) (js : List ℕ) {xs : List (Finset Gap)}
    (hx : xs ∈ enumerate (menus F js)) {d : Gap} (hd : d ∈ traceSet xs) :
    bandIndex d ∈ js := by
  induction js generalizing xs with
  | nil =>
    have he : xs=[] := Finset.mem_singleton.mp hx
    simp [he,traceSet] at hd
  | cons j js ih =>
    obtain ⟨tail,ht,S,hS,rfl⟩ := mem_extend.mp hx
    rcases Finset.mem_union.mp hd with hd|hd
    · have hdj := (Finset.mem_filter.mp ((mem_suffixChoices.mp hS).1 hd)).2
      exact List.mem_cons.mpr (Or.inl (bandIndex_eq_of_mem hdj))
    · exact List.mem_cons.mpr (Or.inr (ih ht hd))

/-- Options from distinct band positions never share an atom. -/
theorem head_disjoint_tail (F : Finset Gap) {j : ℕ} {js : List ℕ}
    (hj : j ∉ js) {S : Finset Gap} (hS : S ∈ suffixChoices (slice F j))
    {xs : List (Finset Gap)} (hx : xs ∈ enumerate (menus F js)) :
    Disjoint S (traceSet xs) := by
  apply Finset.disjoint_left.mpr
  intro d hd ht
  have hdj := (Finset.mem_filter.mp ((mem_suffixChoices.mp hS).1 hd)).2
  have hm := trace_band_mem F js hx ht
  rw [bandIndex_eq_of_mem hdj] at hm
  exact hj hm

/-- Before any cost compression, actual finite menus attain the original
selection objective against every fractional submeasure. -/
theorem menu_attains (μ : Measure Gap) [IsProbabilityMeasure μ]
    (hF : μ.support.Finite) (js : List ℕ)
    (hcover : ∀ d ∈ hF.toFinset, bandIndex d ∈ js)
    {ρ B : ℝ} (hr : 0 < ρ) (hu : ρ ≤ 1/4) (hB : 0 < B) :
    ∃ xs ∈ enumerate (menus hF.toFinset js), ∀ σ : Measure Gap, σ ≤ μ →
      selectionObjective μ ρ B (μ.restrict (traceSet xs)) ≤ selectionObjective μ ρ B σ := by
  obtain ⟨S,hS,hmin⟩ := search_attains μ hF hr hu hB
  have hmem : S ∈ (enumerate (menus hF.toFinset js)).image traceSet := by
    rw [trace_image _ _ hcover]
    exact hS
  obtain ⟨xs,hxs,rfl⟩ := Finset.mem_image.mp hmem
  exact ⟨xs,hxs,hmin⟩

end ThresholdHC.GapLawMenus

