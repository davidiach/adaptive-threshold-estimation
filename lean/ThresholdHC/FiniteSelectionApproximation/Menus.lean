import ThresholdHC.FiniteSelectionApproximation.Traces
import ThresholdHC.GapLawMenus.Atoms

noncomputable section
open MeasureTheory
open scoped Classical BigOperators ENNReal
namespace ThresholdHC.FiniteSelectionApproximation
open ThresholdHC.Tier6 ThresholdHC.EntropyTail ThresholdHC.BandwiseSuffix
open ThresholdHC.BandCostSelection ThresholdHC.GapLawMenus

def lawMenus (μ : Measure Gap) (hF : μ.support.Finite) : List (Finset (Finset Gap)) :=
  menus hF.toFinset (occupiedBands hF.toFinset)

theorem empty_suffix (F : Finset Gap) : ∅ ∈ suffixChoices F :=
  mem_suffixChoices.mpr ⟨Finset.empty_subset _,fun _ _ _ hx => False.elim (Finset.notMem_empty _ hx)⟩

theorem self_suffix (F : Finset Gap) : F ∈ suffixChoices F :=
  mem_suffixChoices.mpr ⟨Finset.Subset.refl _,fun _ _ _ _ hy _ _ _ => hy⟩

theorem lawMenus_empty_option (μ : Measure Gap) (hF : μ.support.Finite) :
    ∀ menu ∈ lawMenus μ hF, ∅ ∈ menu := by
  intro menu hm
  obtain ⟨j,_,rfl⟩ := List.mem_map.mp hm
  exact empty_suffix _

theorem cost_empty (μ : Measure Gap) : cost μ ∅ = 0 := by simp [cost,costMass]

theorem positive_support_cost (μ : Measure Gap) [IsProbabilityMeasure μ] (hF : μ.support.Finite)
    {S : Finset Gap} (hS : S ⊆ hF.toFinset) (hne : S.Nonempty) : 0 < cost μ S := by
  obtain ⟨d,hd⟩ := hne
  rw [cost_atomic]
  apply lt_of_lt_of_le (b := (μ {d}).toReal*((d:ℝ)⁻¹)^2)
  · have hw : 0 < (μ {d}).toReal := ENNReal.toReal_pos
      (ne_of_gt (support_atom_pos hF (hF.mem_toFinset.mp (hS hd)))) (measure_ne_top μ _)
    exact mul_pos hw (sq_pos_of_pos (inv_pos.mpr d.property.1))
  · exact Finset.single_le_sum (fun x _ => show 0 ≤ (μ {x}).toReal*((x:ℝ)⁻¹)^2 by positivity) hd

theorem menuMax_le_maxCost {α : Type*} (a : α → ℝ) {menu : Finset α}
    {ms : List (Finset α)} (hm : menu ∈ ms) : menuMax a menu ≤ maxCost a ms := by
  induction ms with
  | nil => simp at hm
  | cons first rest ih =>
    rcases List.mem_cons.mp hm with rfl | h
    · simpa [maxCost] using le_add_of_nonneg_right (a := menuMax a menu) (maxCost_nonneg a rest)
    · have hi := ih h
      have hn := menuMax_nonneg a first
      simp only [maxCost,List.map_cons,List.sum_cons] at *
      linarith

/-- The finite probability law constructs a nondegenerate input range; no cost
ratio or nonempty-menu premise is left to the final approximation theorem. -/
theorem lawMenus_input (μ : Measure Gap) [IsProbabilityMeasure μ] (hF : μ.support.Finite) :
    0 < (lawMenus μ hF).length ∧ 1 ≤ maxCost (cost μ) (lawMenus μ hF)/minCost (cost μ) (lawMenus μ hF) := by
  obtain ⟨d,hd⟩ := μ.nonempty_support (by
    intro hzero
    have hmass : μ Set.univ = 1 := measure_univ
    simp [hzero] at hmass)
  let S := slice hF.toFinset (bandIndex d)
  have hdF : d ∈ hF.toFinset := hF.mem_toFinset.mpr hd
  have hdS : d ∈ S := Finset.mem_filter.mpr ⟨hdF,mem_index_band d⟩
  have hopt : S ∈ suffixChoices S := self_suffix S
  have hm : suffixChoices S ∈ lawMenus μ hF := List.mem_map.mpr
    ⟨bandIndex d,Finset.mem_toList.mpr (Finset.mem_image_of_mem _ hdF),rfl⟩
  have hc : 0 < cost μ S := positive_support_cost μ hF (Finset.filter_subset _ _) ⟨d,hdS⟩
  have hmin : minCost (cost μ) (lawMenus μ hF) ≤ cost μ S :=
    minCost_le (mem_options.mpr ⟨_,hm,hopt⟩) hc
  have hmax : cost μ S ≤ maxCost (cost μ) (lawMenus μ hF) :=
    (le_menuMax hopt).trans (menuMax_le_maxCost (cost μ) hm)
  refine ⟨Nat.pos_of_ne_zero (fun hz => List.ne_nil_of_mem hm (List.length_eq_zero_iff.mp hz)),?_⟩
  exact (le_div_iff₀ (minCost_pos _ _)).mpr (by simpa using hmin.trans hmax)

theorem slice_eq_self_of_subset {F S : Finset Gap} {j : ℕ} (hS : S ⊆ slice F j) : slice S j = S := by
  ext d
  simp only [slice,Finset.mem_filter]
  exact ⟨And.left,fun hd => ⟨hd,(Finset.mem_filter.mp (hS hd)).2⟩⟩

/-- A menu contains at most one suffix of each cardinality, hence at most `n_j+1` options. -/
theorem one_band_options (F : Finset Gap) (j : ℕ) :
    (suffixChoices (slice F j)).card ≤ (slice F j).card+1 := by
  let code (S : ↥(suffixChoices (slice F j))) : Fin ((slice F j).card+1) :=
    ⟨S.val.card,Nat.lt_succ_of_le (Finset.card_le_card (mem_suffixChoices.mp S.property).1)⟩
  have hi : Function.Injective code := by
    intro S T he
    have hc : S.val.card = T.val.card := congrArg Fin.val he
    have hs : slice S.val j = S.val := slice_eq_self_of_subset (mem_suffixChoices.mp S.property).1
    have ht : slice T.val j = T.val := slice_eq_self_of_subset (mem_suffixChoices.mp T.property).1
    have hcomp := slices_comparable S.property T.property j
    rw [hs,ht] at hcomp
    apply Subtype.ext
    rcases hcomp with hst | hts
    · exact Finset.eq_of_subset_of_card_le hst hc.ge
    · exact (Finset.eq_of_subset_of_card_le hts hc.le).symm
  simpa using Fintype.card_le_of_injective code hi

theorem slice_eq_fiber (F : Finset Gap) (j : ℕ) : slice F j = F.filter (fun d => bandIndex d = j) := by
  ext d
  simp only [slice,Finset.mem_filter]
  constructor
  · exact fun h => ⟨h.1,bandIndex_eq_of_mem h.2⟩
  · intro h
    exact ⟨h.1,h.2 ▸ mem_index_band d⟩

/-- The total number of menu options is bounded by the advertised `Q=n+m`. -/
theorem lawMenus_option_count (μ : Measure Gap) (hF : μ.support.Finite) :
    ((lawMenus μ hF).map Finset.card).sum ≤ hF.toFinset.card+(occupiedBands hF.toFinset).length := by
  let F := hF.toFinset
  let J := F.image bandIndex
  have hsum : (∑ j ∈ J, (slice F j).card) = F.card := by
    simp only [slice_eq_fiber]
    exact (Finset.card_eq_sum_card_image bandIndex F).symm
  change ((J.toList.map (fun j => suffixChoices (slice F j))).map Finset.card).sum ≤ F.card+J.toList.length
  rw [List.map_map,Finset.sum_map_toList,Finset.length_toList]
  calc
    (∑ j ∈ J, (suffixChoices (slice F j)).card) ≤ ∑ j ∈ J, ((slice F j).card+1) :=
      Finset.sum_le_sum (fun j _ => one_band_options F j)
    _ = F.card+J.card := by rw [Finset.sum_add_distrib,hsum]; simp

end ThresholdHC.FiniteSelectionApproximation
