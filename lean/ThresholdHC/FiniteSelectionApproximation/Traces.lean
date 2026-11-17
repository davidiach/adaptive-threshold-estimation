import ThresholdHC.FiniteSelectionApproximation.Parameters
import ThresholdHC.SelectionApproximation.Entropy
import ThresholdHC.SelectionApproximation.Compression
import ThresholdHC.BandCostSelection.Entropy

noncomputable section
open scoped Classical BigOperators
namespace ThresholdHC.FiniteSelectionApproximation
open ThresholdHC.BandCostSelection ThresholdHC.SelectionApproximation
open ThresholdHC.EntropyTailQuantile

variable {α : Type*}

def options (menus : List (Finset α)) : Finset α := menus.foldr (· ∪ ·) ∅

def positiveCosts (a : α → ℝ) (menus : List (Finset α)) : Finset ℝ :=
  ((options menus).image a).filter (0 < ·)

/-- Least positive option cost; the fallback only applies to a degenerate menu problem. -/
def minCost (a : α → ℝ) (menus : List (Finset α)) : ℝ :=
  if h : (positiveCosts a menus).Nonempty then (positiveCosts a menus).min' h else 1

def menuMax (a : α → ℝ) (menu : Finset α) : ℝ :=
  (insert 0 (menu.image a)).max' (Finset.insert_nonempty _ _)

/-- Sum of the largest cost in each menu, including the empty option. -/
def maxCost (a : α → ℝ) (menus : List (Finset α)) : ℝ :=
  (menus.map (menuMax a)).sum

def summary (a : α → ℝ) (r ε : ℝ) (x : α) : ℝ := a x*(1+upperLog r ε (a x))

theorem mem_options {x : α} {menus : List (Finset α)} :
    x ∈ options menus ↔ ∃ menu ∈ menus, x ∈ menu := by
  induction menus with
  | nil => simp [options]
  | cons menu rest ih =>
    change x ∈ menu ∪ options rest ↔ _
    simp [ih]

theorem trace_mem_options {menus : List (Finset α)} {xs : List α}
    (hx : xs ∈ enumerate menus) {x : α} (hm : x ∈ xs) : x ∈ options menus := by
  induction menus generalizing xs with
  | nil => have he := Finset.mem_singleton.mp hx; simp [he] at hm
  | cons menu rest ih =>
    obtain ⟨ys,hy,y,hym,rfl⟩ := mem_extend.mp hx
    rcases List.mem_cons.mp hm with rfl | hrest
    · simp [options, hym]
    · exact Finset.mem_union_right _ (ih hy hrest)

theorem minCost_pos (a : α → ℝ) (menus : List (Finset α)) : 0 < minCost a menus := by
  unfold minCost
  split_ifs with h
  · exact (Finset.mem_filter.mp (Finset.min'_mem _ h)).2
  · norm_num

theorem minCost_le {a : α → ℝ} {menus : List (Finset α)} {x : α}
    (hx : x ∈ options menus) (ha : 0 < a x) : minCost a menus ≤ a x := by
  have hm : a x ∈ positiveCosts a menus := Finset.mem_filter.mpr ⟨Finset.mem_image_of_mem _ hx,ha⟩
  rw [minCost, dite_eq_left ⟨_,hm⟩]
  exact Finset.min'_le _ _ hm

theorem menuMax_nonneg (a : α → ℝ) (menu : Finset α) : 0 ≤ menuMax a menu :=
  Finset.le_max' _ _ (Finset.mem_insert_self _ _)

theorem le_menuMax {a : α → ℝ} {menu : Finset α} {x : α} (hx : x ∈ menu) :
    a x ≤ menuMax a menu :=
  Finset.le_max' _ _ (Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ hx))

theorem maxCost_nonneg (a : α → ℝ) (menus : List (Finset α)) : 0 ≤ maxCost a menus := by
  induction menus with
  | nil => simp [maxCost]
  | cons menu rest ih => simpa [maxCost] using add_nonneg (menuMax_nonneg a menu) ih

theorem trace_le_maxCost {a : α → ℝ} {menus : List (Finset α)} {xs : List α}
    (hx : xs ∈ enumerate menus) : traceSaved a xs ≤ maxCost a menus := by
  induction menus generalizing xs with
  | nil => have he := Finset.mem_singleton.mp hx; simp [he,traceSaved,maxCost]
  | cons menu rest ih =>
    obtain ⟨ys,hy,y,hym,rfl⟩ := mem_extend.mp hx
    simpa [traceSaved,maxCost] using add_le_add (le_menuMax hym) (ih hy)

theorem traceTotal (a : α → ℝ) (xs : List α) :
    costTotal (fun i : Fin xs.length => a (xs.get i)) = traceSaved a xs := by
  have he : List.ofFn (fun i : Fin xs.length => a (xs.get i)) = xs.map a := by
    rw [← Function.comp_def,← List.map_ofFn,List.ofFn_get]
  unfold costTotal
  rw [← List.sum_ofFn,he]
  rfl

theorem traceEntropy (a : α → ℝ) (xs : List α) :
    costEntropy (fun i : Fin xs.length => a (xs.get i)) = multisetEntropy (traceKey a xs) := by
  rw [← multisetEntropy_ofFn]
  congr 1
  simp [traceKey]

theorem trace_zero_or_lower {a : α → ℝ} (ha : ∀ x, 0 ≤ a x)
    {menus : List (Finset α)} {xs : List α} (hx : xs ∈ enumerate menus) :
    traceSaved a xs = 0 ∨ minCost a menus ≤ traceSaved a xs := by
  by_cases hz : traceSaved a xs = 0
  · exact Or.inl hz
  right
  have hne : ∃ i : Fin xs.length, a (xs.get i) ≠ 0 := by
    by_contra h
    push Not at h
    have ht : costTotal (fun i : Fin xs.length => a (xs.get i)) = 0 :=
      Finset.sum_eq_zero (fun i _ => h i)
    exact hz ((traceTotal a xs).symm.trans ht)
  obtain ⟨i,hi⟩ := hne
  exact (minCost_le (trace_mem_options hx (List.get_mem _ _))
    (lt_of_le_of_ne (ha _) (Ne.symm hi))).trans (by
      rw [← traceTotal]
      exact le_costTotal (fun _ => ha _) i)

theorem summary_nonneg {a : α → ℝ} (ha : ∀ x, 0 ≤ a x) {r ε : ℝ}
    (hε : 0 ≤ ε) (x : α) : 0 ≤ summary a r ε x :=
  mul_nonneg (ha x) (by linarith [upperLog_nonneg (r := r) (a := a x) hε])

theorem trace_summary_bounds {a : α → ℝ} (ha : ∀ x, 0 ≤ a x)
    {menus : List (Finset α)} {xs : List α} (hx : xs ∈ enumerate menus)
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hR : 1 ≤ maxCost a menus / minCost a menus) :
    let r := minCost a menus
    let L := logScale (maxCost a menus/r)
    let A := traceSaved a xs
    let H := traceSaved (summary a r ε) xs
    let v := fun i : Fin xs.length => a (xs.get i)
    baseSummary r v ≤ H ∧ H ≤ baseSummary r v+(ε/8)*A ∧ A ≤ H ∧ H ≤ L*A := by
  dsimp
  let r := minCost a menus
  let U := maxCost a menus
  let v := fun i : Fin xs.length => a (xs.get i)
  have hr : 0 < r := minCost_pos a menus
  have hl (i : Fin xs.length) (hi : v i ≠ 0) : r ≤ v i :=
    minCost_le (trace_mem_options hx (List.get_mem _ _)) (lt_of_le_of_ne (ha _) (Ne.symm hi))
  have hU : costTotal v ≤ U := (traceTotal a xs).trans_le (trace_le_maxCost hx)
  have hderiv := logScale_derivative hR
  have hb := surrogate_bounds (a := v) (u := fun i => upperLog r ε (v i))
    (fun _ => ha _) hr hl hU (show 0 ≤ ε/8 by positivity)
    (show 1+Real.log (U/r)+ε/8 ≤ logScale (U/r) by linarith)
    (fun i hi => upperLog_bounds hr hε (hl i hi))
  have he : (∑ i : Fin xs.length, v i*(1+upperLog r ε (v i))) =
      traceSaved (summary a r ε) xs := traceTotal (summary a r ε) xs
  rw [he,traceTotal] at hb
  refine ⟨hb.1,hb.2.1,?_,hb.2.2.2⟩
  rw [← traceTotal a xs,← traceTotal (summary a r ε) xs]
  apply Finset.sum_le_sum
  intro i _
  change a (xs.get i) ≤ a (xs.get i)*(1+upperLog r ε (a (xs.get i)))
  have hp := mul_nonneg (ha (xs.get i)) (upperLog_nonneg (r := r) hε.le (a := a (xs.get i)))
  nlinarith only [hp]

end ThresholdHC.FiniteSelectionApproximation
