import ThresholdHC.GapLawMenus.Menus
import ThresholdHC.GapLawMenus.FiniteEntropy

noncomputable section
open MeasureTheory
open scoped BigOperators ENNReal Classical
namespace ThresholdHC.GapLawMenus
open ThresholdHC.Tier6 ThresholdHC.EntropyTail ThresholdHC.BandwiseSuffix
open ThresholdHC.BandCostSelection

def costMass (μ : Measure Gap) (S : Finset Gap) : ℝ≥0∞ :=
  ∫⁻ d in (S : Set Gap), ENNReal.ofReal (((d:ℝ)⁻¹)^2) ∂μ

def cost (μ : Measure Gap) (S : Finset Gap) : ℝ := (costMass μ S).toReal

def saving (μ : Measure Gap) (h : ℝ) (S : Finset Gap) : ℝ :=
  (tailCost (μ.restrict S) h).toReal

theorem costMass_band (μ : Measure Gap) (S : Finset Gap) (j : ℕ)
    (hs : ∀ d ∈ S, d ∈ band j) :
    costMass μ S = bandCost (μ.restrict S) j := by
  unfold costMass bandCost
  rw [Measure.restrict_restrict (measurableSet_band j),
    Set.inter_eq_right.mpr (show (S : Set Gap) ⊆ band j from hs)]

theorem bandCost_restrict_zero (μ : Measure Gap) (S : Finset Gap) (j : ℕ)
    (hs : ∀ d ∈ S, d ∉ band j) :
    bandCost (μ.restrict S) j = 0 := by
  have he : band j ∩ (S : Set Gap) = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro d hd
    exact hs d hd.2 hd.1
  simp only [bandCost,Measure.restrict_restrict (measurableSet_band j),he,
    Measure.restrict_empty,lintegral_zero_measure]

theorem trace_bandCost_zero (μ : Measure Gap) (F : Finset Gap)
    (js : List ℕ) {xs : List (Finset Gap)}
    (hx : xs ∈ enumerate (menus F js)) {j : ℕ} (hj : j ∉ js) :
    bandCost (μ.restrict (traceSet xs)) j = 0 := by
  apply bandCost_restrict_zero
  intro d hd hdj
  have hm := trace_band_mem F js hx hd
  rw [bandIndex_eq_of_mem hdj] at hm
  exact hj hm

theorem trace_restrict_cons (μ : Measure Gap) (F : Finset Gap) {j : ℕ} {js : List ℕ}
    (hj : j ∉ js) {S : Finset Gap} (hS : S ∈ suffixChoices (slice F j))
    {xs : List (Finset Gap)} (hx : xs ∈ enumerate (menus F js)) :
    μ.restrict (traceSet (S::xs)) = μ.restrict S + μ.restrict (traceSet xs) := by
  have hd := head_disjoint_tail F hj hS hx
  rw [traceSet,Finset.coe_union]
  exact Measure.restrict_union
    (Set.disjoint_left.mpr (Finset.disjoint_left.mp hd)) (traceSet xs).measurableSet

theorem bandCost_add (σ τ : Measure Gap) (j : ℕ) :
    bandCost (σ+τ) j = bandCost σ j+bandCost τ j := by
  simp only [bandCost,Measure.restrict_add,lintegral_add_measure]

/-- The concrete cost list is exactly the vector of inverse-square band costs
of the selected measure, in the supplied band order. -/
theorem trace_costs (μ : Measure Gap) (F : Finset Gap) (js : List ℕ) (hj : js.Nodup)
    {xs : List (Finset Gap)} (hx : xs ∈ enumerate (menus F js)) :
    xs.map (cost μ) = js.map (fun j => (bandCost (μ.restrict (traceSet xs)) j).toReal) := by
  induction js generalizing xs with
  | nil =>
    have he : xs=[] := Finset.mem_singleton.mp hx
    simp [he]
  | cons j js ih =>
    obtain ⟨tail,ht,S,hS,rfl⟩ := mem_extend.mp hx
    obtain ⟨hnot,hnd⟩ := List.nodup_cons.mp hj
    have hSj : ∀ d ∈ S, d ∈ band j := fun d hd =>
      (Finset.mem_filter.mp ((mem_suffixChoices.mp hS).1 hd)).2
    have hhead : bandCost (μ.restrict (traceSet (S::tail))) j = costMass μ S := by
      rw [trace_restrict_cons μ F hnot hS ht,bandCost_add,
        trace_bandCost_zero μ F js ht hnot,add_zero,← costMass_band μ S j hSj]
    have htail : js.map (fun k => (bandCost (μ.restrict (traceSet (S::tail))) k).toReal) =
        js.map (fun k => (bandCost (μ.restrict (traceSet tail)) k).toReal) := by
      apply List.map_congr_left
      intro k hk
      have hkj : k ≠ j := by intro he; subst k; exact hnot hk
      have hz : bandCost (μ.restrict S) k = 0 := by
        apply bandCost_restrict_zero
        intro d hd hdk
        exact Set.disjoint_left.mp (band_disjoint hkj) hdk (hSj d hd)
      rw [trace_restrict_cons μ F hnot hS ht,bandCost_add,hz,zero_add]
    simp only [List.map_cons,hhead]
    rw [htail,← ih hnd ht]
    rfl

theorem trace_gamma (μ : Measure Gap) [IsFiniteMeasure μ]
    (F : Finset Gap) (js : List ℕ) (hj : js.Nodup)
    {xs : List (Finset Gap)} (hx : xs ∈ enumerate (menus F js)) :
    gamma (μ.restrict (traceSet xs)) =
      ENNReal.ofReal (multisetEntropy ((traceKey (cost μ) xs))) := by
  rw [gamma_list _ js hj (fun j h => trace_bandCost_zero μ F js hx h)]
  unfold traceKey
  rw [trace_costs μ F js hj hx]

theorem tailCost_ne_top (μ : Measure Gap) [IsFiniteMeasure μ] (h : ℝ) :
    tailCost μ h ≠ ⊤ := ne_top_of_le_ne_top (measure_ne_top μ _) (tailCost_le_mass _ _)

/-- The sum of actual menu savings is precisely the removed ordinary tail cost. -/
theorem trace_saving (μ : Measure Gap) [IsFiniteMeasure μ] (h : ℝ)
    (F : Finset Gap) (js : List ℕ) (hj : js.Nodup)
    {xs : List (Finset Gap)} (hx : xs ∈ enumerate (menus F js)) :
    traceSaved (saving μ h) xs = (tailCost (μ.restrict (traceSet xs)) h).toReal := by
  induction js generalizing xs with
  | nil =>
    have he : xs=[] := Finset.mem_singleton.mp hx
    simp [he,traceSaved,traceSet,tailCost_zero]
  | cons j js ih =>
    obtain ⟨tail,ht,S,hS,rfl⟩ := mem_extend.mp hx
    obtain ⟨hnot,hnd⟩ := List.nodup_cons.mp hj
    rw [trace_restrict_cons μ F hnot hS ht]
    change saving μ h S + traceSaved (saving μ h) tail =
      (tailCost (μ.restrict S+μ.restrict (traceSet tail)) h).toReal
    rw [show tailCost (μ.restrict S+μ.restrict (traceSet tail)) h =
        tailCost (μ.restrict S) h+tailCost (μ.restrict (traceSet tail)) h by
      simp only [tailCost,lintegral_add_measure],
      ENNReal.toReal_add (tailCost_ne_top _ _) (tailCost_ne_top _ _),ih hnd ht]
    rfl

end ThresholdHC.GapLawMenus

