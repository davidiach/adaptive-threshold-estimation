import ThresholdHC.ArbitraryLawAdaptation.BandGeometry
import ThresholdHC.ArbitraryLawAdaptation.TransportCells
import ThresholdHC.EntropyTail.HardSelection

/-! Construct the band cells of an increasing-gap coupling. Every destination
column is summable because its band is bounded away from zero. -/

noncomputable section
open MeasureTheory
open scoped ENNReal BigOperators
namespace ThresholdHC.ArbitraryLawAdaptation
open ThresholdHC.Tier6 (Gap)
open ThresholdHC.EntropyTail

def inverseWeight (d : Gap) : ℝ≥0∞ := ENNReal.ofReal ((d : ℝ)⁻¹^2)

theorem measurable_inverseWeight : Measurable inverseWeight := by
  unfold inverseWeight; fun_prop

def transportTag (z : Gap × Gap) : ℕ × ℕ :=
  (bandIndex z.1, bandIndex z.1-bandIndex z.2)

def transportDest (x : ℕ × ℕ) : ℕ := x.1-x.2

theorem measurable_transportTag : Measurable transportTag :=
  (measurable_of_countable (fun p : ℕ × ℕ => (p.1,p.1-p.2))).comp
    ((measurable_bandIndex.comp measurable_fst).prodMk
      (measurable_bandIndex.comp measurable_snd))

theorem transportTag_destination {z : Gap × Gap} (hz : (z.1 : ℝ) ≤ (z.2 : ℝ)) :
    transportDest (transportTag z) = bandIndex z.2 := by
  have := bandIndex_antitone hz
  dsimp [transportDest, transportTag]
  omega

theorem bandCost_map_index {Ω : Type*} [MeasurableSpace Ω] (π : Measure Ω)
    {g : Ω → Gap} (hg : Measurable g) (j : ℕ) :
    bandCost (π.map g) j = ∫⁻ z, if bandIndex (g z) = j then inverseWeight (g z) else 0 ∂π := by
  change (∫⁻ d in band j, inverseWeight d ∂π.map g) = _
  rw [← lintegral_indicator (measurableSet_band j),
    lintegral_map ((measurable_inverseWeight).indicator (measurableSet_band j)) hg]
  apply lintegral_congr
  intro z
  by_cases hz : bandIndex (g z) = j
  · rw [ite_eq_left hz, Set.indicator_of_mem ((bandIndex_eq_iff (g z) j).mp hz)]
  · rw [ite_eq_right hz, Set.indicator_of_notMem (fun hm => hz ((bandIndex_eq_iff (g z) j).mpr hm))]

theorem coupling_row_cost (π : Measure (Gap × Gap)) (i : ℕ) :
    (∑' k, cellCost π transportTag (fun z => inverseWeight z.1) (i,k)) =
      bandCost (π.map Prod.fst) i := by
  have h := cellCost_merge π (w := fun z => inverseWeight z.1) measurable_transportTag
    (measurable_inverseWeight.comp measurable_fst) Prod.fst i
  rw [ENNReal.tsum_prod'] at h
  have he (a : ℕ) : (∑' k, if a = i then
      cellCost π transportTag (fun z => inverseWeight z.1) (a,k) else 0) =
      if a = i then ∑' k, cellCost π transportTag (fun z => inverseWeight z.1) (a,k) else 0 := by
    by_cases ha : a = i <;> simp [ha]
  simp_rw [he] at h
  rw [tsum_ite_eq] at h
  rw [bandCost_map_index π measurable_fst i]
  exact h

theorem coupling_column_cost (π : Measure (Gap × Gap))
    (hup : ∀ᵐ z ∂π, (z.1 : ℝ) ≤ (z.2 : ℝ)) (j : ℕ) :
    (∑' x, if transportDest x = j then
      cellCost π transportTag (fun z => inverseWeight z.2) x else 0) =
        bandCost (π.map Prod.snd) j := by
  rw [cellCost_merge π (w := fun z => inverseWeight z.2) measurable_transportTag
    (measurable_inverseWeight.comp measurable_snd) transportDest j, bandCost_map_index π measurable_snd]
  apply lintegral_congr_ae
  filter_upwards [hup] with z hz
  rw [transportTag_destination hz]

theorem coupling_cell_contraction (π : Measure (Gap × Gap))
    (hup : ∀ᵐ z ∂π, (z.1 : ℝ) ≤ (z.2 : ℝ)) (x : ℕ × ℕ) :
    cellCost π transportTag (fun z => inverseWeight z.2) x ≤
      ENNReal.ofReal (bandContraction x.2) *
        cellCost π transportTag (fun z => inverseWeight z.1) x := by
  unfold cellCost
  rw [← lintegral_const_mul _ (f := fun z => if transportTag z = x then inverseWeight z.1 else 0)
    ((measurable_inverseWeight.comp measurable_fst).ite
    (measurableSet_eq_fun measurable_transportTag measurable_const) measurable_const)]
  apply lintegral_mono_ae
  filter_upwards [hup] with z hz
  by_cases ht : transportTag z = x
  · simp only [ht, ite_true]
    have h := inverseSquare_band_contraction hz
    have hk : bandIndex z.1-bandIndex z.2 = x.2 := congrArg Prod.snd ht
    rw [hk] at h
    exact (ENNReal.ofReal_le_ofReal h).trans_eq
      (ENNReal.ofReal_mul (bandContraction_nonneg x.2))
  · simp [ht]

theorem gamma_le_three_of_increasing_coupling (π : Measure (Gap × Gap))
    [IsFiniteMeasure π] (hup : ∀ᵐ z ∂π, (z.1 : ℝ) ≤ (z.2 : ℝ)) :
    gamma (π.map Prod.snd) ≤ 3*gamma (π.map Prod.fst) := by
  let f := cellCost π transportTag (fun z => inverseWeight z.1)
  let b := cellCost π transportTag (fun z => inverseWeight z.2)
  have hf (x : ℕ × ℕ) : f x ≠ ∞ := by
    apply ne_top_of_le_ne_top (bandCost_ne_top (π.map Prod.fst) x.1)
    rw [← coupling_row_cost]
    simpa only [f, Prod.mk.eta] using
      (ENNReal.le_tsum (f := fun k => cellCost π transportTag (fun z => inverseWeight z.1) (x.1,k)) x.2)
  have hcol (j : ℕ) : (∑' x, if transportDest x = j then b x else 0) ≠ ∞ := by
    rw [coupling_column_cost π hup]
    exact bandCost_ne_top _ _
  have hb (x : ℕ × ℕ) : b x ≠ ∞ := by
    apply ne_top_of_le_ne_top (hcol (transportDest x))
    simpa only [ite_true] using
      (ENNReal.le_tsum (f := fun y => if transportDest y = transportDest x then b y else 0) x)
  apply gamma_le_three_of_band_transport (π.map Prod.snd) (π.map Prod.fst)
    (f := fun x => (f x).toReal) (b := fun x => (b x).toReal)
    (dest := transportDest)
    (fun _ => ENNReal.toReal_nonneg) (fun _ => ENNReal.toReal_nonneg)
  · intro i n
    rw [← ENNReal.toReal_sum (fun k _ => hf (i,k.val))]
    apply ENNReal.toReal_mono (bandCost_ne_top _ _)
    rw [← coupling_row_cost]
    simpa only [Finset.sum_range] using
      (ENNReal.sum_le_tsum (f := fun k => f (i,k)) (Finset.range n))
  · intro x
    have h := ENNReal.toReal_mono
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hf x)) (coupling_cell_contraction π hup x)
    simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofReal (bandContraction_nonneg x.2)] using h
  · intro j
    simpa only [apply_ite ENNReal.toReal, ENNReal.toReal_zero] using
      ENNReal.summable_toReal (hcol j)
  · intro j
    have he := ENNReal.tsum_toReal_eq (f := fun x => if transportDest x = j then b x else 0)
      (fun x => by split_ifs; exact hb x; exact ENNReal.zero_ne_top)
    dsimp only [b] at he
    rw [coupling_column_cost π hup] at he
    simpa only [apply_ite ENNReal.toReal, ENNReal.toReal_zero] using he

end ThresholdHC.ArbitraryLawAdaptation
