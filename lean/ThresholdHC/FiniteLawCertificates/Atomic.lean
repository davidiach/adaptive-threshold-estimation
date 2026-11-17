import ThresholdHC.GapLawMenus.FiniteEntropy
import ThresholdHC.EntropyTail.HardSelection

/-! Finite rational data connected to the original measure-level definitions. -/
noncomputable section
open MeasureTheory
open scoped BigOperators ENNReal Classical
namespace ThresholdHC.FiniteLawCertificates
open ThresholdHC.Tier6

def atomicMeasure {n : ℕ} (d : Fin n → Gap) (w : Fin n → ℚ) : Measure Gap :=
  ∑ i, ENNReal.ofReal (w i : ℝ) • Measure.dirac (d i)

theorem atomicMeasure_finite {n : ℕ} (d : Fin n → Gap) (w : Fin n → ℚ) :
    IsFiniteMeasure (atomicMeasure d w) := by
  constructor
  simp only [atomicMeasure, Measure.finsetSum_apply, Measure.smul_apply,
    Measure.dirac_apply_of_mem (Set.mem_univ _), smul_eq_mul, mul_one]
  exact ENNReal.sum_lt_top.mpr (fun _ _ => ENNReal.ofReal_lt_top)

theorem atomicMeasure_univ {n : ℕ} (d : Fin n → Gap) (w : Fin n → ℚ)
    (hw : ∀ i, 0 ≤ w i) :
    atomicMeasure d w Set.univ = ENNReal.ofReal ((∑ i, w i : ℚ) : ℝ) := by
  simp only [atomicMeasure, Measure.finsetSum_apply, Measure.smul_apply,
    Measure.dirac_apply_of_mem (Set.mem_univ _), smul_eq_mul, mul_one]
  rw [Rat.cast_sum, ENNReal.ofReal_sum_of_nonneg (fun i _ => by exact_mod_cast hw i)]

theorem atomicMeasure_probability {n : ℕ} (d : Fin n → Gap) (w : Fin n → ℚ)
    (hw : ∀ i, 0 ≤ w i) (hs : ∑ i, w i = 1) :
    IsProbabilityMeasure (atomicMeasure d w) := by
  constructor
  rw [atomicMeasure_univ d w hw, hs]
  norm_num

theorem lintegral_atomic {n : ℕ} (d : Fin n → Gap) (w : Fin n → ℚ)
    (f : Gap → ℝ≥0∞) :
    ∫⁻ x, f x ∂atomicMeasure d w = ∑ i, ENNReal.ofReal (w i : ℝ) * f (d i) := by
  simp [atomicMeasure, lintegral_finsetSum_measure, lintegral_smul_measure]

theorem integrable_atomic {n : ℕ} (d : Fin n → Gap) (w : Fin n → ℚ) (f : Gap → ℝ) :
    Integrable f (atomicMeasure d w) := by
  rw [atomicMeasure, integrable_finsetSum_measure]
  intro i _
  exact (integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top

theorem integral_atomic {n : ℕ} (d : Fin n → Gap) (w : Fin n → ℚ)
    (hw : ∀ i, 0 ≤ w i) (f : Gap → ℝ) :
    ∫ x, f x ∂atomicMeasure d w = ∑ i, (w i : ℝ) * f (d i) := by
  unfold atomicMeasure
  rw [integral_finsetSum_measure (fun i _ =>
    (integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top)]
  apply Finset.sum_congr rfl
  intro i _
  simp [ENNReal.toReal_ofReal (show (0:ℝ) ≤ w i by exact_mod_cast hw i)]

theorem atomicMeasure_add {n : ℕ} (d : Fin n → Gap) (v w : Fin n → ℚ)
    (hv : ∀ i, 0 ≤ v i) (hw : ∀ i, 0 ≤ w i) :
    atomicMeasure d (fun i => v i+w i) = atomicMeasure d v + atomicMeasure d w := by
  have he (i : Fin n) : ENNReal.ofReal ((v i+w i:ℚ):ℝ) =
      ENNReal.ofReal (v i:ℝ)+ENNReal.ofReal (w i:ℝ) := by
    rw [Rat.cast_add, ENNReal.ofReal_add (by exact_mod_cast hv i) (by exact_mod_cast hw i)]
  simp only [atomicMeasure, he, add_smul, Finset.sum_add_distrib]

theorem atomicMeasure_smul {n : ℕ} (d : Fin n → Gap) (w : Fin n → ℚ)
    (q : ℚ) (hq : 0 ≤ q) :
    atomicMeasure d (fun i => q*w i) = ENNReal.ofReal (q:ℝ) • atomicMeasure d w := by
  simp only [atomicMeasure, Rat.cast_mul,
    ENNReal.ofReal_mul (show (0:ℝ) ≤ q by exact_mod_cast hq),
    mul_smul, Finset.smul_sum]

theorem atomicMeasure_restrict {n : ℕ} (d : Fin n → Gap) (w : Fin n → ℚ) (S : Set Gap) :
    (atomicMeasure d w).restrict S = atomicMeasure d (fun i => if d i ∈ S then w i else 0) := by
  unfold atomicMeasure
  rw [← Measure.sum_fintype, Measure.restrict_sum_of_countable, Measure.sum_fintype]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : d i ∈ S <;> simp [Measure.restrict_smul, restrict_dirac, hi]

theorem atomicMeasure_sub {n : ℕ} (d : Fin n → Gap) (w v : Fin n → ℚ)
    (hv : ∀ i, 0 ≤ v i) (hle : ∀ i, v i ≤ w i) :
    atomicMeasure d w - atomicMeasure d v = atomicMeasure d (fun i => w i-v i) := by
  let := atomicMeasure_finite d v
  have he : atomicMeasure d (fun i => w i-v i)+atomicMeasure d v = atomicMeasure d w := by
    rw [← atomicMeasure_add d _ v (fun i => sub_nonneg.mpr (hle i)) hv]
    congr 1
    funext i
    ring
  rw [← he, Measure.add_sub_cancel]

theorem atomicMeasure_le {n : ℕ} (d : Fin n → Gap) (w v : Fin n → ℚ)
    (hle : ∀ i, v i ≤ w i) : atomicMeasure d v ≤ atomicMeasure d w := by
  apply Measure.le_iff'.mpr
  intro S
  simp only [atomicMeasure, Measure.finsetSum_apply, Measure.smul_apply, smul_eq_mul]
  apply Finset.sum_le_sum
  intro i _
  gcongr
  exact_mod_cast hle i

theorem atomicMeasure_real {n : ℕ} (d : Fin n → Gap) (w : Fin n → ℚ)
    (hw : ∀ i, 0 ≤ w i) (S : Set Gap) :
    (atomicMeasure d w).real S = ∑ i, if d i ∈ S then (w i:ℝ) else 0 := by
  have hn (i : Fin n) : 0 ≤ (if d i ∈ S then w i else 0) := by
    split_ifs <;> simp_all
  rw [measureReal_def, ← Measure.restrict_apply_univ, atomicMeasure_restrict,
    atomicMeasure_univ d _ hn, ENNReal.toReal_ofReal (by exact_mod_cast Finset.sum_nonneg (fun i _ => hn i))]
  simp only [Rat.cast_sum]
  apply Finset.sum_congr rfl
  intro i _
  split_ifs <;> simp

theorem lintegral_ofReal_atomic {n : ℕ} (d : Fin n → Gap) (w : Fin n → ℚ)
    (hw : ∀ i, 0 ≤ w i) (f : Gap → ℝ) (hf : ∀ x, 0 ≤ f x) :
    ∫⁻ x, ENNReal.ofReal (f x) ∂atomicMeasure d w = ENNReal.ofReal (∑ i, (w i:ℝ)*f (d i)) := by
  rw [lintegral_atomic, ENNReal.ofReal_sum_of_nonneg (fun i _ =>
    mul_nonneg (by exact_mod_cast hw i) (hf _))]
  apply Finset.sum_congr rfl
  intro i _
  rw [ENNReal.ofReal_mul (by exact_mod_cast hw i)]

theorem bandCost_atomic {n : ℕ} (d : Fin n → Gap) (w : Fin n → ℚ)
    (hw : ∀ i, 0 ≤ w i) (j : ℕ) :
    ThresholdHC.EntropyTail.bandCost (atomicMeasure d w) j =
      ENNReal.ofReal (∑ i, if d i ∈ ThresholdHC.EntropyTail.band j
        then (w i:ℝ)*((d i:ℝ)⁻¹)^2 else 0) := by
  rw [ThresholdHC.EntropyTail.bandCost,
    ← lintegral_indicator (ThresholdHC.EntropyTail.measurableSet_band j)]
  have he : (ThresholdHC.EntropyTail.band j).indicator
      (fun x : Gap => ENNReal.ofReal ((x:ℝ)⁻¹^2)) =
      fun x : Gap => ENNReal.ofReal (if x ∈ ThresholdHC.EntropyTail.band j then (x:ℝ)⁻¹^2 else 0) := by
    funext x
    by_cases hx : x ∈ ThresholdHC.EntropyTail.band j <;> simp [hx]
  rw [he, lintegral_ofReal_atomic d w hw _ (by intro x; split_ifs <;> positivity)]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  split_ifs <;> simp

theorem tailCost_atomic {n : ℕ} (d : Fin n → Gap) (w : Fin n → ℚ)
    (hw : ∀ i, 0 ≤ w i) {h : ℝ} (hh : 0 ≤ h) :
    ThresholdHC.EntropyTail.tailCost (atomicMeasure d w) h =
      ENNReal.ofReal (∑ i, (w i:ℝ)*min 1 (h/(d i:ℝ))) := by
  exact lintegral_ofReal_atomic d w hw _ (fun x =>
    le_min zero_le_one (div_nonneg hh x.property.1.le))

theorem gamma_atomic {n m : ℕ} (d : Fin n → Gap) (w : Fin n → ℚ)
    (hw : ∀ i, 0 ≤ w i) (labels : Fin m → ℕ) (hinj : Function.Injective labels)
    (hcover : ∀ i, ∃ j, d i ∈ ThresholdHC.EntropyTail.band (labels j)) :
    ThresholdHC.EntropyTail.gamma (atomicMeasure d w) =
      ENNReal.ofReal (ThresholdHC.EntropyTailQuantile.costEntropy (fun j =>
        ∑ i, if d i ∈ ThresholdHC.EntropyTail.band (labels j)
          then (w i:ℝ)*((d i:ℝ)⁻¹)^2 else 0)) := by
  let := atomicMeasure_finite d w
  have hz (k : ℕ) (hk : k ∉ List.ofFn labels) :
      ThresholdHC.EntropyTail.bandCost (atomicMeasure d w) k = 0 := by
    rw [bandCost_atomic d w hw]
    have he : (∑ i, if d i ∈ ThresholdHC.EntropyTail.band k
        then (w i:ℝ)*((d i:ℝ)⁻¹)^2 else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro i _
      have hnot : d i ∉ ThresholdHC.EntropyTail.band k := by
        intro hi
        obtain ⟨j,hj⟩ := hcover i
        have hne : k ≠ labels j := by
          intro he
          exact hk (by simp [List.mem_ofFn, he])
        exact Set.disjoint_left.mp (ThresholdHC.EntropyTail.band_disjoint hne) hi hj
      simp [hnot]
    rw [he, ENNReal.ofReal_zero]
  rw [ThresholdHC.GapLawMenus.gamma_list _ (List.ofFn labels) (List.nodup_ofFn.mpr hinj) hz,
    List.map_ofFn, ThresholdHC.BandCostSelection.multisetEntropy_ofFn]
  congr 2
  funext j
  rw [Function.comp_apply, bandCost_atomic d w hw, ENNReal.toReal_ofReal]
  apply Finset.sum_nonneg
  intro i _
  split_ifs
  · exact mul_nonneg (by exact_mod_cast hw i) (sq_nonneg _)
  · exact le_rfl

end ThresholdHC.FiniteLawCertificates
