import ThresholdHC.BandCostExample.Specification
import ThresholdHC.GlobalSelectionCertificates.Menu

/-! Rational data for the 64-band example and its bridge to the measure-level
specification. Gap `i` is `2^{-(i+1)}` and lies in canonical band `i`; its
weight is `g_i^2 / ∑ g_j^2`. Every lemma is uniform in `i : Fin 64`: no case
split or sum expansion over the 64 atoms is used. -/
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace ThresholdHC.BandCostExample
open ThresholdHC.Tier6 (Gap)
open ThresholdHC.EntropyTail ThresholdHC.FiniteLawCertificates
open ThresholdHC.GlobalSelectionCertificates

/-- The rational gaps `2^{-(i+1)}`. -/
def gaps (i : Fin 64) : ℚ := (1/2 : ℚ)^(i.val+1)

/-- The rational normalizer `∑ g_j^2`. -/
def zq : ℚ := ∑ j : Fin 64, (gaps j)^2

/-- The rational masses `g_i^2 / ∑ g_j^2`. -/
def weights (i : Fin 64) : ℚ := (gaps i)^2 / zq

/-- The band of each gap; also the list of occupied bands. -/
def labels (i : Fin 64) : ℕ := i.val

theorem gaps_pos (i : Fin 64) : 0 < gaps i := pow_pos (by norm_num) _

theorem gaps_valid : ∀ i, 0 < gaps i ∧ gaps i ≤ 1/2 := fun i =>
  ⟨gaps_pos i, pow_le_of_le_one (by norm_num) (by norm_num) (Nat.succ_ne_zero _)⟩

theorem zq_pos : 0 < zq :=
  Finset.sum_pos (fun i _ => pow_pos (gaps_pos i) 2) Finset.univ_nonempty

theorem weights_positive : ∀ i, 0 < weights i := fun i =>
  div_pos (pow_pos (gaps_pos i) 2) zq_pos

theorem weights_nonneg : ∀ i, 0 ≤ weights i := fun i => (weights_positive i).le

theorem weights_sum : ∑ i, weights i = 1 := by
  unfold weights
  rw [← Finset.sum_div]
  exact div_self zq_pos.ne'

theorem labels_injective : Function.Injective labels := Fin.val_injective

/-- Gap `i` lies in canonical band `j` exactly when `j = i`. -/
theorem inBand_iff (i : Fin 64) (j : ℕ) : inBand (gaps i) j = true ↔ i.val = j := by
  rw [inBand, decide_eq_true_iff]
  unfold gaps
  rw [pow_lt_pow_iff_right_of_lt_one₀ (by norm_num) (by norm_num),
    pow_le_pow_iff_right_of_lt_one₀ (by norm_num) (by norm_num)]
  omega

theorem labels_valid : ∀ i, inBand (gaps i) (labels i) = true :=
  fun i => (inBand_iff i _).mpr rfl

theorem labels_cover : ∀ i, ∃ j, inBand (gaps i) (labels j) = true :=
  fun i => ⟨i, labels_valid i⟩

theorem atoms_val (i : Fin 64) : (atoms i : ℝ) = (1/2 : ℝ)^(i.val+1) := rfl

theorem gaps_cast (i : Fin 64) : ((gaps i : ℚ) : ℝ) = (1/2 : ℝ)^(i.val+1) := by
  simp [gaps]

theorem atoms_eq : atoms = points gaps gaps_valid := by
  funext i
  apply Subtype.ext
  change (1/2 : ℝ)^(i.val+1) = ((gaps i : ℚ) : ℝ)
  rw [gaps_cast]

/-- The real normalizer `∑ d_j^2` of the specification. -/
def zsum : ℝ := ∑ j : Fin 64, (atoms j : ℝ)^2

theorem zq_cast : ((zq : ℚ) : ℝ) = zsum := by
  simp only [zq, zsum, Rat.cast_sum, Rat.cast_pow, gaps_cast, atoms_val]

theorem weights_cast (i : Fin 64) : ((weights i : ℚ) : ℝ) = masses i := by
  simp only [weights, Rat.cast_div, Rat.cast_pow, zq_cast, gaps_cast, masses, atoms_val, zsum]

theorem masses_eq (i : Fin 64) :
    ENNReal.ofReal (masses i) = ENNReal.ofReal (weights i : ℝ) := by
  rw [weights_cast]

theorem law_eq : law = atomicMeasure (points gaps gaps_valid) weights := by
  simp only [law, atomicMeasure, atoms_eq, masses_eq]

theorem retained_eq (s : Fin 64 → Bool) :
    retained s = atomicMeasure (points gaps gaps_valid) (fun i => weights i * fractions s i) := by
  unfold retained atomicMeasure
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [atoms_eq]
  cases h : s i <;> simp [fractions, h, masses_eq]

theorem retained_le (s : Fin 64 → Bool) : retained s ≤ law := by
  rw [retained_eq, law_eq]
  exact selected_le _ _ _ weights_nonneg (fractions_valid s)

theorem law_probability : IsProbabilityMeasure law := by
  rw [law_eq]
  exact atomicMeasure_probability _ _ weights_nonneg weights_sum

theorem law_support : law.support = Set.range atoms := by
  rw [law_eq, atomic_support _ _ weights_positive, ← atoms_eq]

theorem atoms_mem_band (i : Fin 64) : atoms i ∈ band i.val := by
  rw [atoms_eq]
  exact (points_mem_band gaps gaps_valid i _).mpr ((inBand_iff i _).mpr rfl)

theorem atoms_injective : Function.Injective atoms := by
  intro i j h
  have h1 : (atoms i : ℝ) = (atoms j : ℝ) := congrArg Subtype.val h
  rw [atoms_val, atoms_val] at h1
  have h2 := (pow_right_injective₀ (by norm_num : (0:ℝ) < 1/2) (by norm_num)) h1
  exact Fin.ext (by omega)

theorem sqrt_budget : Real.sqrt 4294967296 = 65536 := by
  rw [show (4294967296 : ℝ) = 65536^2 by norm_num]
  exact Real.sqrt_sq (by norm_num)

theorem atoms_sq (j : Fin 64) : (atoms j : ℝ)^2 = (1/4 : ℝ)^(j.val+1) := by
  rw [atoms_val, ← pow_mul, mul_comm, pow_mul]
  norm_num

/-- The geometric closed form of the normalizer. -/
theorem zsum_eq : zsum = (1 - (1/4 : ℝ)^64)/3 := by
  unfold zsum
  simp only [atoms_sq]
  rw [Fin.sum_univ_eq_sum_range (fun j => (1/4 : ℝ)^(j+1)) 64]
  simp only [pow_succ]
  rw [← Finset.sum_mul, geom_sum_eq (by norm_num : (1/4 : ℝ) ≠ 1)]
  ring

theorem zsum_pos : 0 < zsum := by
  rw [← zq_cast]
  exact_mod_cast zq_pos

/-- The common inverse-square cost `c = 1/∑ d_j^2` of every atom. -/
def cc : ℝ := 1 / zsum

theorem cc_pos : 0 < cc := div_pos one_pos zsum_pos

theorem three_lt_cc : 3 < cc := by
  rw [cc, zsum_eq, lt_div_iff₀ (by norm_num)]
  have : (0:ℝ) < (1/4)^64 := by norm_num
  linarith

theorem cc_le : cc ≤ 301/100 := by
  rw [cc, zsum_eq, div_le_iff₀ (by norm_num)]
  norm_num

theorem weights_div (i : Fin 64) : (weights i : ℝ) = cc * (atoms i : ℝ)^2 := by
  rw [weights_cast, masses, cc]
  change _ / zsum = _
  ring

end ThresholdHC.BandCostExample
