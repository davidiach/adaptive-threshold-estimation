import Mathlib.MeasureTheory.Measure.Dirac.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Tactic

/-! A conservative finite gap law from cumulative upper bounds. Its mass at
zero is retained explicitly. These are deterministic statements: the pilot
probability event that supplies the upper bounds is a separate obligation. -/

noncomputable section
open MeasureTheory Set
open scoped ENNReal BigOperators
namespace ThresholdHC.ArbitraryLawAdaptation

def prefixMinimum (u : ℕ → ℝ) : ℕ → ℝ
  | 0 => u 0
  | n+1 => min (prefixMinimum u n) (u (n+1))

theorem prefixMinimum_le (u : ℕ → ℝ) (n : ℕ) : prefixMinimum u n ≤ u n := by
  cases n with
  | zero => exact le_rfl
  | succ n => exact min_le_right _ _

theorem prefixMinimum_antitone (u : ℕ → ℝ) : Antitone (prefixMinimum u) := by
  apply antitone_nat_of_succ_le
  intro n
  exact min_le_left _ _

theorem prefixMinimum_nonneg {u : ℕ → ℝ} (hu : ∀ j, 0 ≤ u j) (n : ℕ) :
    0 ≤ prefixMinimum u n := by
  induction n with
  | zero => exact hu 0
  | succ n ih => exact le_min ih (hu (n+1))

theorem prefixMinimum_majorizes {u v : ℕ → ℝ} (hv : Antitone v)
    (n : ℕ) (hu : ∀ j ≤ n, v j ≤ u j) : v n ≤ prefixMinimum u n := by
  induction n with
  | zero => exact hu 0 le_rfl
  | succ n ih =>
    exact le_min ((hv (Nat.le_succ n)).trans (ih (fun j hj => hu j (by omega))))
      (hu (n+1) le_rfl)

def gridPoint (j : ℕ) : ℝ := (1/2:ℝ)^(j+1)

theorem gridPoint_pos (j : ℕ) : 0 < gridPoint j := by unfold gridPoint; positivity

theorem gridPoint_antitone : Antitone gridPoint := by
  apply antitone_nat_of_succ_le
  intro n
  unfold gridPoint
  rw [pow_succ]
  nlinarith [pow_nonneg (by norm_num : (0:ℝ) ≤ 1/2) (n+1)]

theorem gridPoint_succ_lt (j : ℕ) : gridPoint (j+1) < gridPoint j := by
  have hp := gridPoint_pos j
  unfold gridPoint at *
  rw [pow_succ]
  linarith

def envelopeLaw (c : ℕ → ℝ) (n : ℕ) : Measure ℝ :=
  ENNReal.ofReal (c n) • Measure.dirac 0 +
    ∑ i : Fin n, ENNReal.ofReal (c i.val-c (i.val+1)) • Measure.dirac (gridPoint (i.val+1))

def envelopeCDF (c : ℕ → ℝ) (n : ℕ) (x : ℝ) : ℝ :=
  if 0 ≤ x then c n + ∑ i : Fin n,
    if gridPoint (i.val+1) ≤ x then c i.val-c (i.val+1) else 0 else 0

theorem envelope_weights_sum (c : ℕ → ℝ) (n : ℕ) :
    c n + (∑ i : Fin n, (c i.val-c (i.val+1))) = c 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc,Fin.val_last]
    linarith

theorem envelopeCDF_nonneg {c : ℕ → ℝ} (hc : ∀ j, 0 ≤ c j)
    (hmono : Antitone c) (n : ℕ) (x : ℝ) : 0 ≤ envelopeCDF c n x := by
  unfold envelopeCDF
  split_ifs
  · exact add_nonneg (hc n) (Finset.sum_nonneg fun i _ => by
      split_ifs
      · exact sub_nonneg.mpr (hmono (Nat.le_succ _))
      · exact le_rfl)
  · exact le_rfl

theorem envelopeCDF_below_grid {c : ℕ → ℝ} {n : ℕ} {x : ℝ}
    (hx : 0 ≤ x) (hgrid : x < gridPoint n) : envelopeCDF c n x = c n := by
  unfold envelopeCDF
  rw [ite_eq_left hx]
  have hz (i : Fin n) : ¬ gridPoint (i.val+1) ≤ x := by
    have hi := gridPoint_antitone (show i.val+1 ≤ n by omega)
    linarith
  simp only [ite_eq_right (hz _),Finset.sum_const_zero,add_zero]

theorem envelopeCDF_succ_above {c : ℕ → ℝ} {n : ℕ} {x : ℝ}
    (hx : gridPoint (n+1) ≤ x) : envelopeCDF c (n+1) x = envelopeCDF c n x := by
  have hx0 := (gridPoint_pos (n+1)).le.trans hx
  simp only [envelopeCDF,ite_eq_left hx0,Fin.sum_univ_castSucc,Fin.val_castSucc,Fin.val_last,
    ite_eq_left hx]
  ring

theorem envelopeCDF_dominates {F : ℝ → ℝ} {c : ℕ → ℝ} {n : ℕ}
    (hF : Monotone F) (hneg : ∀ x < 0, F x ≤ 0) (htop : ∀ x, F x ≤ c 0)
    (hgrid : ∀ j ≤ n, F (gridPoint j) ≤ c j) (x : ℝ) : F x ≤ envelopeCDF c n x := by
  by_cases hx : 0 ≤ x
  · induction n generalizing x with
    | zero => simpa [envelopeCDF,hx] using htop x
    | succ n ih =>
      by_cases hg : gridPoint (n+1) ≤ x
      · rw [envelopeCDF_succ_above hg]
        exact ih (fun j hj => hgrid j (by omega)) x hx
      · rw [envelopeCDF_below_grid hx (lt_of_not_ge hg)]
        exact (hF (le_of_not_ge hg)).trans (hgrid (n+1) le_rfl)
  · simpa [envelopeCDF,hx] using hneg x (lt_of_not_ge hx)

theorem envelopeLaw_Iic {c : ℕ → ℝ} (hc : ∀ j, 0 ≤ c j)
    (hmono : Antitone c) (n : ℕ) (x : ℝ) :
    envelopeLaw c n (Iic x) = ENNReal.ofReal (envelopeCDF c n x) := by
  have hw (i : Fin n) : 0 ≤ c i.val-c (i.val+1) :=
    sub_nonneg.mpr (hmono (Nat.le_succ _))
  have hs : (∑ i : Fin n, ENNReal.ofReal (c i.val-c (i.val+1)) •
      Measure.dirac (gridPoint (i.val+1))) (Iic x) =
      ∑ i : Fin n, if gridPoint (i.val+1) ≤ x then
        ENNReal.ofReal (c i.val-c (i.val+1)) else 0 := by
    simp [Measure.dirac_apply,Set.indicator,Set.mem_Iic,mul_ite]
  rw [envelopeLaw,Measure.add_apply,hs]
  by_cases hx : 0 ≤ x
  · have hw' (i : Fin n) : 0 ≤ if gridPoint (i.val+1) ≤ x then
        c i.val-c (i.val+1) else 0 := by split_ifs; exact hw i; exact le_rfl
    simp only [envelopeCDF,ite_eq_left hx]
    rw [ENNReal.ofReal_add (hc n) (Finset.sum_nonneg fun i _ => hw' i),
      ENNReal.ofReal_sum_of_nonneg (fun i _ => hw' i)]
    simp [hx,apply_ite]
  · have hg (i : Fin n) : ¬ gridPoint (i.val+1) ≤ x := by
      have hp := gridPoint_pos (i.val+1)
      linarith
    simp [envelopeCDF,hx,hg,Measure.dirac_apply,Set.indicator]

theorem envelopeLaw_mass {c : ℕ → ℝ} (hc : ∀ j, 0 ≤ c j)
    (hmono : Antitone c) (n : ℕ) : envelopeLaw c n univ = ENNReal.ofReal (c 0) := by
  have hw (i : Fin n) : 0 ≤ c i.val-c (i.val+1) :=
    sub_nonneg.mpr (hmono (Nat.le_succ _))
  simp only [envelopeLaw,Measure.add_apply,Measure.finsetSum_apply,Measure.smul_apply,
    Measure.dirac_apply_of_mem (mem_univ _),smul_eq_mul,mul_one]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => hw i),
    ← ENNReal.ofReal_add (hc n) (Finset.sum_nonneg fun i _ => hw i),envelope_weights_sum]

theorem envelopeLaw_probability {c : ℕ → ℝ} (hc : ∀ j, 0 ≤ c j)
    (hmono : Antitone c) (hzero : c 0 = 1) (n : ℕ) :
    IsProbabilityMeasure (envelopeLaw c n) := by
  constructor
  rw [envelopeLaw_mass hc hmono,hzero]
  norm_num

theorem envelopeLaw_zero (c : ℕ → ℝ) (n : ℕ) : envelopeLaw c n {0} = ENNReal.ofReal (c n) := by
  have hg (i : Fin n) : gridPoint (i.val+1) ≠ 0 := (gridPoint_pos _).ne'
  simp [envelopeLaw,hg]

/-- A grid atom belongs to the closed CDF at that point: the value is the
preceding upper bound, not the next one. -/
theorem envelopeCDF_at_grid (c : ℕ → ℝ) {n j : ℕ} (hj : j < n) :
    envelopeCDF c n (gridPoint (j+1)) = c j := by
  induction n with
  | zero => omega
  | succ n ih =>
    rw [envelopeCDF_succ_above (gridPoint_antitone (by omega : j+1 ≤ n+1))]
    by_cases he : j = n
    · subst j
      exact envelopeCDF_below_grid (gridPoint_pos _).le (gridPoint_succ_lt _)
    · exact ih (by omega)

theorem envelopeLaw_dominates (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {c : ℕ → ℝ} (hc : ∀ j, 0 ≤ c j) (hmono : Antitone c) (hzero : c 0 = 1)
    (hsupport : μ (Iio 0) = 0) (n : ℕ)
    (hgrid : ∀ j ≤ n, μ.real (Iic (gridPoint j)) ≤ c j) (x : ℝ) :
    μ (Iic x) ≤ envelopeLaw c n (Iic x) := by
  have hF : Monotone (fun y : ℝ => μ.real (Iic y)) := by
    intro y z hyz
    exact measureReal_mono (Iic_subset_Iic.mpr hyz)
  have hn : ∀ y < 0, μ.real (Iic y) ≤ 0 := by
    intro y hy
    have hm : μ (Iic y) = 0 := le_antisymm
      ((measure_mono (show Iic y ⊆ Iio 0 from fun z hz => lt_of_le_of_lt hz hy)).trans_eq hsupport)
      zero_le
    simp [measureReal_def,hm]
  have ht : ∀ y, μ.real (Iic y) ≤ c 0 := by
    intro y
    rw [hzero]
    exact measureReal_le_one
  have hb := envelopeCDF_dominates hF hn ht hgrid x
  rw [envelopeLaw_Iic hc hmono,← ENNReal.ofReal_toReal (measure_ne_top μ (Iic x))]
  exact ENNReal.ofReal_le_ofReal hb

theorem learnedEnvelope_probability {u : ℕ → ℝ} (hu : ∀ j, 0 ≤ u j)
    (hu0 : u 0 = 1) (n : ℕ) : IsProbabilityMeasure (envelopeLaw (prefixMinimum u) n) :=
  envelopeLaw_probability (prefixMinimum_nonneg hu) (prefixMinimum_antitone u) hu0 n

/-- Valid upper bounds at the finitely many probed cutoffs produce a
conservative probability law, without assumptions on unprobed cutoffs. -/
theorem learnedEnvelope_dominates (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {u : ℕ → ℝ} (hu : ∀ j, 0 ≤ u j) (hu0 : u 0 = 1)
    (hsupport : μ (Iio 0) = 0) (n : ℕ)
    (hgrid : ∀ j ≤ n, μ.real (Iic (gridPoint j)) ≤ u j) (x : ℝ) :
    μ (Iic x) ≤ envelopeLaw (prefixMinimum u) n (Iic x) := by
  apply envelopeLaw_dominates μ (prefixMinimum_nonneg hu) (prefixMinimum_antitone u)
    hu0 hsupport n _ x
  intro j hj
  apply prefixMinimum_majorizes _ j (fun i hi => hgrid i (hi.trans hj))
  intro i k hik
  exact measureReal_mono (Iic_subset_Iic.mpr (gridPoint_antitone hik))

end ThresholdHC.ArbitraryLawAdaptation
