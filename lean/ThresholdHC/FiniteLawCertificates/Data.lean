import ThresholdHC.FiniteLawCertificates.Atomic

/-! Finite rational data connected to the original measure-level definitions. -/
noncomputable section
open MeasureTheory
open scoped BigOperators ENNReal Classical
namespace ThresholdHC.FiniteLawCertificates
open ThresholdHC.Tier6

def inBand (g : ℚ) (j : ℕ) : Bool :=
  decide ((1/2:ℚ)^(j+2) < g ∧ g ≤ (1/2:ℚ)^(j+1))

def costs {n m : ℕ} (g v : Fin n → ℚ) (labels : Fin m → ℕ) : Fin m → ℚ :=
  fun j => ∑ i, if inBand (g i) (labels j) then v i/(g i)^2 else 0

def points {n : ℕ} (g : Fin n → ℚ) (hg : ∀ i, 0 < g i ∧ g i ≤ 1/2) : Fin n → Gap :=
  fun i => ⟨(g i:ℝ), by
    constructor
    · exact_mod_cast (hg i).1
    · have h : (g i:ℝ) ≤ ((1/2:ℚ):ℝ) := Rat.cast_le.mpr (hg i).2
      simpa only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] using h⟩

theorem points_mem_band {n : ℕ} (g : Fin n → ℚ) (hg : ∀ i, 0 < g i ∧ g i ≤ 1/2)
    (i : Fin n) (j : ℕ) :
    points g hg i ∈ ThresholdHC.EntropyTail.band j ↔ inBand (g i) j = true := by
  simp only [points, ThresholdHC.EntropyTail.band, Set.mem_ofPred_eq, inBand, decide_eq_true_eq]
  have h₁ : (((1/2:ℚ)^(j+2):ℚ):ℝ) < (g i:ℝ) ↔ (1/2:ℚ)^(j+2) < g i := Rat.cast_lt
  have h₂ : (g i:ℝ) ≤ (((1/2:ℚ)^(j+1):ℚ):ℝ) ↔ g i ≤ (1/2:ℚ)^(j+1) := Rat.cast_le
  simpa only [Rat.cast_pow, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] using and_congr h₁ h₂

theorem costs_nonneg {n m : ℕ} (g v : Fin n → ℚ) (labels : Fin m → ℕ)
    (hv : ∀ i, 0 ≤ v i) (j : Fin m) : 0 ≤ costs g v labels j := by
  apply Finset.sum_nonneg
  intro i _
  split_ifs
  · exact div_nonneg (hv i) (sq_nonneg _)
  · exact le_rfl

theorem costs_cast {n m : ℕ} (g v : Fin n → ℚ) (labels : Fin m → ℕ)
    (hg : ∀ i, 0 < g i ∧ g i ≤ 1/2) (j : Fin m) :
    (costs g v labels j : ℝ) =
      ∑ i, if points g hg i ∈ ThresholdHC.EntropyTail.band (labels j)
        then (v i:ℝ)*((points g hg i:ℝ)⁻¹)^2 else 0 := by
  simp only [costs, Rat.cast_sum, points_mem_band]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : inBand (g i) (labels j) = true
  · simp [hi, points, div_eq_mul_inv, inv_pow]
  · simp [hi]

theorem gamma_rational {n m : ℕ} (g v : Fin n → ℚ) (labels : Fin m → ℕ)
    (hg : ∀ i, 0 < g i ∧ g i ≤ 1/2) (hv : ∀ i, 0 ≤ v i)
    (hinj : Function.Injective labels) (hcover : ∀ i, ∃ j, inBand (g i) (labels j) = true) :
    ThresholdHC.EntropyTail.gamma (atomicMeasure (points g hg) v) =
      ENNReal.ofReal (ThresholdHC.EntropyTailQuantile.costEntropy (fun j => (costs g v labels j:ℝ))) := by
  rw [gamma_atomic (points g hg) v hv labels hinj
    (fun i => by obtain ⟨j,hj⟩ := hcover i; exact ⟨j,(points_mem_band g hg i _).mpr hj⟩)]
  simp only [costs_cast g v labels hg]

end ThresholdHC.FiniteLawCertificates
