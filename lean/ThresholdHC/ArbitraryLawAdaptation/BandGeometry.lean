import ThresholdHC.ArbitraryLawAdaptation.GammaTransport
import ThresholdHC.EntropyTail.Band

/-! Canonical band indices and the inverse-square contraction of an upward
gap move. Endpoints use the existing half-open dyadic partition. -/

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace ThresholdHC.ArbitraryLawAdaptation
open ThresholdHC.Tier6 (Gap)
open ThresholdHC.EntropyTail

def bandIndex (d : Gap) : ℕ := (exists_band d).choose

theorem mem_bandIndex (d : Gap) : d ∈ band (bandIndex d) := (exists_band d).choose_spec

theorem bandIndex_eq_iff (d : Gap) (j : ℕ) : bandIndex d = j ↔ d ∈ band j := by
  constructor
  · intro h; exact h ▸ mem_bandIndex d
  · intro h
    by_contra hn
    exact Set.disjoint_left.mp (band_disjoint hn) (mem_bandIndex d) h

theorem measurable_bandIndex : Measurable bandIndex := by
  apply measurable_to_countable'
  intro j
  simpa [Set.preimage, bandIndex_eq_iff] using measurableSet_band j

theorem bandIndex_antitone {x y : Gap} (hxy : (x : ℝ) ≤ (y : ℝ)) :
    bandIndex y ≤ bandIndex x := by
  by_contra h
  have hx := (mem_bandIndex x).1
  have hy := (mem_bandIndex y).2
  have hp : (1/2 : ℝ)^(bandIndex y+1) ≤ (1/2 : ℝ)^(bandIndex x+2) :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
  linarith

theorem inverseSquare_band_contraction {x y : Gap}
    (hxy : (x : ℝ) ≤ (y : ℝ)) :
    (y : ℝ)⁻¹^2 ≤ bandContraction (bandIndex x-bandIndex y) * (x : ℝ)⁻¹^2 := by
  let k := bandIndex x-bandIndex y
  have hidx : bandIndex x = bandIndex y+k := by
    have := bandIndex_antitone hxy
    dsimp [k]; omega
  have hx := (mem_bandIndex x).2
  have hy := (mem_bandIndex y).1
  have he : (1/2 : ℝ)^(bandIndex x+1) =
      (2*(1/2 : ℝ)^k) * (1/2 : ℝ)^(bandIndex y+2) := by
    rw [hidx]
    simp only [pow_add, pow_succ]
    ring
  have hs : (x : ℝ) ≤ (2*(1/2 : ℝ)^k) * (y : ℝ) := by
    rw [he] at hx
    exact hx.trans (mul_le_mul_of_nonneg_left hy.le (by positivity))
  have hi : (y : ℝ)⁻¹ ≤ (2*(1/2 : ℝ)^k) * (x : ℝ)⁻¹ := by
    rw [← div_eq_mul_inv, le_div_iff₀ x.property.1]
    rw [inv_mul_eq_div, div_le_iff₀ y.property.1]
    exact hs
  have hp := pow_le_pow_left₀ (inv_nonneg.mpr y.property.1.le) hi 2
  have he2 : (2*(1/2 : ℝ)^k)^2 = 4*(1/4 : ℝ)^k := by
    rw [mul_pow, ← pow_mul, Nat.mul_comm k 2, pow_mul]
    norm_num
  rw [mul_pow, he2] at hp
  have hm := pow_le_pow_left₀ (inv_nonneg.mpr y.property.1.le)
    (inv_anti₀ x.property.1 hxy) 2
  rw [bandContraction, min_mul_of_nonneg _ _ (sq_nonneg _), one_mul]
  exact le_min hm hp

end ThresholdHC.ArbitraryLawAdaptation
