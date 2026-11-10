import ThresholdHC.ArbitraryLawAdaptation.CouplingEntropy

/-! The product gap VD/2 has exactly two possible destination bands per
source band and multiplier band. -/

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace ThresholdHC.ArbitraryLawAdaptation
open ThresholdHC.Tier6 (Gap)
open ThresholdHC.EntropyTail

def lightGap (z : Gap × Gap) : Gap :=
  ⟨(z.1 : ℝ)*(z.2 : ℝ)/2, div_pos (mul_pos z.1.property.1 z.2.property.1) (by norm_num), by
    have hm := mul_le_mul z.1.property.2 z.2.property.2 z.2.property.1.le (by norm_num)
    linarith⟩

theorem measurable_lightGap : Measurable lightGap := by
  apply Measurable.subtype_mk
  fun_prop

theorem bandIndex_le_of_lower {d : Gap} {m : ℕ}
    (h : (1/2 : ℝ)^(m+2) < (d : ℝ)) : bandIndex d ≤ m := by
  by_contra hn
  have hp : (1/2 : ℝ)^(bandIndex d+1) ≤ (1/2 : ℝ)^(m+2) :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
  linarith [(mem_bandIndex d).2]

theorem bandIndex_ge_of_upper {d : Gap} {m : ℕ}
    (h : (d : ℝ) ≤ (1/2 : ℝ)^(m+1)) : m ≤ bandIndex d := by
  by_contra hn
  have hp : (1/2 : ℝ)^(m+1) ≤ (1/2 : ℝ)^(bandIndex d+2) :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
  linarith [(mem_bandIndex d).1]

theorem lightGap_bands (z : Gap × Gap) :
    bandIndex z.1+bandIndex z.2+2 ≤ bandIndex (lightGap z) ∧
      bandIndex (lightGap z) ≤ bandIndex z.1+bandIndex z.2+3 := by
  have hlow : (1/2 : ℝ)^(bandIndex z.1+bandIndex z.2+3+2) < (lightGap z : ℝ) := by
    have hp := mul_lt_mul (mem_bandIndex z.1).1 (mem_bandIndex z.2).1.le
      (by positivity) z.1.property.1.le
    have he : (1/2 : ℝ)^(bandIndex z.1+bandIndex z.2+3+2) =
        (1/2 : ℝ)^(bandIndex z.1+2)*(1/2 : ℝ)^(bandIndex z.2+2)/2 := by
      simp only [pow_add, pow_succ]; ring
    rw [he]
    exact div_lt_div_of_pos_right hp (by norm_num)
  have hupp : (lightGap z : ℝ) ≤ (1/2 : ℝ)^(bandIndex z.1+bandIndex z.2+2+1) := by
    have hp := mul_le_mul (mem_bandIndex z.1).2 (mem_bandIndex z.2).2
      z.2.property.1.le (by positivity)
    have he : (1/2 : ℝ)^(bandIndex z.1+bandIndex z.2+2+1) =
        (1/2 : ℝ)^(bandIndex z.1+1)*(1/2 : ℝ)^(bandIndex z.2+1)/2 := by
      simp only [pow_add, pow_succ]; ring
    rw [he]
    exact div_le_div_of_nonneg_right hp (by norm_num)
  exact ⟨bandIndex_ge_of_upper hupp, bandIndex_le_of_lower hlow⟩

def lightTag (z : Gap × Gap) : ℕ × ℕ :=
  (bandIndex z.1, 2*(bandIndex z.2-1)+
    (bandIndex (lightGap z)-(bandIndex z.1+(bandIndex z.2-1)+3)))

def lightDest (x : ℕ × ℕ) : ℕ := x.1+x.2/2+3+x.2%2

theorem measurable_lightTag : Measurable lightTag := by
  exact (measurable_of_countable (fun x : ℕ × ℕ × ℕ =>
    (x.1, 2*(x.2.1-1)+(x.2.2-(x.1+(x.2.1-1)+3))))).comp
    ((measurable_bandIndex.comp measurable_fst).prodMk
      ((measurable_bandIndex.comp measurable_snd).prodMk
        (measurable_bandIndex.comp measurable_lightGap)))

theorem lightTag_multiplier {z : Gap × Gap} (hv : (z.2 : ℝ) ≤ 1/4) :
    (lightTag z).2/2+1 = bandIndex z.2 := by
  have hj : 1 ≤ bandIndex z.2 := bandIndex_ge_of_upper (by norm_num; exact hv)
  have hb := lightGap_bands z
  dsimp [lightTag]
  omega

theorem lightTag_destination {z : Gap × Gap} (hv : (z.2 : ℝ) ≤ 1/4) :
    lightDest (lightTag z) = bandIndex (lightGap z) := by
  have hj : 1 ≤ bandIndex z.2 := bandIndex_ge_of_upper (by norm_num; exact hv)
  have hb := lightGap_bands z
  dsimp [lightTag, lightDest]
  omega

theorem lightGap_inverseSquare (z : Gap × Gap) :
    (lightGap z : ℝ)⁻¹^2 ≤ (4 : ℝ)^(bandIndex z.2+3)*(z.1 : ℝ)⁻¹^2 := by
  have hv : (z.2 : ℝ)⁻¹ ≤ (2 : ℝ)^(bandIndex z.2+2) := by
    have h := inv_anti₀ (by positivity : 0 < (1/2 : ℝ)^(bandIndex z.2+2))
      (mem_bandIndex z.2).1.le
    simpa only [one_div, inv_pow, inv_inv] using h
  have hs := pow_le_pow_left₀ (inv_nonneg.mpr z.2.property.1.le) hv 2
  have he : ((2 : ℝ)^(bandIndex z.2+2))^2 = (4 : ℝ)^(bandIndex z.2+2) := by
    rw [← pow_mul, Nat.mul_comm, pow_mul]; norm_num
  rw [he] at hs
  have hm := mul_le_mul_of_nonneg_left hs (by positivity : 0 ≤ 4*(z.1 : ℝ)⁻¹^2)
  change ((z.1 : ℝ)*(z.2 : ℝ)/2)⁻¹^2 ≤ _
  rw [inv_div, div_eq_mul_inv, mul_inv, mul_pow, mul_pow, pow_succ _ (bandIndex z.2+2)]
  norm_num only [sq]
  nlinarith only [hm]

end ThresholdHC.ArbitraryLawAdaptation
