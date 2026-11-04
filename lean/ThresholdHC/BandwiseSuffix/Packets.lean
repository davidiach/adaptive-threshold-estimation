import ThresholdHC.EntropyTail.HardSelection

noncomputable section
open MeasureTheory Set Real
open scoped ENNReal Classical
namespace ThresholdHC.BandwiseSuffix
open ThresholdHC.Tier6 (Gap)
open ThresholdHC.EntropyTail

/-- Atomic mass carrying exactly e units of inverse-square cost. -/
def packet (e : ℝ) (x : Gap) : Measure Gap :=
  ENNReal.ofReal (e * (x:ℝ)^2) • Measure.dirac x

theorem packet_le_restrict {μ : Measure Gap} [IsFiniteMeasure μ] {x : Gap} {s : Set Gap}
    (hx : x ∈ s) {e : ℝ} (he : e ≤ μ.real {x} / (x:ℝ)^2) :
    packet e x ≤ μ.restrict s := by
  apply le_trans _ (Measure.restrict_mono (singleton_subset_iff.mpr hx) (le_refl μ))
  rw [Measure.restrict_singleton]
  have hw := (le_div_iff₀ (pow_pos x.property.1 2)).mp he
  have hm := ENNReal.ofReal_le_ofReal hw
  rw [measureReal_def, ENNReal.ofReal_toReal (measure_ne_top _ _)] at hm
  intro A
  simp only [packet, Measure.smul_apply, smul_eq_mul]
  exact mul_le_mul_left hm _

theorem packet_bandCost {e : ℝ} (he : 0 ≤ e) (x : Gap) (j : ℕ) :
    bandCost (packet e x) j = if x ∈ band j then ENNReal.ofReal e else 0 := by
  classical
  rw [packet, bandCost, Measure.restrict_smul, lintegral_smul_measure]
  change _ * bandCost (Measure.dirac x) j = _
  rw [bandCost_dirac]
  by_cases hx : x ∈ band j
  · rw [ite_eq_left hx, indicator_of_mem hx, ← ENNReal.ofReal_mul (mul_nonneg he (sq_nonneg _))]
    congr 1
    field_simp [x.property.1.ne']
  · simp [hx]

/-- Tail cost saved per unit of inverse-square cost. -/
def saving (h : ℝ) (x : Gap) : ℝ := min ((x:ℝ)^2) (h*x)

theorem packet_tailCost {e : ℝ} (he : 0 ≤ e) (x : Gap) (h : ℝ) :
    tailCost (packet e x) h = ENNReal.ofReal (e * saving h x) := by
  rw [packet, tailCost_smul, tailCost_dirac, ← ENNReal.ofReal_mul (mul_nonneg he (sq_nonneg _))]
  congr 1
  rw [mul_assoc, mul_min_of_nonneg _ _ (sq_nonneg _), mul_one]
  have hd : (x:ℝ)^2 * (h/(x:ℝ)) = h*x := by field_simp [x.property.1.ne']
  rw [hd, saving]

theorem saving_strictMono {h : ℝ} (hh : 0 < h) : StrictMono (saving h) := by
  intro x y hxy
  have h : (x:ℝ) < (y:ℝ) := hxy
  exact lt_min ((min_le_left _ _).trans_lt (pow_lt_pow_left₀ h x.property.1.le (by decide : 2 ≠ 0)))
    ((min_le_right _ _).trans_lt (mul_lt_mul_of_pos_left h hh))

theorem packet_strict_gain {e h : ℝ} (he : 0 < e) (hh : 0 < h) {x y : Gap} (hxy : x < y) :
    tailCost (packet e x) h < tailCost (packet e y) h := by
  rw [packet_tailCost he.le, packet_tailCost he.le]
  exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg
    (mul_nonneg he.le (le_min (sq_nonneg _) (mul_nonneg hh.le x.property.1.le)))).mpr
      (mul_lt_mul_of_pos_left (saving_strictMono hh hxy) he)

end ThresholdHC.BandwiseSuffix
