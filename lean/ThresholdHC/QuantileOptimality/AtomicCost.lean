import ThresholdHC.QuantileOptimality.Specification
import ThresholdHC.BandwiseSuffix.Packets

noncomputable section
open MeasureTheory Real Set
open scoped ENNReal BigOperators Classical
namespace ThresholdHC.QuantileOptimality
open ThresholdHC.Tier6 (Gap)
open ThresholdHC.EntropyTailQuantile
open ThresholdHC.BandwiseSuffix (packet)

@[instance]
theorem packet_finite (e : ℝ) (d : Gap) : IsFiniteMeasure (packet e d) := by
  constructor
  simp [packet]

theorem bandCost_smul (σ : Measure Gap) {c : ℝ} (hc : 0 ≤ c) (j : ℕ) :
    bandCost (ENNReal.ofReal c • σ) j = c*bandCost σ j := by
  simp only [bandCost,Measure.restrict_smul,integral_smul_measure,
    ENNReal.toReal_ofReal hc,smul_eq_mul]

theorem measureCostEntropy_smul (σ : Measure Gap) {c : ℝ} (hc : 0 ≤ c) :
    measureCostEntropy (ENNReal.ofReal c • σ) = ENNReal.ofReal c*measureCostEntropy σ := by
  unfold measureCostEntropy
  rw [ENNReal.mul_iSup]
  apply iSup_congr
  intro n
  simp only [bandCost_smul σ hc,costEntropy_smul,ENNReal.ofReal_mul hc]

theorem packet_real_mass {e : ℝ} (he : 0 ≤ e) (d : Gap) :
    (packet e d).real univ=e*(d : ℝ)^2 := by
  simp [packet,measureReal_def,ENNReal.toReal_ofReal (mul_nonneg he (sq_nonneg _))]

theorem packet_real_bandCost {e : ℝ} (he : 0 ≤ e) (d : Gap) (j : ℕ) :
    bandCost (packet e d) j = if d ∈ band j then e else 0 := by
  classical
  have hp := ThresholdHC.BandwiseSuffix.packet_bandCost he d j
  rw [← ThresholdHC.EntropyTail.quantile_band_eq] at hp
  rw [ThresholdHC.EntropyTail.quantile_bandCost_eq,hp]
  split_ifs
  · exact ENNReal.toReal_ofReal he
  · rfl

theorem packet_entropy_le {e : ℝ} (he : 0 ≤ e) (d : Gap) :
    measureCostEntropy (packet e d) ≤ ENNReal.ofReal e := by
  have hc : 0 ≤ e*(d : ℝ)^2 := mul_nonneg he (sq_nonneg _)
  rw [packet,measureCostEntropy_smul _ hc]
  have hd := (ThresholdHC.EntropyTail.quantile_measureCostEntropy_le (Measure.dirac d)).trans
    (ThresholdHC.EntropyTail.gamma_dirac_le d)
  have h := mul_le_mul' (le_refl (ENNReal.ofReal (e*(d : ℝ)^2))) hd
  apply h.trans_eq
  rw [← ENNReal.ofReal_mul hc]
  congr 1
  field_simp [d.property.1.ne']

theorem packet_entropy_toReal_le {e : ℝ} (he : 0 ≤ e) (d : Gap) :
    (measureCostEntropy (packet e d)).toReal ≤ e := by
  have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top (packet_entropy_le he d)
  simpa only [ENNReal.toReal_ofReal he] using h

end ThresholdHC.QuantileOptimality
