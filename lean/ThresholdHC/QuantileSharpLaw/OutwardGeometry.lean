import ThresholdHC.QuantileSharpLaw.Reindex
import ThresholdHC.QuantileSharpLaw.CoreWeights
import ThresholdHC.EntropyTailQuantile.BandGeometry

noncomputable section
open Real
namespace ThresholdHC.QuantileSharpLaw
open ThresholdHC.Tier6 (Gap)
open ThresholdHC.EntropyTailQuantile

theorem outward_band_edge {n : ℕ} (i : Fin n) :
    bandEdge n*(2 : ℝ)^i.val = bandEdge i.rev.val/2 := by
  have hedge (j r : ℕ) : bandEdge (j+r)*(2 : ℝ)^r = bandEdge j := by
    rw [bandEdge,bandEdge,show j+r+1=(j+1)+r by omega,pow_add,inv_pow]
    field_simp
    norm_num [← mul_pow]
  have hindex : i.rev.val+1+i.val=n := by simp only [Fin.val_rev]; omega
  have h := hedge (i.rev.val+1) i.val
  rw [hindex,bandEdge_succ] at h
  exact h

theorem outward_band_lower {n : ℕ} {t : ℝ} (ht : t ≤ bandEdge n)
    (i : Fin n) (d : Gap) (hd : d ∈ band i.rev.val) :
    t*(2 : ℝ)^i.val ≤ (d : ℝ) := by
  have h := mul_le_mul_of_nonneg_right ht (show 0 ≤ (2 : ℝ)^i.val by positivity)
  rw [outward_band_edge] at h
  exact h.trans hd.1.le

end ThresholdHC.QuantileSharpLaw
