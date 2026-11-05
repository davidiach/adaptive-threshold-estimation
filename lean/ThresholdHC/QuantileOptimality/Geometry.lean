import ThresholdHC.QuantileOptimality.Specification

noncomputable section
open Real
namespace ThresholdHC.QuantileOptimality
open ThresholdHC.Tier6 (Gap)
open ThresholdHC.EntropyTailQuantile ThresholdHC.QuantileSharpLaw

def edgeGap (n : ℕ) : Gap :=
  ⟨bandEdge n,bandEdge_pos n,by
    have h := bandEdge_antitone (Nat.zero_le n)
    simpa [bandEdge] using h⟩

theorem edgeGap_band (n : ℕ) : edgeGap n ∈ band n := by
  change bandEdge n/2 < bandEdge n ∧ bandEdge n ≤ bandEdge n
  exact ⟨by linarith [bandEdge_pos n],le_rfl⟩

def aboveGap {n : ℕ} (i : Fin n) (η : ℝ) (hη : 0 < η) (hη1 : η ≤ 1) : Gap :=
  ⟨bandEdge n*(2 : ℝ)^i.val*(1+η),by positivity [bandEdge_pos n],by
    have he := outward_band_edge i
    have hm := mul_le_mul_of_nonneg_left hη1
      (show 0 ≤ bandEdge n*(2 : ℝ)^i.val by positivity [bandEdge_pos n])
    have htop : bandEdge i.rev.val ≤ 1/2 :=
      (bandEdge_antitone (Nat.zero_le i.rev.val)).trans_eq (by norm_num [bandEdge])
    nlinarith only [he,hm,htop]⟩

theorem aboveGap_band {n : ℕ} (i : Fin n) {η : ℝ} (hη : 0 < η) (hη1 : η ≤ 1) :
    aboveGap i η hη hη1 ∈ band i.rev.val := by
  change bandEdge i.rev.val/2 < bandEdge n*(2 : ℝ)^i.val*(1+η) ∧
    bandEdge n*(2 : ℝ)^i.val*(1+η) ≤ bandEdge i.rev.val
  have he := outward_band_edge i
  have hr : 0 < bandEdge n*(2 : ℝ)^i.val := by positivity [bandEdge_pos n]
  have hp := mul_pos hr hη
  have hm := mul_le_mul_of_nonneg_left hη1 hr.le
  constructor <;> nlinarith only [he,hp,hm]

theorem aboveGap_gt_boundary {n : ℕ} (i : Fin n) {η : ℝ} (hη : 0 < η) (hη1 : η ≤ 1) :
    bandEdge n < (aboveGap i η hη hη1 : ℝ) := by
  have hr : 0 < bandEdge n*(2 : ℝ)^i.val := by positivity [bandEdge_pos n]
  have hp := mul_pos hr hη
  have hm := mul_le_mul_of_nonneg_left (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2) : 1 ≤ (2 : ℝ)^i.val)
    (bandEdge_pos n).le
  change bandEdge n < bandEdge n*(2 : ℝ)^i.val*(1+η)
  nlinarith only [hp,hm]

theorem aboveGap_lt_half {n : ℕ} (i : Fin n) {η : ℝ} (hη : 0 < η) (hη1 : η ≤ 1)
    (hi : i.val+1 < n) : (aboveGap i η hη hη1 : ℝ) < 1/2 := by
  have hrev : 1 ≤ i.rev.val := by simp only [Fin.val_rev]; omega
  calc
    _ ≤ bandEdge i.rev.val := (aboveGap_band i hη hη1).2
    _ ≤ bandEdge 1 := bandEdge_antitone hrev
    _ < 1/2 := by norm_num [bandEdge]

end ThresholdHC.QuantileOptimality
