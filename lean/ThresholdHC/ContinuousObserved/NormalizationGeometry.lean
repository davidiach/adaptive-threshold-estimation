import ThresholdHC.ContinuousObserved.Normalization

noncomputable section
open Set
namespace ThresholdHC.ContinuousObserved

theorem inverseNormalizedGap_strictMono : StrictMono inverseNormalizedGap :=
  strictMono_of_hasDerivAt_pos hasDerivAt_inverseNormalizedGap inverseSlope_pos

theorem inverseNormalizedGap_zero : inverseNormalizedGap 0 = 0 := by
  simp [inverseNormalizedGap]

theorem inverseNormalizedGap_endpoint : inverseNormalizedGap (normalizedGap (1 / 4)) = 1 / 4 :=
  inverse_normalized_gap (by norm_num)

def normalizedSupport : Set ℝ := Ioc 0 (normalizedGap (1 / 4))

theorem normalizedGap_mem_support {d : ℝ} (hd : d ∈ Ioc (0 : ℝ) (1 / 4)) :
    normalizedGap d ∈ normalizedSupport := by
  have hi : inverseNormalizedGap (normalizedGap d) = d :=
    inverse_normalized_gap (by rw [abs_of_pos hd.1]; linarith [hd.2])
  constructor
  · apply inverseNormalizedGap_strictMono.lt_iff_lt.mp
    simpa only [inverseNormalizedGap_zero,hi] using hd.1
  · apply inverseNormalizedGap_strictMono.le_iff_le.mp
    simpa only [inverseNormalizedGap_endpoint,hi] using hd.2

theorem inverseNormalizedGap_mem_interval {z : ℝ} (hz : z ∈ normalizedSupport) :
    inverseNormalizedGap z ∈ Ioc (0 : ℝ) (1 / 4) := by
  constructor
  · simpa only [inverseNormalizedGap_zero] using inverseNormalizedGap_strictMono hz.1
  · simpa only [inverseNormalizedGap_endpoint] using inverseNormalizedGap_strictMono.monotone hz.2

theorem normalized_inverse_gap {z : ℝ} (hz : z ∈ normalizedSupport) :
    normalizedGap (inverseNormalizedGap z) = z := by
  apply inverseNormalizedGap_strictMono.injective
  apply inverse_normalized_gap
  have hi := inverseNormalizedGap_mem_interval hz
  rw [abs_of_pos hi.1]
  linarith [hi.2]

theorem normalized_preimage (S : Set ℝ) :
    normalizedGap ⁻¹' S ∩ Ioc (0 : ℝ) (1 / 4) =
      inverseNormalizedGap '' (S ∩ normalizedSupport) := by
  ext d
  constructor
  · rintro ⟨hS,hd⟩
    refine ⟨normalizedGap d,⟨hS,normalizedGap_mem_support hd⟩,?_⟩
    apply inverse_normalized_gap
    rw [abs_of_pos hd.1]
    linarith [hd.2]
  · rintro ⟨z,⟨hS,hz⟩,rfl⟩
    refine ⟨?_,inverseNormalizedGap_mem_interval hz⟩
    simpa only [mem_preimage,normalized_inverse_gap hz] using hS

end ThresholdHC.ContinuousObserved
