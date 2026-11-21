import ThresholdHC.AffineComparison.Specification
import ThresholdHC.StoppingProgram.AffinityRisk

/-! Testing by affinity. If one estimator has squared risk at most `r^2`
under two laws whose Hellinger affinity is at least `1/2`, with targets `a`
under the first and `b` under the second, then `a - b ≤ 4r`. This replaces the total-variation threshold test of
the source (display (4) of `lem:comparison`), whose factor is
`sqrt (2/(1-sqrt 3/2))`, by the direct bound of `affinity_squared_risk`. -/

noncomputable section
open MeasureTheory
namespace ThresholdHC.AffineComparison
open ThresholdHC.CriticalEntropy
open ThresholdHC.Tier6 (squaredRisk)

theorem difference_le_of_affinity {Ω : Type} [MeasurableSpace Ω]
    (P Q : Measure Ω) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (f : Ω → ℝ) (hf : Measurable f) (a b r : ℝ) (hr : 0 ≤ r)
    (hP : squaredRisk P f a ≤ ENNReal.ofReal (r^2))
    (hQ : squaredRisk Q f b ≤ ENNReal.ofReal (r^2))
    (hA : 1/2 ≤ (hellingerAffinity P Q).toReal) :
    a-b ≤ 4*r := by
  have h := (ThresholdHC.StoppingProgram.affinity_squared_risk P Q f hf a b).trans
    (max_le hP hQ)
  rw [ENNReal.ofReal_le_ofReal_iff (sq_nonneg r)] at h
  have hA2 : 1/4 ≤ (hellingerAffinity P Q).toReal^2 := by nlinarith
  have h16 : (a-b)^2 ≤ (4*r)^2 := by nlinarith [sq_nonneg (b-a)]
  by_contra hc
  have hc' : 4*r < a-b := lt_of_not_ge hc
  nlinarith

end ThresholdHC.AffineComparison
