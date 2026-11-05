import ThresholdHC.SubcriticalPower.Full
noncomputable section
open MeasureTheory ThresholdHC.Tier6 ThresholdHC.RareAboveTwo ThresholdHC.EntropyTailQuantile
open ThresholdHC.Confidence ThresholdHC.ConfidenceTransfer ThresholdHC.SubcriticalPower
open scoped ENNReal

example (μ : Measure Gap) [IsProbabilityMeasure μ] {ρ : ℝ} (hr : 0 < ρ) (hu : ρ ≤ 1) (x : ℝ) :
    (quantileTail μ ρ).real {d : Gap | (d:ℝ) ≤ x} = min ρ (μ.real {d : Gap | (d:ℝ) ≤ x}) :=
  quantile_cdf μ hr hu x

example (ν : Measure Gap) [IsFiniteMeasure ν] {h : ℝ} (hh : 0 ≤ h) :
    tailModulus ν h = ∫ t in (0:ℝ)..1, ν.real {d : Gap | (d:ℝ) ≤ h/t} := tail_layers ν hh

example {α a ρ B : ℝ} (hα : 0 < α) (hu : α < 1) (ha : 0 < a) (hr : 0 ≤ ρ) (hb : 1 ≤ B) :
    ∃ (R : Type) (_ : MeasurableSpace R) (A : AdaptiveEstimator R),
    ∀ (ν : Measure Gap) [IsProbabilityMeasure ν], PowerMargin ν α a →
      RareBudget ν A ρ B ∧ rareRisk ν A ρ ≤
        ENNReal.ofReal ((512/(1-α))*min ρ (((Real.sqrt B)⁻¹/a)^α)) :=
  sublinear_rms_family hα hu ha hr hb

example {α a ρ B δ : ℝ} (hα : 0 < α) (hu : α < 1) (ha : 0 < a) (hr : 0 ≤ ρ)
    (hb : 1 ≤ B) (hd : 0 < δ) (hd' : δ ≤ 1/4) :
    ∃ (R : Type) (_ : MeasurableSpace R) (A : AdaptiveEstimator R),
    ∀ (ν : Measure Gap) [IsProbabilityMeasure ν], PowerMargin ν α a →
      RareBudget ν A ρ B ∧ ∀ q : SignLaw, RarePrior ν ρ q →
        failureProbability ν A q ((8192/(1-α))*min ρ ((Real.sqrt (Real.log (1/δ)/B)/a)^α)) ≤ ENNReal.ofReal δ :=
  sublinear_confidence_family hα hu ha hr hb hd hd'

example (μ : Measure Gap) [IsProbabilityMeasure μ] {α a ρ B δ : ℝ}
    (hα : 0 < α) (hu : α < 1) (ha : 0 < a) (hm : ExactPowerLaw μ α a)
    (hr : 0 < ρ) (hr' : ρ ≤ 1/4) (hb : 1 ≤ B) (hd : 0 < δ) (hd' : δ ≤ 1/4) :
    let z := min ρ (((Real.sqrt B)⁻¹/a)^α)
    let w := min ρ ((Real.sqrt (Real.log (1/δ)/B)/a)^α)
    (ENNReal.ofReal (z/32) ≤ rareMinimaxRisk μ ρ B ∧ rareMinimaxRisk μ ρ B ≤ ENNReal.ofReal ((512/(1-α))*z)) ∧
    (ENNReal.ofReal (w/960) ≤ rareConfidenceRadius μ ρ B δ ∧ rareConfidenceRadius μ ρ B δ ≤ ENNReal.ofReal ((8192/(1-α))*w)) :=
  sublinear_rates μ hα hu ha hm hr hr' hb hd hd'
#print axioms ThresholdHC.SubcriticalPower.mass_le_tail
#print axioms ThresholdHC.SubcriticalPower.power_confidence_lower
#print axioms ThresholdHC.SubcriticalPower.power_rms_lower
#print axioms ThresholdHC.SubcriticalPower.power_tail_floor
#print axioms ThresholdHC.SubcriticalPower.quantile_cdf
#print axioms ThresholdHC.SubcriticalPower.sublinear_confidence_family
#print axioms ThresholdHC.SubcriticalPower.sublinear_modulus
#print axioms ThresholdHC.SubcriticalPower.sublinear_rates
#print axioms ThresholdHC.SubcriticalPower.sublinear_rms_family
#print axioms ThresholdHC.SubcriticalPower.tail_layers
