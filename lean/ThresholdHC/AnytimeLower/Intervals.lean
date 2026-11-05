import ThresholdHC.AnytimeLower.Full

noncomputable section
open MeasureTheory Real Set Filter
open scoped ENNReal Topology
namespace ThresholdHC.AnytimeLower
open ThresholdHC.Tier3 ThresholdHC.Tier6 ThresholdHC.RareAboveTwo

/-- Joint simultaneous coverage and deterministic half-width control,
in one actual online hidden-gap experiment. -/
def OnlineIntervalCoverage {R : Type} [MeasurableSpace R]
    (μ : Measure Gap) [IsProbabilityMeasure μ] (A : AdaptiveEstimator R)
    (L U : ∀ n, R × Prefix n → ℝ) (ρ δ : ℝ) (t : ℕ → ℝ) : Prop :=
  ∀ q : SignLaw, RarePrior μ ρ q →
    1-δ ≤ (experimentLaw μ A q).real {x | ∀ n,
      L n (prefixData n x) ≤ signMean μ q.val ∧
      signMean μ q.val ≤ U n (prefixData n x) ∧
      U n (prefixData n x)-L n (prefixData n x) ≤ 2*t n}

theorem interval_midpoint_accuracy {R : Type} [MeasurableSpace R]
    (μ : Measure Gap) [IsProbabilityMeasure μ] (A : AdaptiveEstimator R)
    (L U : ∀ n, R × Prefix n → ℝ) {ρ δ : ℝ} (t : ℕ → ℝ)
    (hc : OnlineIntervalCoverage μ A L U ρ δ t) :
    OnlineAccuracy μ A (fun n x => (L n x+U n x)/2) ρ δ t := by
  intro q hq
  apply (hc q hq).trans (measureReal_mono _)
  intro x hx n
  have hh := hx n
  change |(L n (prefixData n x)+U n (prefixData n x))/2-signMean μ q.val| ≤ t n
  exact abs_le.mpr ⟨by linarith,by linarith⟩

/-- The matching law-dependent time-uniform lower bound for observable
confidence intervals, expressed as a real half-width inequality. -/
theorem law_dependent_interval_lower {R : Type} [MeasurableSpace R]
    (μ : Measure Gap) [IsProbabilityMeasure μ]
    {ρ δ : ℝ} (hρ : 0 < ρ) (hρ4 : ρ ≤ 1/4) (hd : 0 < δ ∧ δ ≤ 1/4)
    (A : AdaptiveEstimator R) (L U : ∀ n, R × Prefix n → ℝ)
    (hL : ∀ n, Measurable (L n)) (hU : ∀ n, Measurable (U n))
    (t : ℕ → ℝ) (ht : ∀ n, 0 ≤ t n) (hc : OnlineIntervalCoverage μ A L U ρ δ t)
    (M : ℕ) :
    ∃ n : ℕ, max M 3 ≤ n ∧
      ((10:ℝ)⁻¹^22)*(ThresholdHC.EntropyTail.selection μ ρ
        ((n:ℝ)/budgetInflation δ n)).toReal ≤ t n := by
  obtain ⟨n,hn,hbound⟩ := law_dependent_online_lower μ hρ hρ4 hd A
    (fun n x => (L n x+U n x)/2) (fun n => ((hL n).add (hU n)).div_const 2) t
    (interval_midpoint_accuracy μ A L U t hc) (max M 3)
  refine ⟨n,hn,?_⟩
  have hr := ENNReal.toReal_mono ENNReal.ofReal_ne_top hbound
  simpa only [ENNReal.toReal_mul,ENNReal.toReal_ofReal (ht n),
    ENNReal.toReal_ofReal (show 0 ≤ (10:ℝ)⁻¹^22 by positivity)] using hr

end ThresholdHC.AnytimeLower
