import ThresholdHC.AnytimeLower.ObservedTesting

noncomputable section
open MeasureTheory InformationTheory Real Set
open scoped ENNReal
namespace ThresholdHC.AnytimeLower
open ThresholdHC.Tier3 ThresholdHC.Tier6 ThresholdHC.RareAboveTwo

theorem online_prefix_accuracy {R : Type} [MeasurableSpace R]
    (μ : Measure Gap) [IsProbabilityMeasure μ] (A : AdaptiveEstimator R)
    (H : ∀ n, R × Prefix n → ℝ) (hH : ∀ n, Measurable (H n))
    {ρ δ : ℝ} (t : ℕ → ℝ) (hacc : OnlineAccuracy μ A H ρ δ t)
    (q : SignLaw) (hq : RarePrior μ ρ q) (n : ℕ) :
    1-δ ≤ (observablePrefixLaw μ A q n).real {x | |H n x-signMean μ q.val| ≤ t n} := by
  have hm : MeasurableSet {x | |H n x-signMean μ q.val| ≤ t n} :=
    measurableSet_le (((hH n).sub measurable_const).abs) measurable_const
  change 1-δ ≤ ((experimentLaw μ A q).map (prefixData n)).real _
  rw [map_measureReal_apply (measurable_prefixData n) hm]
  exact (hacc q hq).trans (measureReal_mono (fun _ hx => hx n))

theorem prefix_two_point_radius {R : Type} [MeasurableSpace R]
    (μ : Measure Gap) [IsProbabilityMeasure μ] (A : AdaptiveEstimator R)
    (H : ∀ n, R × Prefix n → ℝ) (hH : ∀ n, Measurable (H n))
    {ρ δ : ℝ} (hd : δ ≤ 1/4) (t : ℕ → ℝ) (hacc : OnlineAccuracy μ A H ρ δ t)
    (q r : SignLaw) (hq : RarePrior μ ρ q) (hr : RarePrior μ ρ r) (n : ℕ)
    (hkl : klDiv (observablePrefixLaw μ A r n) (observablePrefixLaw μ A q n) <
      ENNReal.ofReal (1/2)) :
    (signMean μ r.val-signMean μ q.val)/2 ≤ t n := by
  by_contra hn
  have ht : t n < (signMean μ r.val-signMean μ q.val)/2 := not_le.mp hn
  let s := {x : R × Prefix n | (signMean μ r.val+signMean μ q.val)/2 < H n x}
  have hs : MeasurableSet s := measurableSet_lt measurable_const (hH n)
  have hp : (3/4:ℝ) ≤ (observablePrefixLaw μ A r n).real s := by
    have ha := online_prefix_accuracy μ A H hH t hacc r hr n
    have he : {x | |H n x-signMean μ r.val| ≤ t n} ⊆ s := by
      intro x hx
      change |H n x-signMean μ r.val| ≤ t n at hx
      have hh := (abs_le.mp hx).1
      dsimp [s]
      linarith
    exact (by linarith : (3/4:ℝ) ≤ 1-δ).trans (ha.trans (measureReal_mono he))
  have hq' : (observablePrefixLaw μ A q n).real s ≤ 1/4 := by
    have ha := online_prefix_accuracy μ A H hH t hacc q hq n
    have he : {x | |H n x-signMean μ q.val| ≤ t n} ⊆ sᶜ := by
      intro x hx
      change |H n x-signMean μ q.val| ≤ t n at hx
      have hh := (abs_le.mp hx).2
      change ¬(signMean μ r.val+signMean μ q.val)/2 < H n x
      linarith
    have hc := ha.trans (measureReal_mono he)
    rw [probReal_compl_eq_one_sub hs] at hc
    linarith
  exact (klDiv_event_separation _ _ s hs hp hq').not_gt hkl

end ThresholdHC.AnytimeLower
