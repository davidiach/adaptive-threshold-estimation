
import ThresholdHC.AnytimeLower.ObservedTesting
noncomputable section
set_option linter.unusedVariables false
open MeasureTheory InformationTheory Real Set Filter
open scoped ENNReal Topology
open ThresholdHC.AnytimeLower ThresholdHC.Tier3 ThresholdHC.Tier6 ThresholdHC.RareAboveTwo

example : ∀ {p q : ℝ} (hp : 0 ≤ p ∧ p ≤ 1) (hq : 0 < q ∧ q < 1),
    -p*log q-log 2 ≤ ThresholdHC.klB p q := @binary_event_log_bound

example : ∀ {Ω : Type} [MeasurableSpace Ω]
    (P Q : Measure Ω) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (s : Set Ω) (hs : MeasurableSet s) {δ K : ℝ}
    (hd : 0 ≤ δ ∧ δ ≤ 1/2) (hK : 0 ≤ K)
    (hP : 1-δ ≤ P.real s) (hkl : klDiv P Q ≤ ENNReal.ofReal K),
    exp (-K/(1-δ))/4 ≤ Q.real s := @event_probability_lower

example : ∀ {Ω : Type} [MeasurableSpace Ω]
    {X : ℕ → Type} [∀ k, MeasurableSpace (X k)]
    (Q : Measure Ω) [IsProbabilityMeasure Q]
    (P : ℕ → Measure Ω) [∀ k, IsProbabilityMeasure (P k)]
    (E : ℕ → Set Ω) (hE : ∀ k, MeasurableSet (E k))
    (obs : ∀ k, Ω → X k) (hobs : ∀ k, Measurable (obs k))
    (A : ∀ k, Set (X k)) (hA : ∀ k, MeasurableSet (A k))
    (hread : ∀ k, obs k ⁻¹' A k = firstCrossing E k)
    {δ : ℝ} (hd : 0 ≤ δ ∧ δ ≤ 1/2) (K : ℕ → ℝ) (hK : ∀ k, 0 ≤ K k)
    (hpower : ∀ k, 1-δ ≤ (P k).real (firstCrossing E k))
    (herror : Q.real (⋃ k, E k) ≤ δ)
    (hkl : ∀ k, klDiv ((P k).map (obs k)) (Q.map (obs k)) ≤ ENNReal.ofReal (K k))
    (s : Finset ℕ),
    ∑ k ∈ s, exp (-K k/(1-δ)) ≤ 4*δ := @firstCrossing_information_budget

example : ∀ {Ω : Type} [MeasurableSpace Ω]
    {X : ℕ → Type} [∀ k, MeasurableSpace (X k)]
    (Q : Measure Ω) [IsProbabilityMeasure Q]
    (P : ℕ → Measure Ω) [∀ k, IsProbabilityMeasure (P k)]
    (E : ℕ → Set Ω) (hE : ∀ k, MeasurableSet (E k))
    (obs : ∀ k, Ω → X k) (hobs : ∀ k, Measurable (obs k))
    (A : ∀ k, Set (X k)) (hA : ∀ k, MeasurableSet (A k))
    (hread : ∀ k, obs k ⁻¹' A k = firstCrossing E k)
    {δ : ℝ} (hd : 0 ≤ δ ∧ δ ≤ 1/2) (K : ℕ → ℝ) (hK : ∀ k, 0 ≤ K k)
    (hpower : ∀ k, 1-δ ≤ (P k).real (firstCrossing E k))
    (herror : Q.real (⋃ k, E k) ≤ δ)
    (hkl : ∀ k, klDiv ((P k).map (obs k)) (Q.map (obs k)) ≤ ENNReal.ofReal (K k)),
    Summable (fun k => exp (-K k/(1-δ))) := @firstCrossing_information_summable

example : ∀ {Ω : Type} [MeasurableSpace Ω]
    {X : ℕ → Type} [∀ k, MeasurableSpace (X k)]
    (Q : Measure Ω) [IsProbabilityMeasure Q]
    (P : ℕ → Measure Ω) [∀ k, IsProbabilityMeasure (P k)]
    (z : ℕ → Ω → ℝ) (hz : ∀ k, Measurable (z k))
    (obs : ∀ k, Ω → X k) (hobs : ∀ k, Measurable (obs k))
    (readback : ∀ k, ℕ → X k → ℝ) (hr : ∀ k i, Measurable (readback k i))
    (hread : ∀ k i, i ≤ k → ∀ x, readback k i (obs k x) = z i x)
    (θ : ℝ) (a t : ℕ → ℝ) (ha : ∀ i, 0 < a i)
    (hsep : ∀ i k, i < k → 3*a k ≤ a i) (hw : ∀ i, t i < a i/6)
    {δ : ℝ} (hd : 0 ≤ δ ∧ δ ≤ 1/2)
    (hbase : 1-δ ≤ Q.real {x | ∀ i, |z i x-θ| ≤ t i})
    (halt : ∀ k, 1-δ ≤ (P k).real {x | ∀ i, |z i x-(θ+a k)| ≤ t i})
    (K : ℕ → ℝ) (hK : ∀ k, 0 ≤ K k)
    (hkl : ∀ k, klDiv ((P k).map (obs k)) (Q.map (obs k)) ≤ ENNReal.ofReal (K k)),
    Summable (fun k => exp (-K k/(1-δ))) := @separated_accuracy_summable

example : ∀ {Ω : Type} [MeasurableSpace Ω]
    {X : ℕ → Type} [∀ k, MeasurableSpace (X k)]
    (Q : Measure Ω) [IsProbabilityMeasure Q]
    (P : ℕ → Measure Ω) [∀ k, IsProbabilityMeasure (P k)]
    (z : ℕ → Ω → ℝ) (hz : ∀ k, Measurable (z k))
    (obs : ∀ k, Ω → X k) (hobs : ∀ k, Measurable (obs k))
    (readback : ∀ k, ℕ → X k → ℝ) (hr : ∀ k i, Measurable (readback k i))
    (hread : ∀ k i, i ≤ k → ∀ x, readback k i (obs k x) = z i x)
    (θ : ℝ) (a t : ℕ → ℝ) (ha : ∀ i, 0 < a i)
    (hsep : ∀ i k, i < k → 3*a k ≤ a i)
    {δ : ℝ} (hd : 0 ≤ δ ∧ δ ≤ 1/2)
    (hbase : 1-δ ≤ Q.real {x | ∀ i, |z i x-θ| ≤ t i})
    (halt : ∀ k, 1-δ ≤ (P k).real {x | ∀ i, |z i x-(θ+a k)| ≤ t i})
    (K : ℕ → ℝ) (hK : ∀ k, 0 ≤ K k)
    (hkl : ∀ k, klDiv ((P k).map (obs k)) (Q.map (obs k)) ≤ ENNReal.ofReal (K k))
    (hdiv : ¬Summable (fun k => exp (-K k/(1-δ)))),
    ∃ᶠ k in atTop, a k/6 ≤ t k := @separated_accuracy_frequently

example : ¬Summable (fun k : ℕ => exp (-log ((k:ℝ)+2)/2)) := not_summable_half_log

example : ∀ {R : Type} [MeasurableSpace R]
    (μ : Measure Gap) [IsProbabilityMeasure μ] (A : AdaptiveEstimator R)
    (H : ∀ n, R × Prefix n → ℝ) (hH : ∀ n, Measurable (H n))
    {ρ δ : ℝ} (hd : 0 ≤ δ ∧ δ ≤ 1/2) (t : ℕ → ℝ)
    (hacc : OnlineAccuracy μ A H ρ δ t)
    (q : SignLaw) (hq : RarePrior μ ρ q)
    (r : ℕ → SignLaw) (hr : ∀ k, RarePrior μ ρ (r k))
    (a : ℕ → ℝ) (ha : ∀ k, 0 < a k)
    (hmean : ∀ k, signMean μ (r k).val = signMean μ q.val+a k)
    (hsep : ∀ i k, i < k → 3*a k ≤ a i)
    (N : ℕ → ℕ) (hN : Monotone N)
    (K : ℕ → ℝ) (hK : ∀ k, 0 ≤ K k)
    (hkl : ∀ k, klDiv (observablePrefixLaw μ A (r k) (N k))
      (observablePrefixLaw μ A q (N k)) ≤ ENNReal.ofReal (K k))
    (hdiv : ¬Summable (fun k => exp (-K k/(1-δ)))),
    ∃ᶠ k in atTop, a k/6 ≤ t (N k) := @observed_separated_frequently
#print axioms ThresholdHC.AnytimeLower.binary_event_log_bound
#print axioms ThresholdHC.AnytimeLower.event_probability_lower
#print axioms ThresholdHC.AnytimeLower.firstCrossing_information_budget
#print axioms ThresholdHC.AnytimeLower.firstCrossing_information_summable
#print axioms ThresholdHC.AnytimeLower.not_summable_half_log
#print axioms ThresholdHC.AnytimeLower.observed_separated_frequently
#print axioms ThresholdHC.AnytimeLower.separated_accuracy_frequently
#print axioms ThresholdHC.AnytimeLower.separated_accuracy_summable
