import ThresholdHC.AnytimeLower.FrequentTesting
import ThresholdHC.AnytimeLower.Quartet

noncomputable section
open MeasureTheory InformationTheory Real Set Filter
open scoped ENNReal Topology
namespace ThresholdHC.AnytimeLower
open ThresholdHC.Tier3 ThresholdHC.Tier6 ThresholdHC.RareAboveTwo

def prefixData {R : Type} (n : ℕ) (x : PopulationSeed R × ProcessTape) :
    R × Prefix n := (x.1.1,processPrefix n x.2)

theorem measurable_prefixData {R : Type} [MeasurableSpace R] (n : ℕ) :
    Measurable (prefixData (R := R) n) :=
  measurable_fst.fst.prodMk
    (measurable_pi_iff.mpr fun i => (measurable_pi_apply i.val).comp measurable_snd)

def prefixEstimate {R : Type} (H : ∀ n, R × Prefix n → ℝ) (n : ℕ)
    (x : PopulationSeed R × ProcessTape) : ℝ := H n (prefixData n x)

/-- Simultaneous accuracy in one original online experiment. Each output
uses only the private seed and the actual observed prefix at that budget. -/
def OnlineAccuracy {R : Type} [MeasurableSpace R]
    (μ : Measure Gap) [IsProbabilityMeasure μ] (A : AdaptiveEstimator R)
    (H : ∀ n, R × Prefix n → ℝ) (ρ δ : ℝ) (t : ℕ → ℝ) : Prop :=
  ∀ q : SignLaw, RarePrior μ ρ q →
    1-δ ≤ (experimentLaw μ A q).real
      {x | ∀ n, |prefixEstimate H n x-signMean μ q.val| ≤ t n}

def prefixReadback {R : Type} (H : ∀ n, R × Prefix n → ℝ) (N : ℕ → ℕ)
    (hN : Monotone N) (k i : ℕ) (x : R × Prefix (N k)) : ℝ :=
  if hi : i ≤ k then H (N i) (x.1,fun j => x.2 (Fin.castLE (hN hi) j)) else 0

theorem measurable_prefixReadback {R : Type} [MeasurableSpace R]
    (H : ∀ n, R × Prefix n → ℝ) (hH : ∀ n, Measurable (H n))
    (N : ℕ → ℕ) (hN : Monotone N) (k i : ℕ) :
    Measurable (prefixReadback H N hN k i) := by
  unfold prefixReadback
  split_ifs
  · exact (hH _).comp (measurable_fst.prodMk
      (measurable_pi_iff.mpr fun j => (measurable_pi_apply _).comp measurable_snd))
  · exact measurable_const

theorem prefixReadback_eq {R : Type} (H : ∀ n, R × Prefix n → ℝ)
    (N : ℕ → ℕ) (hN : Monotone N) (k i : ℕ) (hi : i ≤ k)
    (x : PopulationSeed R × ProcessTape) :
    prefixReadback H N hN k i (prefixData (N k) x) = prefixEstimate H (N i) x := by
  simp only [prefixReadback,dite_eq_left hi,prefixEstimate,prefixData,processPrefix]
  rfl

/-- The sequential lower bound in the original hidden-gap experiment, for
any separated rare-prior family whose actual observable-prefix information is
bounded by a nonsummable testing schedule. -/
theorem observed_separated_frequently {R : Type} [MeasurableSpace R]
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
    (hdiv : ¬Summable (fun k => exp (-K k/(1-δ)))) :
    ∃ᶠ k in atTop, a k/6 ≤ t (N k) := by
  have hb : 1-δ ≤ (experimentLaw μ A q).real
      {x | ∀ i, |prefixEstimate H (N i) x-signMean μ q.val| ≤ t (N i)} :=
    (hacc q hq).trans (measureReal_mono (fun _ hx i => hx (N i)))
  have hp (k : ℕ) : 1-δ ≤ (experimentLaw μ A (r k)).real
      {x | ∀ i, |prefixEstimate H (N i) x-(signMean μ q.val+a k)| ≤ t (N i)} := by
    rw [← hmean k]
    exact (hacc (r k) (hr k)).trans (measureReal_mono (fun _ hx i => hx (N i)))
  exact separated_accuracy_frequently (experimentLaw μ A q)
    (fun k => experimentLaw μ A (r k))
    (fun k => prefixEstimate H (N k))
    (fun k => (hH _).comp (measurable_prefixData _))
    (fun k => prefixData (N k)) (fun k => measurable_prefixData _)
    (prefixReadback H N hN) (measurable_prefixReadback H hH N hN)
    (prefixReadback_eq H N hN) (signMean μ q.val) a (fun k => t (N k))
    ha hsep hd hb hp K hK hkl hdiv

end ThresholdHC.AnytimeLower
