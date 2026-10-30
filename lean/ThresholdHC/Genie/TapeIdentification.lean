import ThresholdHC.CriticalEntropy.UniformCoin
import Mathlib.Probability.StrongLaw
import Mathlib.MeasureTheory.Measure.Prod

/-! An infinite Bernoulli tape identifies its parameter almost surely,
including the deterministic endpoint parameters zero and one. -/

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology BigOperators
namespace ThresholdHC.Genie
open ThresholdHC.CriticalEntropy

def bitValue (b : Bool) : ℝ := if b then 1 else 0

def empiricalMean (n : ℕ) (ω : ℕ → Bool) : ℝ :=
  (∑ i ∈ Finset.range n, bitValue (ω i))/(n:ℝ)

theorem measurable_bitValue : Measurable bitValue := measurable_of_countable _

theorem tape_parameter_identification (p : unitInterval) :
    ∀ᵐ ω ∂ThresholdHC.Tier2.tapeMeasure p,
      Tendsto (fun n => empiricalMean n ω) atTop (𝓝 (p:ℝ)) := by
  let μ := ThresholdHC.Tier2.tapeMeasure p
  let X : ℕ → (ℕ → Bool) → ℝ := fun i ω => bitValue (ω i)
  have hm (i : ℕ) : Measurable (X i) := measurable_bitValue.comp (measurable_pi_apply i)
  have hi : Integrable (X 0) μ := Integrable.of_bound (hm 0).aestronglyMeasurable 1
    (Filter.Eventually.of_forall (fun ω => by cases he : ω 0 <;> simp [X,bitValue,he]))
  have hmap (i : ℕ) : μ.map (X i) = (bernoulliMeasure true false p).map bitValue := by
    change (ThresholdHC.Tier2.tapeMeasure p).map (bitValue ∘ (fun ω : ℕ → Bool => ω i)) = _
    rw [←Measure.map_map measurable_bitValue (measurable_pi_apply i)]
    exact congrArg (fun ν : Measure Bool => ν.map bitValue)
      (measurePreserving_eval_infinitePi (fun _ : ℕ => bernoulliMeasure true false p) i).map_eq
  have hind : Pairwise (fun i j => IndepFun (X i) (X j) μ) := by
    intro i j hij
    exact (iIndepFun_infinitePi (P := fun _ : ℕ => bernoulliMeasure true false p)
      (X := fun _ => bitValue) (fun _ => measurable_bitValue)).indepFun hij
  have hid (i : ℕ) : IdentDistrib (X i) (X 0) μ μ :=
    ⟨(hm i).aemeasurable,(hm 0).aemeasurable,(hmap i).trans (hmap 0).symm⟩
  have hmean : (∫ ω, X 0 ω ∂μ) = (p:ℝ) := by
    change (∫ ω, bitValue (ω 0) ∂μ) = _
    rw [←integral_map (measurable_pi_apply 0).aemeasurable measurable_bitValue.aestronglyMeasurable]
    have he : μ.map (fun ω : ℕ → Bool => ω 0) = bernoulliMeasure true false p :=
      (measurePreserving_eval_infinitePi (fun _ : ℕ => bernoulliMeasure true false p) 0).map_eq
    rw [he,integral_bernoulliMeasure]
    simp [bitValue]
  simpa only [hmean,empiricalMean,X] using strong_law_ae_real X hi hind hid

theorem measurable_empiricalMean (n : ℕ) : Measurable (empiricalMean n) := by
  unfold empiricalMean
  exact (Finset.measurable_sum _ (fun i _ => measurable_bitValue.comp (measurable_pi_apply i))).div_const _

def tapeParameter (ω : ℕ → Bool) : ℝ := limsup (fun n => empiricalMean n ω) atTop

theorem measurable_tapeParameter : Measurable tapeParameter :=
  Measurable.limsup measurable_empiricalMean

theorem tapeParameter_ae (p : unitInterval) :
    ∀ᵐ ω ∂ThresholdHC.Tier2.tapeMeasure p, tapeParameter ω = (p:ℝ) := by
  filter_upwards [tape_parameter_identification p] with ω hω
  exact hω.limsup_eq

theorem uniform_tapeParameter_ae (p : unitInterval) :
    ∀ᵐ u ∂uniformTapeMeasure, tapeParameter (uniformCoinTape p u) = (p:ℝ) := by
  have ht := tapeParameter_ae p
  rw [←uniformCoinTape_map] at ht
  exact ae_of_ae_map (measurable_uniformCoinTape.comp (measurable_const.prodMk measurable_id)).aemeasurable ht

theorem parameter_mixture_identification (κ : Measure unitInterval) [IsFiniteMeasure κ] :
    ∀ᵐ z ∂κ.prod uniformTapeMeasure, tapeParameter (uniformCoinTape z.1 z.2) = (z.1:ℝ) := by
  apply (Measure.ae_prod_iff_ae_ae (measurableSet_eq_fun
    (measurable_tapeParameter.comp measurable_uniformCoinTape) (measurable_subtype_coe.comp measurable_fst))).mpr
  exact Filter.Eventually.of_forall uniform_tapeParameter_ae

end ThresholdHC.Genie
