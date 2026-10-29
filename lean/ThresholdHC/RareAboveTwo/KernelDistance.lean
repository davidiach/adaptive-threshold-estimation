import ThresholdHC.RareAboveTwo.FiniteMixture
import Mathlib.Analysis.Convex.Integral
import ThresholdHC.CriticalEntropy.FiniteRMS
import ThresholdHC.CriticalEntropy.SeedAdaptation

noncomputable section
namespace ThresholdHC.RareAboveTwo
open MeasureTheory Set ThresholdHC.CriticalEntropy

theorem probability_kernel_integrable {X I : Type} [MeasurableSpace X] [Fintype I]
    (μ : Measure X) [IsProbabilityMeasure μ] (p : X → I → ℝ)
    (hm : ∀ i, Measurable (fun x => p x i)) (hp : ∀ x i, 0 ≤ p x i)
    (hs : ∀ x, ∑ i, p x i=1) (i : I) : Integrable (fun x => p x i) μ := by
  apply Integrable.of_bound (hm i).aestronglyMeasurable 1
  apply ae_of_all
  intro x
  rw [Real.norm_eq_abs,abs_of_nonneg (hp x i)]
  calc
    _ ≤ ∑ j, p x j := Finset.single_le_sum (fun j _ => hp x j) (Finset.mem_univ i)
    _ = 1 := hs x

theorem finite_distance_integrable {X I : Type} [MeasurableSpace X] [Fintype I]
    (μ : Measure X) [IsProbabilityMeasure μ] (p q : X → I → ℝ)
    (hpm : ∀ i, Measurable (fun x => p x i)) (hqm : ∀ i, Measurable (fun x => q x i))
    (hp : ∀ x i, 0 ≤ p x i) (hq : ∀ x i, 0 ≤ q x i)
    (hps : ∀ x, ∑ i, p x i=1) (hqs : ∀ x, ∑ i, q x i=1) :
    Integrable (fun x => 1-realFiniteAffinity (p x) (q x)) μ := by
  apply Integrable.of_bound ((measurable_const.sub (realFiniteAffinity_continuous.measurable.comp
    ((Measurable.of_eval hpm).prodMk (Measurable.of_eval hqm)))).aestronglyMeasurable) 1
  apply ae_of_all
  intro x
  have hb := realFiniteAffinity_le_one (p x) (q x) (hp x) (hq x) (hps x) (hqs x)
  have hn : 0 ≤ realFiniteAffinity (p x) (q x) := Finset.sum_nonneg (fun _ _ => Real.sqrt_nonneg _)
  change ‖1-realFiniteAffinity (p x) (q x)‖ ≤ 1
  rw [Real.norm_eq_abs,abs_of_nonneg (sub_nonneg.mpr hb)]
  linarith

theorem finite_distance_integral_le {X I : Type} [MeasurableSpace X] [Fintype I]
    (μ : Measure X) [IsProbabilityMeasure μ] (p q : X → I → ℝ)
    (hpm : ∀ i, Measurable (fun x => p x i)) (hqm : ∀ i, Measurable (fun x => q x i))
    (hp : ∀ x i, 0 ≤ p x i) (hq : ∀ x i, 0 ≤ q x i)
    (hps : ∀ x, ∑ i, p x i=1) (hqs : ∀ x, ∑ i, q x i=1) :
    1-realFiniteAffinity (fun i => ∫ x, p x i ∂μ) (fun i => ∫ x, q x i ∂μ) ≤
      ∫ x, 1-realFiniteAffinity (p x) (q x) ∂μ := by
  have hpi := probability_kernel_integrable μ p hpm hp hps
  have hqi := probability_kernel_integrable μ q hqm hq hqs
  have hclosed : IsClosed {z : (I → ℝ) × (I → ℝ) | (∀ i, 0 ≤ z.1 i) ∧ (∀ i, 0 ≤ z.2 i)} :=
    by
      have hcl : IsClosed {f : I → ℝ | ∀ i, 0 ≤ f i} := by
        convert isClosed_iInter (fun i : I => isClosed_le (continuous_const : Continuous (fun _ : I → ℝ => (0 : ℝ))) (continuous_apply i)) using 1
        ext f; simp
      exact (hcl.preimage continuous_fst).inter (hcl.preimage continuous_snd)
  have h := (realFiniteDistance_convex (I := I)).map_integral_le
    (continuous_const.sub realFiniteAffinity_continuous).continuousOn hclosed
    (ae_of_all μ (fun x => ⟨hp x,hq x⟩))
    ((Integrable.of_eval hpi).prodMk (Integrable.of_eval hqi))
    (finite_distance_integrable μ p q hpm hqm hp hq hps hqs)
  rw [integral_pair (Integrable.of_eval hpi) (Integrable.of_eval hqi)] at h
  have hep : (∫ x, p x ∂μ) = fun i => ∫ x, p x i ∂μ := funext (eval_integral hpi)
  have heq : (∫ x, q x ∂μ) = fun i => ∫ x, q x i ∂μ := funext (eval_integral hqi)
  simpa only [hep,heq] using h

theorem finite_distance_sum_le {S I : Type} [Fintype S] [MeasurableSpace S]
    [MeasurableSingletonClass S] [Fintype I] (w : S → ℝ)
    (hw : ∀ s, 0 ≤ w s) (hws : ∑ s, w s=1) (p q : S → I → ℝ)
    (hp : ∀ s i, 0 ≤ p s i) (hq : ∀ s i, 0 ≤ q s i)
    (hps : ∀ s, ∑ i, p s i=1) (hqs : ∀ s, ∑ i, q s i=1) :
    1-realFiniteAffinity (fun i => ∑ s, w s*p s i) (fun i => ∑ s, w s*q s i) ≤
      ∑ s, w s*(1-realFiniteAffinity (p s) (q s)) := by
  let ν := finiteWeightMeasure w
  let : IsProbabilityMeasure ν := finiteWeightMeasure_probability w hw hws
  have he (f : S → ℝ) : (∫ s, f s ∂ν) = ∑ s, w s*f s := by
    rw [integral_fintype (finite_function_integrable ν f)]
    simp only [smul_eq_mul,ν,finiteWeightMeasure_real_singleton w hw]
  have h := finite_distance_integral_le ν p q (fun i => measurable_of_countable _)
    (fun i => measurable_of_countable _) hp hq hps hqs
  simpa only [he] using h

end ThresholdHC.RareAboveTwo
