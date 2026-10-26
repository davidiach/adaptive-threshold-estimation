import ThresholdHC.Uniform713.Common
import Mathlib.Probability.Moments.SubGaussian

/-!
The classifier's two-sided concentration interface is derived from independent
observations in [0,1] with a common mean. Bernoulli observations are a special case.
-/

noncomputable section

namespace ThresholdHC.Uniform713

open Real MeasureTheory ProbabilityTheory
open scoped NNReal

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

def prefixMean (X : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  (∑ i ∈ Finset.range n, X i ω) / n

def dyadicMean (X : ℕ → Ω → ℝ) (k : ℕ) : Ω → ℝ := prefixMean X (2 ^ k)

theorem measurable_prefixMean {X : ℕ → Ω → ℝ} (hX : ∀ i, Measurable (X i)) (n : ℕ) :
    Measurable (prefixMean X n) := by
  exact (Finset.measurable_sum _ (fun i _ => hX i)).div_const _

theorem bounded_centered_subgaussian [IsProbabilityMeasure μ]
    {X : Ω → ℝ} {p : ℝ} (hX : Measurable X)
    (hb : ∀ᵐ ω ∂μ, X ω ∈ Set.Icc (0 : ℝ) 1) (hp : ∫ ω, X ω ∂μ = p) :
    HasSubgaussianMGF (fun ω => X ω - p) (1 / 4) μ := by
  have h := hasSubgaussianMGF_of_mem_Icc hX.aemeasurable hb
  norm_num [hp] at h ⊢
  exact h

theorem prefixMean_subgaussian [IsProbabilityMeasure μ]
    {X : ℕ → Ω → ℝ} {p : ℝ} (hX : ∀ i, Measurable (X i))
    (hb : ∀ i, ∀ᵐ ω ∂μ, X i ω ∈ Set.Icc (0 : ℝ) 1)
    (hp : ∀ i, ∫ ω, X i ω ∂μ = p) (hi : iIndepFun X μ)
    {n : ℕ} (hn : 0 < n) :
    HasSubgaussianMGF (fun ω => prefixMean X n ω - p) (1 / (4 * n)) μ := by
  have hind : iIndepFun (fun i ω => X i ω - p) μ :=
    hi.comp (fun _ x => x - p) (fun _ => measurable_id.sub_const p)
  have hs := HasSubgaussianMGF.sum_of_iIndepFun hind
    (c := fun _ => (1/4 : ℝ≥0)) (s := Finset.range n)
    (fun i _ => bounded_centered_subgaussian (hX i) (hb i) (hp i))
  have hm := hs.const_mul ((n : ℝ)⁻¹)
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have heq : NNReal.mk (((n : ℝ)⁻¹)^2) (sq_nonneg _) *
      (∑ _i ∈ Finset.range n, (1/4 : ℝ≥0)) = 1 / (4 * n) := by
    apply NNReal.coe_injective
    simp only [NNReal.coe_mul, NNReal.coe_mk, Finset.sum_const, Finset.card_range,
      nsmul_eq_mul, NNReal.coe_div, NNReal.coe_one, NNReal.coe_ofNat, NNReal.coe_natCast]
    field_simp
    <;> ring
  unfold NNReal.mk at heq
  rw [heq] at hm
  apply hm.congr
  filter_upwards [] with ω
  simp only [prefixMean, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range,
    nsmul_eq_mul]
  field_simp

theorem hasMeanTails_of_independent_bounded [IsProbabilityMeasure μ]
    {X : ℕ → Ω → ℝ} {p : ℝ} (hX : ∀ i, Measurable (X i))
    (hb : ∀ i, ∀ᵐ ω ∂μ, X i ω ∈ Set.Icc (0 : ℝ) 1)
    (hp : ∀ i, ∫ ω, X i ω ∂μ = p) (hi : iIndepFun X μ) :
    HasMeanTails μ (dyadicMean X) p := by
  have hs (k : ℕ) := prefixMean_subgaussian hX hb hp hi (pow_pos (by norm_num : 0 < (2 : ℕ)) k)
  have hexp (k : ℕ) (t : ℝ) :
      -t ^ 2 / (2 * ((1 / (4 * (2 ^ k : ℕ)) : ℝ≥0) : ℝ)) =
        -2 * cap k * t ^ 2 := by
    norm_num [cap]
    field_simp
    <;> ring
  refine ⟨fun k => measurable_prefixMean hX _, ?_, ?_⟩
  · intro k t ht
    simpa only [hexp, dyadicMean] using (hs k).measure_ge_le ht
  · intro k t ht
    have h := (hs k).neg.measure_ge_le ht
    simpa only [Pi.neg_apply, neg_sub, hexp, dyadicMean] using h

end ThresholdHC.Uniform713
