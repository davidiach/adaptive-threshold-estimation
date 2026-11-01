import ThresholdHC.EntropyTailLower.GeneralGoodGaps
import ThresholdHC.EntropyTailLower.AnnularEstimation
import ThresholdHC.CriticalEntropy.CriticalScale

/-! From actual global single-coin population guarantees to weighted annular
hardness, for every probability law on the small-gap domain, including atoms.
The mass condition remains explicit; the scale-dependent gate must supply it. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace ThresholdHC.EntropyTailLower
open ThresholdHC.CriticalEntropy

theorem capped_guarantee_moment_floor_general {D R : Type}
    [MeasurableSpace D] [MeasurableSpace R]
    (μ : Measure D) [IsProbabilityMeasure μ] (ν : Measure R) [IsProbabilityMeasure ν]
    (p₀ p₁ : D → unitInterval) (h₀ : Measurable p₀) (h₁ : Measurable p₁)
    (A : StoppedProcedure R ℝ) (ρ : unitInterval) (hρ : 0 < (ρ:ℝ))
    (hρ' : (ρ:ℝ) ≤ 1/4) (M : ℝ) (hM : 0 ≤ M)
    (hguar : CappedPopulationGuarantee μ ν p₀ p₁ A (ρ:ℝ) M) : 2*(ρ:ℝ)/3 ≤ M := by
  let : IsProbabilityMeasure (populationMeasure μ ν) := by unfold populationMeasure; infer_instance
  have hc₀ := cappedPrior_const μ (ρ:ℝ) 0 (by norm_num) (by simpa using hρ.le)
  have hcρ := cappedPrior_const μ (ρ:ℝ) ρ (by linarith) le_rfl
  have hf (q : D → unitInterval) (hq : CappedPrior μ (ρ:ℝ) q) :
      populationSecondMoment μ ν p₀ p₁ q A ≠ ∞ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hguar.moment q hq)
  have hvar := population_variance_floor μ ν p₀ p₁ h₀ h₁ ρ hρ hρ' A
    (hf _ hc₀) (hf _ hcρ) (by simpa using hguar.bias _ hc₀) (by simpa using hguar.bias _ hcρ)
  have hl2 := population_memLp_of_moment μ ν p₀ p₁ (fun _ => ρ) h₀ h₁ measurable_const A (hf _ hcρ)
  have hv := variance_le_expectation_sq hl2.aestronglyMeasurable
  simp only [Pi.pow_apply] at hv
  rw [population_second_moment_toReal μ ν p₀ p₁ (fun _ => ρ) h₀ h₁ measurable_const A (hf _ hcρ)] at hv
  have hMb := ENNReal.toReal_mono ENNReal.ofReal_ne_top (hguar.moment _ hcρ)
  rw [ENNReal.toReal_ofReal hM] at hMb
  exact hvar.trans (hv.trans hMb)

theorem measurable_entropy_signParameter (s : Bool) :
    Measurable (fun d : EntropyGap => signParameter d s) := by
  apply Measurable.subtype_mk
  cases s <;> dsimp [signParameter] <;> fun_prop

/-- Conditional mean, moment, finiteness, and good-gap bounds are derived
from the actual uniform population guarantee. No atomlessness is assumed. -/
theorem population_annular_entropy {R : Type} [MeasurableSpace R]
    (μ : Measure EntropyGap) [IsProbabilityMeasure μ]
    (ν : Measure R) [IsProbabilityMeasure ν] (A : StoppedProcedure R ℝ)
    (ρ : unitInterval) (hρ : 0 < (ρ:ℝ)) (hρ' : (ρ:ℝ) ≤ 1/4)
    (m : ℝ) (hm0 : 0 ≤ m)
    (hguar : CappedPopulationGuarantee μ ν
      (fun d => signParameter d false) (fun d => signParameter d true) A (ρ:ℝ) m)
    {K : ℕ} (I : Fin K → Set EntropyGap) (b : Fin K → ℝ)
    (hb : ∀ i, 0 < b i) (hI : ∀ i, MeasurableSet (I i))
    (hdisjoint : Pairwise (fun i j => Disjoint (I i) (I j)))
    (hband : ∀ i d, d ∈ I i → b i/2 < (d:ℝ) ∧ (d:ℝ) ≤ b i)
    (hsep : ∀ i j, j.val = i.val+1 → 4*b j ≤ b i)
    (hmass : ∀ i, 140*m ≤ μ.real (I i)) :
    (ρ:ℝ)*ThresholdHC.EntropyTailQuantile.costEntropy (fun i => μ.real (I i)/(b i)^2) ≤
      33554432*m*(populationExpectedWork μ ν
        (fun d => signParameter d false) (fun d => signParameter d true) (fun _ => 0) A).toReal := by
  let p₀ := fun d : EntropyGap => signParameter d false
  let p₁ := fun d : EntropyGap => signParameter d true
  have hp₀ : Measurable p₀ := measurable_entropy_signParameter false
  have hp₁ : Measurable p₁ := measurable_entropy_signParameter true
  have hm := capped_guarantee_moment_floor_general μ ν p₀ p₁ hp₀ hp₁ A ρ hρ hρ' m hm0 hguar
  have hmpos : 0 < m := by linarith
  obtain ⟨G,hG,hGbad,hGgood⟩ := population_good_gaps_general μ ν p₀ p₁ hp₀ hp₁
    ρ hρ hρ' m hm A hguar
  have hc₀ := cappedPrior_const μ (ρ:ℝ) 0 (by norm_num) (by simpa using hρ.le)
  obtain ⟨hw,hwint⟩ := population_negative_work_integral μ ν p₀ p₁ hp₀ hp₁ A (hguar.work _ hc₀)
  let n := ⌈512*(1+m/(ρ:ℝ))⌉₊
  have hr : (2:ℝ)/3 ≤ m/(ρ:ℝ) := (le_div_iff₀ hρ).mpr (by linarith)
  have hn := critical_restart_count_bounds (m/(ρ:ℝ)) hr
  have hfinite : ∀ d ∈ G, ∀ s, expectedStoppedProcedureWork ν (signParameter d s) A ≠ ∞ := by
    intro d hd s
    obtain ⟨_,_,hw₀,hw₁,_,_,_,_⟩ := hGgood d hd
    cases s
    · exact hw₀
    · exact hw₁
  have hmem : ∀ d ∈ G, ∀ s, MemLp id 2
      ((ν.prod (Tier2.tapeMeasure (signParameter d s))).map A.output) := by
    intro d hd s
    obtain ⟨hM₀,hM₁,_,_,_,_,_,_⟩ := hGgood d hd
    apply (conditionalSecondMoment_finite_iff ν _ A).mp
    cases s
    · exact hM₀
    · exact hM₁
  have hmoment : ∀ d ∈ G, ∀ s, (∫ x : ℝ, x^2
      ∂(ν.prod (Tier2.tapeMeasure (signParameter d s))).map A.output) ≤ 1/64+2*m/(ρ:ℝ) := by
    intro d hd s
    obtain ⟨hM₀,hM₁,_,_,_,_,hbound₀,hbound₁⟩ := hGgood d hd
    cases s
    · rw [conditionalSecondMoment_output_law ν _ A hM₀]
      have hratio : 0 ≤ 2*m/(ρ:ℝ) := by positivity
      linarith
    · rw [conditionalSecondMoment_output_law ν _ A hM₁]
      exact hbound₁
  have hminus : ∀ d ∈ G, (∫ x : ℝ, x
      ∂(ν.prod (Tier2.tapeMeasure (signParameter d false))).map A.output) ≤ 3/8-1/4 := by
    intro d hd
    rw [conditionalMean_output_law]
    have h := (abs_le.mp (hGgood d hd).2.2.2.2.1).2
    convert h using 1; norm_num
  have hplus : ∀ d ∈ G, 3/8+1/4 ≤ (∫ x : ℝ, x
      ∂(ν.prod (Tier2.tapeMeasure (signParameter d true))).map A.output) := by
    intro d hd
    rw [conditionalMean_output_law]
    have h := (hGgood d hd).2.2.2.2.2.1
    convert h using 1; norm_num
  have hnM : 10*(1/64+2*m/(ρ:ℝ)) ≤ (n:ℝ)*(1/4)^2 := by
    have h : 160*(1/64+2*m/(ρ:ℝ)) ≤ (n:ℝ) := by
      convert hn.2.1 using 1; ring
    linarith only [h]
  have hs := annular_estimation_entropy ν A μ I b hb hI hdisjoint
    (fun i => by linarith [hmass i]) hband hsep G hG
    (fun i => by linarith [hmass i]) n hn.1 (1/64+2*m/(ρ:ℝ)) (3/8) (1/4)
    (by norm_num) hnM hw hfinite hmem hmoment hminus hplus
  rw [hwint] at hs
  have hnr : (n:ℝ)*(ρ:ℝ) ≤ 2048*m := by
    have hh : (n:ℝ)*(ρ:ℝ) ≤ 1282*m := by
      apply (le_div_iff₀ hρ).mp
      convert hn.2.2 using 1
      ring
    linarith
  calc
    _ ≤ (ρ:ℝ)*(16384*(n:ℝ)*(populationExpectedWork μ ν p₀ p₁ (fun _ => 0) A).toReal) :=
      mul_le_mul_of_nonneg_left hs hρ.le
    _ = 16384*(populationExpectedWork μ ν p₀ p₁ (fun _ => 0) A).toReal*((n:ℝ)*(ρ:ℝ)) := by ring
    _ ≤ 16384*(populationExpectedWork μ ν p₀ p₁ (fun _ => 0) A).toReal*(2048*m) :=
      mul_le_mul_of_nonneg_left hnr (by positivity)
    _ = _ := by ring

end ThresholdHC.EntropyTailLower
