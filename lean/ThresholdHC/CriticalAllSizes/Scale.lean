import ThresholdHC.CriticalAllSizes.Estimation
import ThresholdHC.CriticalEntropy.ActivationCost

noncomputable section
open MeasureTheory ProbabilityTheory Real Set
open scoped ENNReal
namespace ThresholdHC.CriticalAllSizes
open CriticalEntropy

theorem critical_scale_entropy_all {R : Type} [MeasurableSpace R]
    (ν : Measure R) [IsProbabilityMeasure ν] (A : StoppedProcedure R ℝ)
    (ρ : unitInterval) (hρ : 0 < (ρ : ℝ)) (hρ' : (ρ : ℝ) ≤ 1/4)
    (m : ℝ) (hm : 2*(ρ : ℝ)/3 ≤ m)
    (hguar : CappedPopulationGuarantee criticalGapLaw ν
      (fun d => criticalParameter d false) (fun d => criticalParameter d true) A (ρ : ℝ) m)
    (K : ℕ)
    (hmass : ∀ i : Fin K, 140*m ≤ criticalGapLaw.real (criticalAnnulus (i.val+3))) :
    (K : ℝ)*Real.log (K : ℝ)/(4096*(⌈512*(1+m/(ρ : ℝ))⌉₊ : ℝ)) ≤
      (1/3)*(populationExpectedWork criticalGapLaw ν
        (fun d => criticalParameter d false) (fun d => criticalParameter d true)
        (fun _ => 0) A).toReal := by
  let p₀ := fun d => criticalParameter d false
  let p₁ := fun d => criticalParameter d true
  have hmpos : 0 < m := by linarith
  have hp₀ : Measurable p₀ := measurable_criticalParameter false
  have hp₁ : Measurable p₁ := measurable_criticalParameter true
  obtain ⟨G,hG,hGsub,hGbad,hGgood⟩ := population_good_gaps criticalGapLaw ν p₀ p₁ hp₀ hp₁
    0 (1/4) (by norm_num) criticalGapLaw_supported ρ hρ hρ' m hm A hguar
  have hc₀ := cappedPrior_const criticalGapLaw (ρ : ℝ) 0 (by norm_num) (by simpa using hρ.le)
  obtain ⟨hw,hwint⟩ := population_negative_work_integral criticalGapLaw ν p₀ p₁ hp₀ hp₁ A
    (hguar.work _ hc₀)
  let w : ℝ → ℝ := fun d => (expectedStoppedProcedureWork ν (p₀ d) A).toReal
  obtain ⟨d,hd,hsep,hcost⟩ := critical_annulus_good_points G hG m hGbad K hmass w hw
    (fun _ => ENNReal.toReal_nonneg)
  have hg (i : Fin K) := hGgood (d i) (hd i).1
  have hr : (2 : ℝ)/3 ≤ m/(ρ : ℝ) := by
    apply (le_div_iff₀ hρ).mpr
    linarith
  let n := ⌈512*(1+m/(ρ : ℝ))⌉₊
  have hn := critical_restart_count_bounds (m/(ρ : ℝ)) hr
  have hscale : 160*(1/64+2*m/(ρ : ℝ)) ≤ (n : ℝ) := by
    convert hn.2.1 using 1
    ring
  have hfinite : ∀ i b, expectedStoppedProcedureWork ν (signParameter (d i) b) A ≠ ∞ := by
    intro i b
    obtain ⟨_,_,hw₀,hw₁,_,_,_,_⟩ := hg i
    rw [← criticalParameter_eq_sign]
    cases b
    · exact hw₀
    · exact hw₁
  have hmem : ∀ i b, MemLp id 2 ((ν.prod (Tier2.tapeMeasure (signParameter (d i) b))).map A.output) := by
    intro i b
    obtain ⟨hM₀,hM₁,_,_,_,_,_,_⟩ := hg i
    rw [← criticalParameter_eq_sign]
    apply (conditionalSecondMoment_finite_iff ν _ A).mp
    cases b
    · exact hM₀
    · exact hM₁
  have hmoment : ∀ i b, (∫ x : ℝ, x^2
      ∂(ν.prod (Tier2.tapeMeasure (signParameter (d i) b))).map A.output) ≤ 1/64+2*m/(ρ : ℝ) := by
    intro i b
    obtain ⟨hM₀,hM₁,_,_,_,_,hbound₀,hbound₁⟩ := hg i
    rw [← criticalParameter_eq_sign]
    cases b
    · rw [conditionalSecondMoment_output_law ν _ A hM₀]
      have hratio : 0 ≤ 2*m/(ρ : ℝ) := by positivity
      linarith
    · rw [conditionalSecondMoment_output_law ν _ A hM₁]
      exact hbound₁
  have hminus : ∀ i, (∫ x : ℝ, x
      ∂(ν.prod (Tier2.tapeMeasure (signParameter (d i) false))).map A.output) ≤ 1/8 := by
    intro i
    rw [conditionalMean_output_law,← criticalParameter_eq_sign]
    exact (abs_le.mp (hg i).2.2.2.2.1).2
  have hplus : ∀ i, 5/8 ≤ (∫ x : ℝ, x
      ∂(ν.prod (Tier2.tapeMeasure (signParameter (d i) true))).map A.output) := by
    intro i
    rw [conditionalMean_output_law,← criticalParameter_eq_sign]
    exact (hg i).2.2.2.2.2.1
  have hentropy := finite_gap_estimation_entropy_all ν A K d hsep n hn.1
    (1/64+2*m/(ρ : ℝ)) hscale hfinite hmem hmoment hminus hplus
  change (∑ i, (d i : ℝ)^2*(expectedStoppedProcedureWork ν (criticalParameter (d i) false) A).toReal)
    ≤ (1/3)*(∫ x, w x ∂criticalGapLaw) at hcost
  simp_rw [criticalParameter_eq_sign] at hcost
  rw [hwint] at hcost
  exact hentropy.trans hcost

/-- The procedure and seed law are fixed across all population priors. The
conditional moments, good gaps and sign tests are derived inside the proof.
Only the explicit annulus-mass hypothesis remains; there is no lower bound
on the scale count. -/
theorem critical_scale_product_all {R : Type} [MeasurableSpace R]
    (ν : Measure R) [IsProbabilityMeasure ν] (A : StoppedProcedure R ℝ)
    (ρ : unitInterval) (hρ : 0 < (ρ : ℝ)) (hρ' : (ρ : ℝ) ≤ 1/4)
    (m : ℝ) (hm : 2*(ρ : ℝ)/3 ≤ m)
    (hguar : CappedPopulationGuarantee criticalGapLaw ν
      (fun d => criticalParameter d false) (fun d => criticalParameter d true) A (ρ : ℝ) m)
    (K : ℕ)
    (hmass : ∀ i : Fin K, 140*m ≤ criticalGapLaw.real (criticalAnnulus (i.val+3))) :
    (ρ : ℝ)*((K : ℝ)*Real.log (K : ℝ)) ≤
      (5251072/3)*m*(populationExpectedWork criticalGapLaw ν
        (fun d => criticalParameter d false) (fun d => criticalParameter d true)
        (fun _ => 0) A).toReal := by
  let n := ⌈512*(1+m/(ρ : ℝ))⌉₊
  let W := (populationExpectedWork criticalGapLaw ν
    (fun d => criticalParameter d false) (fun d => criticalParameter d true) (fun _ => 0) A).toReal
  have hr : (2 : ℝ)/3 ≤ m/(ρ : ℝ) := (le_div_iff₀ hρ).mpr (by linarith)
  have hn := critical_restart_count_bounds (m/(ρ : ℝ)) hr
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn.1
  have hW : 0 ≤ W := ENNReal.toReal_nonneg
  have he := critical_scale_entropy_all ν A ρ hρ hρ' m hm hguar K hmass
  change (K : ℝ)*Real.log (K : ℝ)/(4096*(n : ℝ)) ≤ (1/3)*W at he
  have hlin := (div_le_iff₀ (show 0 < 4096*(n : ℝ) by positivity)).mp he
  have hnr : (n : ℝ)*(ρ : ℝ) ≤ 1282*m := by
    apply (le_div_iff₀ hρ).mp
    convert hn.2.2 using 1
    ring
  calc
    _ ≤ (ρ : ℝ)*((1/3)*W*(4096*(n : ℝ))) := mul_le_mul_of_nonneg_left hlin hρ.le
    _ = (4096/3)*W*((n : ℝ)*(ρ : ℝ)) := by ring
    _ ≤ (4096/3)*W*(1282*m) := mul_le_mul_of_nonneg_left hnr (by positivity)
    _ = _ := by ring

end ThresholdHC.CriticalAllSizes
