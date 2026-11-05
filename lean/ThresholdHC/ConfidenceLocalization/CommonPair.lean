import ThresholdHC.ConfidenceLocalization.PolicyPair
import ThresholdHC.ConfidenceLocalization.PolicyMixture

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace ThresholdHC.ConfidenceLocalization
open ThresholdHC.CriticalEntropy

/-- A single pair precedes every capped local policy and every auxiliary seed.
The quantitative premise is a variance/null-work obstruction for actual bounded
observable estimators on the full half-prior class. -/
theorem common_pair_of_obstruction {D : Type} [MeasurableSpace D]
    (μ : Measure D) [IsProbabilityMeasure μ] (p₀ p₁ : D → unitInterval)
    (h₀ : Measurable p₀) (h₁ : Measurable p₁)
    (c : unitInterval) (hc0 : 0 < (c : ℝ)) (hc : (c : ℝ) ≤ 1/4)
    {b J δ : ℝ} (hJ : 0 < J) (hδ : 0 < δ) (hδb : δ ≤ b/3)
    (hobs : NullVarianceObstruction μ p₀ p₁ (c : ℝ) b J) :
    ∃ q r : D → unitInterval, CappedPrior μ (c : ℝ) q ∧ CappedPrior μ (c : ℝ) r ∧
      δ ≤ (∫ d, (r d : ℝ) ∂μ)-(∫ d, (q d : ℝ) ∂μ) ∧
      ∀ {R E : Type} [MeasurableSpace R] [MeasurableSpace E]
        (ν : Measure R) [IsProbabilityMeasure ν] (A : StoppedProcedure R E)
        (m : ℕ), (∀ z, A.stop z ≤ m) →
        1-(hellingerAffinity (cappedTranscriptLaw μ ν p₀ p₁ q A m)
          (cappedTranscriptLaw μ ν p₀ p₁ r A m)).toReal ≤
          (42*δ^2/J)*(populationExpectedWork μ ν p₀ p₁ (fun _ => 0) A).toReal := by
  classical
  have hb := obstruction_bias_lt_half μ p₀ p₁ hJ hobs
  let K := populationPairSet μ (c : ℝ) (2*δ)
  obtain ⟨hKc,hKv⟩ := populationPairSet_compact_convex μ (c : ℝ) (2*δ)
  have hKn : K.Nonempty := populationPairSet_nonempty μ (c : ℝ) (2*δ)
    (by positivity) (by linarith) (by linarith)
  choose H hHc hHv hHe using fun B : CappedPolicy =>
    regularized_pair_geometry μ B.seedLaw p₀ p₁ h₀ h₁ B.procedure B.cap B.capped c
  let a := 42*δ^2
  let F (B : CappedPolicy) (z : PopulationDual μ × PopulationDual μ) :=
    J*H B z-a*localNullWork μ p₀ p₁ B
  have hFc (B : CappedPolicy) : Continuous (F B) :=
    (continuous_const.mul (hHc B)).sub continuous_const
  have hFv (B : CappedPolicy) : ConvexOn ℝ K (F B) := by
    refine ⟨hKv,?_⟩
    intro x hx y hy u v hu hv huv
    have hh := (hHv B).2 hx.1 hy.1 hu hv huv
    simp only [smul_eq_mul] at hh
    have hj := mul_le_mul_of_nonneg_left hh hJ.le
    simp only [F,smul_eq_mul]
    calc
      _ ≤ J*(u*H B x+v*H B y)-a*localNullWork μ p₀ p₁ B := sub_le_sub_right hj _
      _ = _ := by
        have he := congrArg (fun t : ℝ => t*(a*localNullWork μ p₀ p₁ B)) huv
        nlinarith only [he]
  have hmix (s : Finset CappedPolicy) (p : s → ℝ)
      (hp : ∀ i, 0 ≤ p i) (hs : (∑ i, p i) = 1) :
      ∃ z ∈ K, (∑ i : s, p i*F i z) ≤ 0 := by
    let e := Fintype.equivFin s
    let w (i : Fin (Fintype.card s)) := p (e.symm i)
    let B (i : Fin (Fintype.card s)) : CappedPolicy := (e.symm i).val
    have hw (i) : 0 ≤ w i := hp _
    have hw1 : (∑ i, w i) = 1 := by rw [e.symm.sum_comp]; exact hs
    let κ := finiteWeightMeasure w
    let : IsProbabilityMeasure κ := finiteWeightMeasure_probability w hw hw1
    obtain ⟨M,hMW,hMA⟩ := local_policy_mixture μ p₀ p₁ h₀ h₁ κ B
    obtain ⟨z,hz,hbound⟩ := regularized_policy_constraint μ M.seedLaw p₀ p₁ h₀ h₁
      M.procedure M.cap M.capped c hc0 hc hJ hδ hδb hobs
    let q := midpointPrior (populationDualPrior μ z.1) (fun _ => c)
    let r := midpointPrior (populationDualPrior μ z.2) (fun _ => c)
    have hq : Measurable q := measurable_midpointPrior _ _ (populationDualPrior_measurable μ z.1) measurable_const
    have hr : Measurable r := measurable_midpointPrior _ _ (populationDualPrior_measurable μ z.2) measurable_const
    have hMwork : localNullWork μ p₀ p₁ M = ∑ i, w i*localNullWork μ p₀ p₁ (B i) := by
      simpa only [κ,finiteWeightMeasure_real_singleton w hw] using hMW
    have hMaff : localAffinity μ p₀ p₁ M q r = ∑ i, w i*localAffinity μ p₀ p₁ (B i) q r := by
      simpa only [κ,finiteWeightMeasure_real_singleton w hw] using hMA q r hq hr
    refine ⟨z,hz,?_⟩
    calc
      (∑ i : s, p i*F i z) =
          ∑ i, w i*(J*(1-localAffinity μ p₀ p₁ (B i) q r)-a*localNullWork μ p₀ p₁ (B i)) := by
        rw [← e.symm.sum_comp (fun i : s => p i*F i z)]
        apply Finset.sum_congr rfl
        intro i _
        dsimp only [F,w,B]
        rw [(hHe (e.symm i).val z.1 hz.1.1 z.2 hz.1.2).1]
        rfl
      _ = J*(1-localAffinity μ p₀ p₁ M q r)-a*localNullWork μ p₀ p₁ M := by
        rw [hMwork,hMaff]
        simp only [mul_sub,Finset.sum_sub_distrib,Finset.mul_sum,mul_one]
        have hsum : (∑ i, w i*J) = J := by rw [← Finset.sum_mul,hw1,one_mul]
        rw [hsum]
        simp only [mul_left_comm]
      _ ≤ 0 := by
        apply sub_nonpos.mpr
        convert hbound using 1 <;> dsimp only [a,localAffinity,localNullWork,q,r]
        all_goals ring
  obtain ⟨z,hz,hall⟩ := common_point_of_finite_mixtures K hKn hKc hKv F hFc hFv hmix
  obtain ⟨hq,hr,hgap⟩ := populationPairSet_realization μ (c : ℝ) (2*δ) z hz
  let q := midpointPrior (populationDualPrior μ z.1) (fun _ => c)
  let r := midpointPrior (populationDualPrior μ z.2) (fun _ => c)
  have hcPrior := cappedPrior_const μ (c : ℝ) c (by linarith) le_rfl
  refine ⟨q,r,cappedPrior_midpoint μ (c : ℝ) _ _ hq hcPrior,
    cappedPrior_midpoint μ (c : ℝ) _ _ hr hcPrior,?_,?_⟩
  · dsimp only [q,r]
    rw [midpointPrior_integral μ _ _ (populationDualPrior_measurable μ z.1) measurable_const,
      midpointPrior_integral μ _ _ (populationDualPrior_measurable μ z.2) measurable_const]
    linarith
  · intro R E _ _ ν _ A m hcap
    let B := cappedPolicyOfProcedure ν A m hcap
    have hh := sub_nonpos.mp (hall B)
    change J*H B z ≤ a*localNullWork μ p₀ p₁ B at hh
    rw [(hHe B z.1 hz.1.1 z.2 hz.1.2).1] at hh
    change J*(1-localAffinity μ p₀ p₁ B q r) ≤ a*localNullWork μ p₀ p₁ B at hh
    rw [localPolicyOfProcedure_affinity,localPolicyOfProcedure_nullWork] at hh
    calc
      _ ≤ (42*δ^2*(populationExpectedWork μ ν p₀ p₁ (fun _ => 0) A).toReal)/J := by
        apply (le_div_iff₀ hJ).mpr
        dsimp only [a] at hh
        nlinarith only [hh]
      _ = _ := by ring

end ThresholdHC.ConfidenceLocalization
