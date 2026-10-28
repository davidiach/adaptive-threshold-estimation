import ThresholdHC.CriticalEntropy.PolicyNormalization
import ThresholdHC.CriticalEntropy.PolicyMixture
import ThresholdHC.CriticalEntropy.CommonPoint

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace ThresholdHC.CriticalEntropy

/-- One separated pair of actual priors controls every capped observable policy,
including arbitrary independent random seeds. The pair precedes the policy
quantifiers. The charge is actual work under the all-negative population. -/
theorem critical_common_capped_pair : ∃ C : ℝ, 0 < C ∧
    ∀ (ρ : unitInterval), 0 < (ρ : ℝ) → (ρ : ℝ) ≤ 1/4 →
    ∀ δ : ℝ, 0 ≤ δ → δ ≤ (ρ : ℝ)/96 →
    ∃ q r : ℝ → unitInterval, CappedPrior criticalGapLaw (ρ : ℝ) q ∧
      CappedPrior criticalGapLaw (ρ : ℝ) r ∧
      δ ≤ (∫ d, (r d : ℝ) ∂criticalGapLaw)-(∫ d, (q d : ℝ) ∂criticalGapLaw) ∧
      ∀ (R E : Type) [MeasurableSpace R] [MeasurableSpace E]
        (ν : Measure R) [IsProbabilityMeasure ν] (A : StoppedProcedure R E)
        (m : ℕ), (∀ z, A.stop z ≤ m) →
        (1-(hellingerAffinity
          (cappedTranscriptLaw criticalGapLaw ν
            (fun d => criticalParameter d false) (fun d => criticalParameter d true) q A m)
          (cappedTranscriptLaw criticalGapLaw ν
            (fun d => criticalParameter d false) (fun d => criticalParameter d true) r A m)).toReal)*
          (ρ : ℝ)*criticalLogFactor (ρ : ℝ) ≤
        C*δ^2*(populationExpectedWork criticalGapLaw ν
          (fun d => criticalParameter d false) (fun d => criticalParameter d true) (fun _ => 0) A).toReal := by
  classical
  obtain ⟨C,hC,hpolicy⟩ := critical_capped_constraint_feasible
  refine ⟨C,hC,?_⟩
  intro ρ hρ hρ' δ hδ hδρ
  obtain ⟨hKc,hKv,hKn,hreal,hgeom⟩ := critical_pair_hellinger_geometry (ρ : ℝ) δ hδ
    (by linarith) (by linarith)
  choose H hHc hHv hHe using
    fun B : CappedPolicy => hgeom B.Seed Unit B.seedLaw B.procedure B.cap B.capped
  let K := populationPairSet criticalGapLaw (ρ : ℝ) δ
  let k := (ρ : ℝ)*criticalLogFactor (ρ : ℝ)
  let b := C*δ^2
  let f (B : CappedPolicy) (z : PopulationDual criticalGapLaw × PopulationDual criticalGapLaw) :=
    k*H B z-b*policyNullWork B
  have hk : 0 ≤ k := mul_nonneg hρ.le (criticalLogFactor_pos (ρ : ℝ) hρ (by linarith)).le
  have hfc (B : CappedPolicy) : Continuous (f B) :=
    (continuous_const.mul (hHc B)).sub continuous_const
  have hfv (B : CappedPolicy) : ConvexOn ℝ K (f B) := by
    refine ⟨hKv,?_⟩
    intro x hx y hy a c ha hc hac
    have hh := (hHv B).2 hx hy ha hc hac
    simp only [smul_eq_mul] at hh
    have hb := mul_le_mul_of_nonneg_left hh hk
    simp only [f,smul_eq_mul]
    calc
      _ ≤ k*(a*H B x+c*H B y)-b*policyNullWork B := sub_le_sub_right hb _
      _ = _ := by
        have he := congrArg (fun t : ℝ => t*(b*policyNullWork B)) hac
        nlinarith only [he]
  have hmix (s : Finset CappedPolicy) (p : s → ℝ)
      (hp : ∀ i, 0 ≤ p i) (hs : (∑ i, p i) = 1) :
      ∃ z ∈ K, (∑ i : s, p i*f i z) ≤ 0 := by
    -- Enumerating the finite family keeps every constructed seed space in the
    -- same universe as the original policy model, even though its index is bundled.
    let e := Fintype.equivFin s
    let w (i : Fin (Fintype.card s)) := p (e.symm i)
    let B (i : Fin (Fintype.card s)) : CappedPolicy := (e.symm i).val
    have hw (i) : 0 ≤ w i := hp _
    have hw1 : (∑ i, w i) = 1 := by rw [e.symm.sum_comp]; exact hs
    let κ := finiteWeightMeasure w
    let : IsProbabilityMeasure κ := finiteWeightMeasure_probability w hw hw1
    obtain ⟨M,hMW,hMA⟩ := capped_policy_mixture κ B
    obtain ⟨z,hz,hbound⟩ := hpolicy M.Seed Unit M.seedLaw M.procedure M.cap M.capped
      ρ hρ hρ' δ hδ hδρ
    let q := populationDualPrior criticalGapLaw z.1
    let r := populationDualPrior criticalGapLaw z.2
    have hq : Measurable q := populationDualPrior_measurable _ _
    have hr : Measurable r := populationDualPrior_measurable _ _
    have hMwork : policyNullWork M = ∑ i, w i*policyNullWork (B i) := by
      simpa only [κ,finiteWeightMeasure_real_singleton w hw] using hMW
    have hMaff : policyAffinity M q r = ∑ i, w i*policyAffinity (B i) q r := by
      simpa only [κ,finiteWeightMeasure_real_singleton w hw] using hMA q r hq hr
    refine ⟨z,hz,?_⟩
    calc
      (∑ i : s, p i*f i z) =
          ∑ i, w i*(k*(1-policyAffinity (B i) q r)-b*policyNullWork (B i)) := by
        rw [← e.symm.sum_comp (fun i : s => p i*f i z)]
        apply Finset.sum_congr rfl
        intro i hi
        dsimp only [f,w,B]
        rw [(hHe (e.symm i).val z hz).1]
        rfl
      _ = k*(1-policyAffinity M q r)-b*policyNullWork M := by
        rw [hMwork,hMaff]
        simp only [mul_sub,Finset.sum_sub_distrib,Finset.mul_sum,mul_one]
        have hsum : (∑ i, w i*k) = k := by rw [← Finset.sum_mul,hw1,one_mul]
        rw [hsum]
        simp only [mul_left_comm]
      _ ≤ 0 := by
        apply sub_nonpos.mpr
        convert hbound using 1 <;> dsimp only [k,b,policyAffinity,policyNullWork,q,r] <;> ring
  obtain ⟨z,hz,hall⟩ := common_point_of_finite_mixtures K hKn hKc hKv f hfc hfv hmix
  obtain ⟨hq,hr,hgap⟩ := hreal z hz
  refine ⟨populationDualPrior criticalGapLaw z.1,populationDualPrior criticalGapLaw z.2,
    hq,hr,hgap,?_⟩
  intro R E _ _ ν _ A m hcap
  let B := cappedPolicyOfProcedure ν A m hcap
  have hb := sub_nonpos.mp (hall B)
  change k*H B z ≤ b*policyNullWork B at hb
  rw [(hHe B z hz).1] at hb
  change k*(1-policyAffinity B _ _) ≤ b*policyNullWork B at hb
  rw [cappedPolicyOfProcedure_affinity,cappedPolicyOfProcedure_nullWork] at hb
  convert hb using 1
  dsimp only [k,b]
  ring

end ThresholdHC.CriticalEntropy
