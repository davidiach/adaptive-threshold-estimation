import ThresholdHC.CriticalEntropy.CriticalPopulationFinite
import ThresholdHC.CriticalEntropy.CreationPopulation
import ThresholdHC.CriticalEntropy.PopulationWorkLaw

noncomputable section

namespace ThresholdHC.CriticalEntropy
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

theorem criticalClipped_parameters :
    (∀ᵐ d ∂criticalGapLaw, (criticalParameter d false : ℝ) = 1/2-criticalClippedGap d) ∧
    (∀ᵐ d ∂criticalGapLaw, (criticalParameter d true : ℝ) = 1/2+criticalClippedGap d) := by
  have hsupport : ∀ᵐ d ∂criticalGapLaw, d ∈ Ioc (0 : ℝ) (1/4) :=
    ae_iff.mpr criticalGapLaw_supported
  constructor
  all_goals
    filter_upwards [hsupport,criticalClippedGap_ae] with d hd hc
    rw [criticalParameter_coe_of_mem d hd,hc]
    simp [sub_eq_add_neg]

/-- A single pair applies to every countably labelled deterministic policy at
every finite horizon. The decision-tree cap is derived separately for each
policy and horizon; no uniform cap is imposed. -/
theorem critical_common_creation_prefix_pair : ∃ C : ℝ, 0 < C ∧
    ∀ (ρ : unitInterval), 0 < (ρ : ℝ) → (ρ : ℝ) ≤ 1/4 →
    ∀ δ : ℝ, 0 ≤ δ → δ ≤ (ρ : ℝ)/96 →
    ∃ q r : ℝ → unitInterval, CappedPrior criticalGapLaw (ρ : ℝ) q ∧
      CappedPrior criticalGapLaw (ρ : ℝ) r ∧
      δ ≤ (∫ d, (r d : ℝ) ∂criticalGapLaw)-(∫ d, (q d : ℝ) ∂criticalGapLaw) ∧
      ∀ (n : ℕ) (pol : List Bool → Option ℕ),
        (1-realFiniteAffinity
          (creationPopulationWeight (n := n) criticalGapLaw pol criticalClippedGap (fun d => (q d : ℝ)))
          (creationPopulationWeight criticalGapLaw pol criticalClippedGap (fun d => (r d : ℝ))))*
          (ρ : ℝ)*criticalLogFactor (ρ : ℝ) ≤
        C*δ^2*(∑ w : Fin n → Option Bool, creationPopulationWeight criticalGapLaw pol
          criticalClippedGap (fun d => (midpointPrior q r d : ℝ)) w*ThresholdHC.workOf w) := by
  obtain ⟨C,hC,hcommon⟩ := critical_common_finite_population_pair
  refine ⟨C,hC,?_⟩
  intro ρ hρ hρ' δ hδ hδρ
  obtain ⟨q,r,hq,hr,hsep,hpair⟩ := hcommon ρ hρ hρ' δ hδ hδρ
  refine ⟨q,r,hq,hr,hsep,?_⟩
  intro n pol
  let m := Tier5.coinCap n pol
  let cpol := Tier5.capPolicy m pol
  have h := hpair m n cpol
  have he (u : ℝ → unitInterval) (hu : Measurable u) :
      creationPopulationWeight (n := n) criticalGapLaw pol criticalClippedGap (fun d => (u d : ℝ)) =
      finitePopulationWeight criticalGapLaw cpol id (fun _ d => (u d : ℝ)) := by
    funext w
    rw [creationPopulationWeight_eq_finite criticalGapLaw pol criticalClippedGap
      (fun d => (u d : ℝ)) measurable_criticalClippedGap (measurable_subtype_coe.comp hu)]
    exact congrFun (finitePopulationWeight_gap_congr criticalGapLaw cpol criticalClippedGap id
      criticalClippedGap_ae (fun _ d => (u d : ℝ))) w
  rw [← he q hq.1,← he r hr.1] at h
  rw [finitePopulation_work_real criticalGapLaw _ _ _ (measurable_criticalParameter false)
    (measurable_criticalParameter true) (measurable_midpointPrior q r hq.1 hr.1)
    criticalClippedGap measurable_criticalClippedGap criticalClippedGap_bounds
    criticalClipped_parameters.1 criticalClipped_parameters.2 cpol] at h
  simpa only [creationPopulationWeight_eq_finite criticalGapLaw pol criticalClippedGap
    (fun d => (midpointPrior q r d : ℝ)) measurable_criticalClippedGap
    (measurable_subtype_coe.comp (measurable_midpointPrior q r hq.1 hr.1))] using h

end ThresholdHC.CriticalEntropy
