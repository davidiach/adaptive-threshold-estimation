import ThresholdHC.CriticalAllSizes.Scale

noncomputable section
open MeasureTheory ProbabilityTheory Real Set
open scoped ENNReal
namespace ThresholdHC.CriticalAllSizes
open CriticalEntropy

theorem critical_product_scale_all {R : Type} [MeasurableSpace R]
    (ν : Measure R) [IsProbabilityMeasure ν] (A : StoppedProcedure R ℝ)
    (ρ : unitInterval) (hρ : 0 < (ρ : ℝ)) (hρ' : (ρ : ℝ) ≤ 1/4)
    (M : ℝ) (hM : 0 ≤ M)
    (hguar : CappedPopulationGuarantee criticalGapLaw ν
      (fun d => criticalParameter d false) (fun d => criticalParameter d true) A (ρ : ℝ) M) :
    let P := M*(populationExpectedWork criticalGapLaw ν
      (fun d => criticalParameter d false) (fun d => criticalParameter d true) (fun _ => 0) A).toReal
    (ρ : ℝ)/6 ≤ P ∧
    ∀ (K : ℕ),
      (∀ i : Fin K, 560*P ≤ criticalGapLaw.real (criticalAnnulus (i.val+3))) →
      (ρ : ℝ)*((K : ℝ)*Real.log (K : ℝ)) ≤ (21004288/3)*P := by
  dsimp only
  let p₀ := fun d => criticalParameter d false
  let p₁ := fun d => criticalParameter d true
  obtain ⟨hp,hnew,hm,_hwork,_hidentity,hsmall,hprod,hfloor⟩ :=
    activation_product_bounds criticalGapLaw ν p₀ p₁ (measurable_criticalParameter false)
      (measurable_criticalParameter true) A ρ hρ hρ' M hM hguar
  let : IsProbabilityMeasure (cond ν (activeSeeds A)) := cond_isProbabilityMeasure hp
  refine ⟨hfloor,?_⟩
  intro K hmass
  have he := critical_scale_product_all (cond ν (activeSeeds A)) (activeProcedure ν A) ρ hρ hρ'
    _ hm hnew K (fun i => by linarith [hmass i])
  nlinarith

end ThresholdHC.CriticalAllSizes
