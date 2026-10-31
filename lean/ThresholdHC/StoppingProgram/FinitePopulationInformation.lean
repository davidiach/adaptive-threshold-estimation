import ThresholdHC.StoppingProgram.OrderedInformationBound
import ThresholdHC.CriticalEntropy.PopulationTransfer

/-! Midpoint information transfers to arbitrary finite adaptive populations.
The physical work is charged once, including interleaved revisits. -/

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace ThresholdHC.StoppingProgram
open ThresholdHC.CriticalEntropy ThresholdHC.ObservableSimulation
open ThresholdHC.Tier6 (Gap SignLaw)

theorem finite_population_information {m N : ℕ}
    (μ : Measure Gap) [IsProbabilityMeasure μ] (q r : SignLaw)
    (pol : List Bool → Option (Fin m)) :
    1-realFiniteAffinity
      (finitePopulationWeight (n := N) μ pol (fun d : Gap => (d : ℝ)) (fun _ => q.val))
      (finitePopulationWeight μ pol (fun d : Gap => (d : ℝ)) (fun _ => r.val)) ≤
      (informationRatio μ N (midpointFourPriors q r)).toReal/4 *
        (finitePopulationExpectedWork μ (gapParameter false) (gapParameter true)
          (signUnit (midpointPrior q r)) pol N).toReal := by
  classical
  let s := midpointPrior q r
  let ν := Measure.pi (fun _ : Fin m => originalPopulationTapeLaw μ s)
  let K := (informationRatio μ N (midpointFourPriors q r)).toReal/4
  let W (i : Fin m) := populationExpectedWork μ ν (gapParameter false) (gapParameter true)
    (signUnit s) (localSimulationProcedure i N pol)
  have hlocal (i : Fin m) :
      1-realFiniteAffinity
        (finitePopulationWeight (n := N) μ pol (fun d : Gap => (d : ℝ))
          (fun j d => if j=i then q.val d else s.val d))
        (finitePopulationWeight μ pol (fun d : Gap => (d : ℝ))
          (fun j d => if j=i then r.val d else s.val d)) ≤ K*(W i).toReal := by
    have hA := localSimulation_affinity_le μ (gapParameter false) (gapParameter true)
      (signUnit q) (signUnit r) (signUnit s)
      (measurable_gapParameter false) (measurable_gapParameter true)
      (measurable_signUnit q) (measurable_signUnit r) (measurable_signUnit s)
      (fun d : Gap => (d : ℝ)) measurable_subtype_coe
      (fun d => ⟨d.property.1.le,d.property.2⟩)
      (ae_of_all _ (fun d => by simp [gapParameter,sub_eq_add_neg]))
      (ae_of_all _ (fun d => by simp [gapParameter])) pol i (n := N)
    have hh := ordered_stopped_hellinger_work μ ν q r (localSimulationProcedure i N pol) N
      (localSimulationProcedure_capped i N pol)
    exact (sub_le_sub_left hA 1).trans hh
  have hhyb := finite_population_hybrid_decomposition μ pol (fun d : Gap => (d : ℝ))
    q.val r.val measurable_subtype_coe q.property.1 r.property.1
    (fun d => ⟨d.property.1.le,d.property.2⟩) q.property.2 r.property.2 (n := N)
  have he (u : Gap → ℝ) (i : Fin m) :
      (fun j => if j=i then u else fun d => (q.val d+r.val d)/2) =
        (fun j d => if j=i then u d else s.val d) := by
    funext j d
    by_cases hj : j=i
    · simp [hj]
    · simp only [hj,ite_false]
      dsimp only [s,midpointPrior,mixPrior]
      ring
  simp_rw [he] at hhyb
  calc
    _ ≤ ∑ i : Fin m, (1-realFiniteAffinity
        (finitePopulationWeight (n := N) μ pol (fun d : Gap => (d : ℝ))
          (fun j d => if j=i then q.val d else s.val d))
        (finitePopulationWeight μ pol (fun d : Gap => (d : ℝ))
          (fun j d => if j=i then r.val d else s.val d))) := hhyb
    _ ≤ ∑ i : Fin m, K*(W i).toReal := Finset.sum_le_sum (fun i hi => hlocal i)
    _ = _ := by
      rw [← Finset.mul_sum]
      congr 1
      exact population_localSimulation_total_work_real μ (gapParameter false) (gapParameter true)
        (signUnit s) (measurable_gapParameter false) (measurable_gapParameter true)
        (measurable_signUnit s) pol

end ThresholdHC.StoppingProgram
