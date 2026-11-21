import ThresholdHC.DepthObstruction.CappedPath
import ThresholdHC.DepthObstruction.OneCoin

/-! Arbitrary cross-coin feedback under a per-coin cap. The observable law of the
unchanged experiment is the law of the simulated population path driven by the
seed and independent complete coin tapes
(`ObservableSimulation.original_observable_simulation_law`). Under a per-coin cap
`N` the path uses only the first `N` flips of each coin, and with matching odd
moments through depth `N` those prefixes have the same law coin by coin. -/

noncomputable section
namespace ThresholdHC.DepthObstruction
open MeasureTheory
open scoped ENNReal
open ThresholdHC.Tier6 (Gap SignLaw AdaptiveEstimator experimentLaw)
open ThresholdHC.CriticalEntropy ThresholdHC.ObservableSimulation ThresholdHC.CapIdentification

/-- Independent coin tapes cut at the cap have the same joint law. -/
theorem capTapes_law_eq (μ : Measure Gap) [IsProbabilityMeasure μ]
    (qH qL : SignLaw) (N : ℕ) (h : OddMomentMatch μ qH qL N) :
    (Measure.infinitePi (fun _ : ℕ => originalPopulationTapeLaw μ qH)).map (capTapes N) =
      (Measure.infinitePi (fun _ : ℕ => originalPopulationTapeLaw μ qL)).map (capTapes N) := by
  have hg : Measurable (fun ω : ℕ → Bool => completePrefix N (Tier2.tapePrefix N ω)) :=
    (measurable_completePrefix N).comp (Tier2.measurable_prefix N)
  have hc : capTapes N =
      fun (s : ℕ → ℕ → Bool) (i : ℕ) => completePrefix N (Tier2.tapePrefix N (s i)) := rfl
  rw [hc, Measure.infinitePi_map_pi (fun _ : ℕ => originalPopulationTapeLaw μ qH) (fun _ => hg),
    Measure.infinitePi_map_pi (fun _ : ℕ => originalPopulationTapeLaw μ qL) (fun _ => hg)]
  congr 1
  funext i
  exact originalTape_completed_law_eq μ qH qL N h

/-- The observable law of a per-coin-capped procedure uses only capped tapes. -/
theorem observable_law_capTapes {R : Type} [MeasurableSpace R]
    (μ : Measure Gap) [IsProbabilityMeasure μ] (A : AdaptiveEstimator R) (q : SignLaw)
    (N : ℕ) (hcap : PerCoinCap A N) :
    (experimentLaw μ A q).map (fun z => (z.1.1, z.2)) =
      (A.randomLaw.prod ((Measure.infinitePi (fun _ : ℕ => originalPopulationTapeLaw μ q)).map
        (capTapes N))).map (fun z => (z.1, populationPath (A.policy z.1) z.2)) := by
  have hFm : Measurable (fun z : R × (ℕ → ℕ → Bool) =>
      (z.1, populationPath (A.policy z.1) z.2)) :=
    measurable_fst.prodMk (measurable_seeded_populationPath A.policy
      (fun xs => measurable_to_countable' (A.policy_measurable xs)))
  have hT : Measurable (Prod.map (id : R → R) (capTapes N)) :=
    measurable_id.prodMap (measurable_capTapes N)
  have hprod : A.randomLaw.prod
      ((Measure.infinitePi (fun _ : ℕ => originalPopulationTapeLaw μ q)).map (capTapes N)) =
      (A.randomLaw.prod (Measure.infinitePi (fun _ : ℕ => originalPopulationTapeLaw μ q))).map
        (Prod.map id (capTapes N)) := by
    rw [← Measure.map_prod_map _ _ measurable_id (measurable_capTapes N), Measure.map_id]
  rw [original_observable_simulation_law, hprod, Measure.map_map hFm hT]
  unfold originalSimulationLaw
  congr 1
  funext z
  simp only [Function.comp_apply, Prod.map_fst, Prod.map_snd, id_eq]
  rw [populationPath_capTapes (hcap z.1)]

/-- `thm:cap`, transcript part, for every per-coin cap `N` and every gap law. -/
theorem cappedTranscript : CappedTranscriptStatement := by
  intro R _ μ _ qH qL N A hm hcap
  rw [observable_law_capTapes μ A qH N hcap, observable_law_capTapes μ A qL N hcap,
    capTapes_law_eq μ qH qL N hm]

end ThresholdHC.DepthObstruction
