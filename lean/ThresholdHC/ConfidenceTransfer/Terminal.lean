import ThresholdHC.ConfidenceTransfer.Observable
import ThresholdHC.Tier5.StoppingEntropy

noncomputable section
open MeasureTheory InformationTheory Set Filter
open scoped ENNReal
namespace ThresholdHC.ConfidenceTransfer
open ThresholdHC.Tier3 ThresholdHC.Tier4 ThresholdHC.Tier6 ThresholdHC.RareAboveTwo
open ThresholdHC.ObservableSimulation

/-- Entropy of the stopped observable seed and tape is exhausted by the finite
prefix entropies. Finite work is required separately at both endpoints. -/
theorem stopped_observable_kl_eq_iSup {R : Type} [MeasurableSpace R]
    (μ : Measure Gap) [IsProbabilityMeasure μ] (A : AdaptiveEstimator R) (q r : SignLaw)
    (hq : expectedWork μ A q < ∞) (hr : expectedWork μ A r < ∞) :
    klDiv (observableDecisionLaw μ A q id) (observableDecisionLaw μ A r id) =
      ⨆ n, klDiv (observablePrefixLaw μ A q n) (observablePrefixLaw μ A r n) := by
  let f (n : ℕ) (z : R × ProcessTape) := (z.1,processPrefix n z.2)
  let flag := Tier5.stoppingFlagPolicy A.policy
  have hflag := Tier5.measurable_stoppingFlagPolicy A.policy A.policy_measurable
  have heq (n) : f n ⁻¹' stoppedPrefixSet flag n = stoppedFullSet flag n :=
    Set.ext (fun z => (stoppedFullSet_prefix flag n z).symm)
  have hseed : Measurable (fun z : PopulationSeed R × ProcessTape => z.1.1) := measurable_fst.fst
  have hobs : Measurable (fun z : PopulationSeed R × ProcessTape => (z.1.1,z.2)) := hseed.prodMk measurable_snd
  let (b : SignLaw) : IsProbabilityMeasure (observableDecisionLaw μ A b id) :=
    (Measure.isProbabilityMeasure_map_iff hobs.aemeasurable).2 inferInstance
  have cover (b : SignLaw) (hb : expectedWork μ A b < ∞) :
      ∀ᵐ z ∂observableDecisionLaw μ A b id, z ∈ ⋃ n, f n ⁻¹' stoppedPrefixSet flag n := by
    simp_rw [heq]
    have hstop := Tier5.creation_stops (PopulationSeed R) (PopulationSeed R × ProcessTape)
      (populationSeedLaw μ A) (experimentLaw μ A b) Prod.fst Prod.snd (populationPolicy A)
      populationGap (populationPrior b) measurable_fst observable_tape_measurable
      (measurable_populationPolicy A) (population_realization R μ A b).2 hb
    exact Tier5.realized_creation_stopped_cover (experimentLaw μ A b)
      (fun z => z.1.1) Prod.snd A.policy hseed observable_tape_measurable A.policy_measurable hstop
  have recn (b : SignLaw) (n : ℕ) : ∀ᵐ z ∂(observableDecisionLaw μ A b id).restrict
      (f n ⁻¹' stoppedPrefixSet flag n), padJoint n (f n z) = z := by
    rw [heq]
    apply (ae_restrict_iff' (measurableSet_stoppedFull flag hflag n)).mpr
    apply (ae_map_iff hobs.aemeasurable ((measurableSet_stoppedFull flag hflag n).imp
      (measurableSet_reconstructed n))).mpr
    have hv := ae_all_iff.2 (fun k => Tier5.realized_creation_valid_step
      (populationSeedLaw μ A) (experimentLaw μ A b) Prod.fst Prod.snd
      (populationPolicy A) populationGap (populationPrior b) measurable_fst observable_tape_measurable
      (measurable_populationPolicy A) (population_realization R μ A b).2 k)
    filter_upwards [hv] with z hz hstop
    apply stopped_valid_reconstruction flag (z.1.1,z.2) _ n hstop
    simpa only [flag,Tier5.stoppingFlagPolicy,populationPolicy,Option.isSome_map] using hz
  have hm : Monotone (fun n => f n ⁻¹' stoppedPrefixSet flag n) := by
    simp_rw [heq]
    exact stoppedFullSet_mono flag
  have h := klDiv_eq_iSup_map_of_reconstruction (observableDecisionLaw μ A q id)
    (observableDecisionLaw μ A r id) f padJoint (stoppedPrefixSet flag) measurable_jointPrefix
    measurable_padJoint (measurableSet_stoppedPrefix flag hflag) hm (cover q hq) (cover r hr)
    (recn q) (recn r)
  have hmap (b : SignLaw) (n : ℕ) : (observableDecisionLaw μ A b id).map (f n) =
      observablePrefixLaw μ A b n := by
    change ((experimentLaw μ A b).map (fun z => (z.1.1,z.2))).map (f n) = _
    rw [Measure.map_map (show Measurable (f n) from measurable_jointPrefix n) hobs]
    rfl
  simpa only [hmap] using h

/-- The bound for unbounded stopping uses only reference expected work on the
right. Finite work under the opposite endpoint guarantees reconstruction. -/
theorem stopped_null_work_kl {R : Type} [MeasurableSpace R] (μ : Measure Gap)
    [IsProbabilityMeasure μ] (A : AdaptiveEstimator R) (q r : SignLaw)
    (hqhalf : ∀ d, q.val d ≤ 1/2) (hrhalf : ∀ d, r.val d ≤ 1/2)
    (κ B : ℝ) (hκ : 0 ≤ κ) (hB : 0 ≤ B) (hloc : LocalNullWorkBound μ
      (gapParameter false) (gapParameter true) (signUnit q) (signUnit r) κ)
    (hw : expectedWork μ A (smoothedSign q r) ≤ ENNReal.ofReal B)
    (hw' : expectedWork μ A (smoothedSign r q) < ∞) :
    klDiv (observableDecisionLaw μ A (smoothedSign q r) id)
      (observableDecisionLaw μ A (smoothedSign r q) id) ≤ ENNReal.ofReal ((16/3)*κ*B) := by
  have hfin := hw.trans_lt ENNReal.ofReal_lt_top
  rw [stopped_observable_kl_eq_iSup μ A _ _ hfin hw']
  refine iSup_le fun n => (observable_null_work_kl μ A q r hqhalf hrhalf n κ hκ hloc).trans ?_
  apply ENNReal.ofReal_le_ofReal
  have hb := prefix_work_le_total (experimentLaw μ A (smoothedSign q r)) Prod.snd
    observable_tape_measurable hfin n
  have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top hw
  rw [ENNReal.toReal_ofReal hB] at h
  exact mul_le_mul_of_nonneg_left (hb.trans h) (mul_nonneg (by norm_num) hκ)

end ThresholdHC.ConfidenceTransfer
