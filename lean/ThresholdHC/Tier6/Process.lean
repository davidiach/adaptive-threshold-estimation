import ThresholdHC.Tier6.ProcessIntegral
import ThresholdHC.Tier6.Specification

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace ThresholdHC.Tier6
open ThresholdHC.Proofs ThresholdHC.Tier3 ThresholdHC.Tier4 ThresholdHC.Tier5

set_option maxHeartbeats 600000 in
theorem creationTrajectoryLaw_realizes {Seed : Type} [MeasurableSpace Seed]
    (μ : Measure Seed) [IsProbabilityMeasure μ]
    (pol : Seed → List Bool → Option ℕ) (d q : Seed → ℕ → ℝ)
    (hp : MeasurableCreationPolicy pol) (hdm : MeasurableEnvironment d)
    (hqm : MeasurableEnvironment q)
    (hd : ∀ u i, 0 ≤ d u i ∧ d u i ≤ 1/2)
    (hq : ∀ u i, 0 ≤ q u i ∧ q u i ≤ 1) :
    RealizesCreationPrefixes μ (creationTrajectoryLaw μ pol d q hp hdm hqm hd hq)
      (fun x => x 0) (fun x => (coordTranscript x).2) pol d q := by
  intro n
  induction n with
  | zero =>
    intro f hf hb
    have hp0 (u : Seed) (w : Prefix 0) : creationLaw (pol u) (d u) (q u) w = 1 := by
      have h := (creationLaw_total 0 (pol u) (d u) (q u) (hd u) (hq u)).2
      rw [Fintype.sum_unique] at h
      convert h using 1
      congr 1
      exact Subsingleton.elim _ _
    have hseed : (creationTrajectoryLaw μ pol d q hp hdm hqm hd hq).map (fun x => x 0) = μ := by
      letI : ∀ k, IsMarkovKernel (creationStepKernel pol d q hp hdm hqm k) :=
        fun k => creationStepKernel_markov pol d q hp hdm hqm hd hq k
      unfold creationTrajectoryLaw
      exact trajMeasure_map_zero (X := ProcessCoord Seed) μ (creationStepKernel pol d q hp hdm hqm)
    calc
      _ = ∫ x, f (x 0) (default : Prefix 0)
          ∂creationTrajectoryLaw μ pol d q hp hdm hqm hd hq := by
        apply integral_congr_ae
        filter_upwards [] with x
        congr 1
        exact Subsingleton.elim _ _
      _ = ∫ u, f u (default : Prefix 0)
          ∂(creationTrajectoryLaw μ pol d q hp hdm hqm hd hq).map (fun x => x 0) := by
        exact (integral_map
          (μ := creationTrajectoryLaw μ pol d q hp hdm hqm hd hq)
          (φ := fun x : (n : ℕ) → ProcessCoord Seed n => (x 0 : Seed))
          (f := fun u => f u (default : Prefix 0))
          (measurable_pi_apply 0).aemeasurable
          (hf (default : Prefix 0)).aestronglyMeasurable).symm
      _ = ∫ u, f u (default : Prefix 0) ∂μ :=
        congrArg (fun M : Measure Seed => ∫ u, f u (default : Prefix 0) ∂M) hseed
      _ = _ := by
        apply integral_congr_ae
        filter_upwards [] with u
        simp only [Fintype.sum_unique, hp0, one_mul]
        exact congrArg (f u) (Subsingleton.elim _ _)
  | succ n ih =>
    intro f hf hb
    obtain ⟨C,hC⟩ := hb
    let g : Seed → Prefix n → ℝ := fun u w =>
      ∑ o : Option Bool, creationTransition (pol u) (d u) (q u) w o * f u (Fin.snoc w o)
    have hgm (w : Prefix n) : Measurable (fun u => g u w) := by
      apply Finset.measurable_sum
      intro o ho
      exact (measurable_creationTransition pol hp d q hdm hqm w o).mul (hf (Fin.snoc w o))
    have hgb (u : Seed) (w : Prefix n) : |g u w| ≤ C := by
      calc
        _ ≤ ∑ o : Option Bool, |creationTransition (pol u) (d u) (q u) w o *
            f u (Fin.snoc w o)| := Finset.abs_sum_le_sum_abs _ _
        _ = ∑ o : Option Bool, creationTransition (pol u) (d u) (q u) w o *
            |f u (Fin.snoc w o)| := by
          apply Finset.sum_congr rfl
          intro o ho
          rw [abs_mul, abs_of_nonneg (creationTransition_nonneg _ _ _ (hd u) (hq u) w o)]
        _ ≤ ∑ o : Option Bool, creationTransition (pol u) (d u) (q u) w o * C :=
          Finset.sum_le_sum fun o ho => mul_le_mul_of_nonneg_left (hC u _)
            (creationTransition_nonneg _ _ _ (hd u) (hq u) w o)
        _ = C := by rw [← Finset.sum_mul, creationTransition_sum, one_mul]
    calc
      _ = ∫ x, g (x 0) (processPrefix n (coordTranscript x).2)
          ∂creationTrajectoryLaw μ pol d q hp hdm hqm hd hq :=
        creationTrajectoryLaw_integral_step μ pol d q hp hdm hqm hd hq n f hf C hC
      _ = ∫ u, ∑ w : Prefix n, creationLaw (pol u) (d u) (q u) w * g u w ∂μ :=
        ih g hgm ⟨C,hgb⟩
      _ = _ := by
        apply integral_congr_ae
        filter_upwards [] with u
        rw [sum_snoc]
        apply Finset.sum_congr rfl
        intro w hw
        simp only [g, Finset.mul_sum, ← mul_assoc, creationTransition_mul _ _ _ (hd u) (hq u)]

theorem creationProcessLaw_realizes {Seed : Type} [MeasurableSpace Seed]
    (μ : Measure Seed) [IsProbabilityMeasure μ]
    (pol : Seed → List Bool → Option ℕ) (d q : Seed → ℕ → ℝ)
    (hp : MeasurableCreationPolicy pol) (hdm : MeasurableEnvironment d)
    (hqm : MeasurableEnvironment q)
    (hd : ∀ u i, 0 ≤ d u i ∧ d u i ≤ 1/2)
    (hq : ∀ u i, 0 ≤ q u i ∧ q u i ≤ 1) :
    RealizesCreationPrefixes μ (creationProcessLaw μ pol d q hp hdm hqm hd hq)
      Prod.fst Prod.snd pol d q := by
  intro n f hf hb
  have hfm : Measurable (fun z : Seed × Prefix n => f z.1 z.2) :=
    measurable_from_prod_countable_left hf
  have hprefix : Measurable (fun z : Seed × ProcessTape => (z.1, processPrefix n z.2)) := by
    apply measurable_fst.prodMk
    apply Measurable.of_eval
    intro i
    exact (measurable_pi_apply i.val).comp measurable_snd
  change (∫ z, f z.1 (processPrefix n z.2)
    ∂(creationTrajectoryLaw μ pol d q hp hdm hqm hd hq).map coordTranscript) = _
  have hmap := integral_map
    (μ := creationTrajectoryLaw μ pol d q hp hdm hqm hd hq)
    (φ := coordTranscript (Seed := Seed))
    (f := fun z : Seed × ProcessTape => f z.1 (processPrefix n z.2))
    measurable_coordTranscript.aemeasurable (hfm.comp hprefix).aestronglyMeasurable
  exact hmap.trans (creationTrajectoryLaw_realizes μ pol d q hp hdm hqm hd hq n f hf hb)

theorem process_realization : ProcessRealizationStatement := by
  intro Seed _ μ _ pol d q hp hdm hqm hd hq
  exact creationProcessLaw_realizes μ pol d q hp hdm hqm hd hq

end ThresholdHC.Tier6
