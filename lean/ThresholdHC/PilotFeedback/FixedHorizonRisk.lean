import ThresholdHC.PilotFeedback.OrderedPopulation
import ThresholdHC.StoppingProgram.TruncatedPrefix
import ThresholdHC.ContinuousObserved.Tape

namespace ThresholdHC.PilotFeedback.FixedHorizon
open Ordered
noncomputable section
open MeasureTheory Set
open scoped ENNReal
open ThresholdHC ThresholdHC.Proofs ThresholdHC.Tier3 ThresholdHC.Tier4 ThresholdHC.Tier5 ThresholdHC.Tier6
open ThresholdHC.SharpRMS ThresholdHC.SharpRMS.LargeBudget ThresholdHC.SharpRMS.Pilot

/-- A common horizon gives an observed tape which can be reconstructed from
its ordered bit word even for estimators with unbounded outputs. -/
def Capped {R : Type} [MeasurableSpace R] (A : AdaptiveEstimator R) : Prop :=
  ∀ r, ∃ label : List Bool → ℕ, A.policy r = HardBudget.stopAt 25 label

private def asTape (xs : List Bool) : ProcessTape := fun n => xs[n]?

private theorem recover (s : List Bool → ℕ) (x : ProcessTape)
    (valid : ∀ k, (x k).isSome = (HardBudget.stopAt 25 s (processHistory x k)).isSome) :
    asTape (fullHist (processPrefix 25 x)) = x := by
  have len (n : ℕ) (hn : n≤25) : (processHistory x n).length=n := by
    induction n with
    | zero => simp [processHistory]
    | succ n ih =>
      have l := ih (by omega)
      have some' := valid n
      simp [HardBudget.stopAt,l,show n<25 by omega] at some'
      rw [ContinuousObserved.processHistory_succ,List.length_append,l]
      cases e : x n <;> simp_all
  have stop : HardBudget.stopAt 25 s (processHistory x 25)=none := by simp [HardBudget.stopAt,len 25 le_rfl]
  have recov := StoppingProgram.valid_path_halt_reconstruction (HardBudget.stopAt 25 s) x valid 25 stop
  let bits (i : Fin 25) := (x i).getD false
  have word : processPrefix 25 x = fun i => some (bits i) := by
    funext i
    have h := valid i
    simp [HardBudget.stopAt,len i i.isLt.le,i.isLt] at h
    cases e : x i <;> simp_all [processPrefix,bits]
  apply Eq.trans _ recov
  rw [word,Revisit.full_bits]
  funext n
  by_cases h : n<25
  · rw [asTape,List.getElem?_eq_getElem (by simpa only [List.length_ofFn] using h),List.getElem_ofFn]
    simp only [padPrefix,dite_eq_left h]
  · rw [asTape,List.getElem?_eq_none (by simp only [List.length_ofFn]; omega)]
    simp only [padPrefix,dite_eq_right h]

private def lawAt (i : Fin 4) : SignLaw := ⟨fun _ => prob i,measurable_const,fun _ => prob_mem i⟩

private def estimate {R : Type} [MeasurableSpace R] (A : AdaptiveEstimator R) (r : R) (xs : List Bool) :=
  HardBudget.clipEstimate 1 (A.output (r,asTape xs))

private def sq {R : Type} [MeasurableSpace R] (A : AdaptiveEstimator R) (i : Fin 4)
    (r : R) (w : Prefix 25) := (estimate A r (fullHist w)-prob i)^2

private theorem sq_meas {R : Type} [MeasurableSpace R] (A : AdaptiveEstimator R) (i : Fin 4)
    (w : Prefix 25) : Measurable (fun r => sq A i r w) := by
  unfold sq estimate HardBudget.clipEstimate
  exact ((measurable_const.max (measurable_const.min
    (A.output_measurable.comp (measurable_id.prodMk measurable_const)))).sub measurable_const).pow_const 2

private theorem sq_bound {R : Type} [MeasurableSpace R] (A : AdaptiveEstimator R) (i : Fin 4)
    (r : R) (w : Prefix 25) : |sq A i r w| ≤ 1 := by
  have h : estimate A r (fullHist w) ∈ Icc 0 1 :=
    ⟨le_max_left ..,max_le (by norm_num) (min_le_left ..)⟩
  have p := prob_mem i
  unfold sq
  rw [abs_of_nonneg (sq_nonneg _)]
  have l : 0 ≤ 1+(estimate A r (fullHist w)-prob i) := by linarith [h.1,p.2]
  have u : 0 ≤ 1-(estimate A r (fullHist w)-prob i) := by linarith [h.2,p.1]
  nlinarith [mul_nonneg l u]

private def conditionalMSE {R : Type} [MeasurableSpace R] (A : AdaptiveEstimator R) (i : Fin 4) (r : R) :=
  ∑ w : Prefix 25, Revisit.law (A.policy r) (prob i) w * sq A i r w

private theorem cond_integrable {R : Type} [MeasurableSpace R] (A : AdaptiveEstimator R) (i : Fin 4) :
    Integrable (conditionalMSE A i) A.randomLaw := by
  have hm : Measurable (conditionalMSE A i) := by
    apply Finset.measurable_sum
    intro w _
    exact (measurable_creationLaw A.policy A.policy_measurable _ _ (fun _ => measurable_const)
      (fun _ => measurable_const) w).mul (sq_meas A i w)
  apply (integrable_const (1:ℝ)).mono' hm.aestronglyMeasurable
  apply ae_of_all
  intro r
  have h := creationLaw_total 25 (A.policy r) (fun _ => 1/5) (fun _ => prob i)
    (fun _ => by norm_num) (fun _ => prob_mem i)
  change |∑ w, Revisit.law (A.policy r) (prob i) w * sq A i r w| ≤ 1
  apply (Finset.abs_sum_le_sum_abs ..).trans
  rw [←h.2]
  apply Finset.sum_le_sum
  intro w _
  rw [abs_mul,abs_of_nonneg (h.1 w)]
  simpa using mul_le_mul_of_nonneg_left (sq_bound A i r w) (h.1 w)

private theorem risk_le {R : Type} [MeasurableSpace R] (A : AdaptiveEstimator R) (hc : Capped A) (i : Fin 4) :
    ENNReal.ofReal (∫ r, conditionalMSE A i r ∂A.randomLaw) ≤
      squaredRisk (experimentLaw (Measure.dirac fifthGap) A (lawAt i))
        (populationOutput A) (signMean (Measure.dirac fifthGap) (lawAt i).val) := by
  let P := experimentLaw (Measure.dirac fifthGap) A (lawAt i)
  let F := fun (u : PopulationSeed R) (w : Prefix 25) => sq A i u.1 w
  have hr := (population_realization R (Measure.dirac fifthGap) A (lawAt i)).2
    25 F (fun w => (sq_meas A i w).comp measurable_fst) ⟨1,fun u w => sq_bound A i u.1 w⟩
  have hm : Measurable (fun u : PopulationSeed R => ∑ w,
      creationLaw (populationPolicy A u) (populationGap u) (populationPrior (lawAt i) u) w * F u w) := by
    apply Finset.measurable_sum
    intro w _
    exact (measurable_creationLaw _ (measurable_populationPolicy A) _ _ measurable_populationGap
      (measurable_populationPrior (lawAt i)) w).mul ((sq_meas A i w).comp measurable_fst)
  have hmap : Measurable (fun r : R => (r,fun _ : ℕ => fifthGap)) := measurable_id.prodMk measurable_const
  rw [populationSeedLaw,Measure.infinitePi_dirac,Measure.prod_dirac,integral_map hmap.aemeasurable hm.aestronglyMeasurable] at hr
  let G := fun z : PopulationSeed R × ProcessTape => F z.1 (processPrefix 25 z.2)
  change (∫ z, G z ∂P) = ∫ r, conditionalMSE A i r ∂A.randomLaw at hr
  have Gm : Measurable G := by
    have Fm : Measurable (fun z : R × Prefix 25 => sq A i z.1 z.2) := measurable_from_prod_countable_left (sq_meas A i)
    exact Fm.comp (measurable_fst.fst.prodMk (measurable_snd.comp (measurable_jointPrefix 25)))
  have Gi : Integrable G P := (integrable_const (1:ℝ)).mono' Gm.aestronglyMeasurable (ae_of_all _ fun z => sq_bound ..)
  rw [←hr,ofReal_integral_eq_lintegral_ofReal Gi (ae_of_all _ fun _ => sq_nonneg _)]
  apply lintegral_mono_ae
  filter_upwards [StoppingProgram.original_path_valid (Measure.dirac fifthGap) A (lawAt i)] with z hz
  obtain ⟨s, hs⟩ := hc z.1.1
  rw [hs] at hz
  change ENNReal.ofReal ((HardBudget.clipEstimate 1 (A.output (z.1.1,asTape (fullHist (processPrefix 25 z.2))))-prob i)^2) ≤ _
  rw [recover s z.2 hz,show signMean (Measure.dirac fifthGap) (lawAt i).val=prob i by simp [signMean,lawAt]]
  exact HardBudget.clip_loss_le 1 (prob i) _ (prob_mem i)

/-- Lift a four-point Bayes inequality for every terminal word function and
every private seed to the original experiment's four-point worst MSE. -/
theorem lower_of_word_bound {R : Type} [MeasurableSpace R] (A : AdaptiveEstimator R) (hc : Capped A)
    (c : ℝ) (h₀ : 0 ≤ c)
    (bound : ∀ (r : R) (X : List Bool → ℝ), c ≤ ∑ i, prior i *
      ∑ w : Prefix 25, Revisit.law (A.policy r) (prob i) w * (X (fullHist w)-prob i)^2) :
    ENNReal.ofReal c ≤ Ordered.fourRisk A := by
  have hr (r : R) : c ≤ ∑ i, prior i * conditionalMSE A i r := bound r (estimate A r)
  have hi := integral_mono_of_nonneg (μ := A.randomLaw) (f := fun _ => c)
    (ae_of_all _ fun _ => h₀) (integrable_finsetSum _ fun i _ => (cond_integrable A i).const_mul _) (ae_of_all _ hr)
  simp only [integral_const,probReal_univ,one_smul,integral_finsetSum _ (fun i _ => (cond_integrable A i).const_mul _),
    integral_const_mul] at hi
  apply (ENNReal.ofReal_le_ofReal hi).trans
  have nonneg (i : Fin 4) : 0 ≤ ∫ r, conditionalMSE A i r ∂A.randomLaw := by
    apply integral_nonneg
    intro r
    unfold conditionalMSE
    apply Finset.sum_nonneg
    intro w _
    exact mul_nonneg ((creationLaw_total _ _ _ _ (fun _ => by norm_num) (fun _ => prob_mem i)).1 w) (sq_nonneg _)
  rw [ENNReal.ofReal_sum_of_nonneg (fun i _ => mul_nonneg (prior_nonneg i) (nonneg i))]
  simp only [ENNReal.ofReal_mul (prior_nonneg _)]
  calc
    _ ≤ ∑ i : Fin 4, ENNReal.ofReal (prior i) * fourRisk A := by
      apply Finset.sum_le_sum
      intro i _
      gcongr
      exact (risk_le A hc i).trans (le_iSup (fun i => squaredRisk (experimentLaw (Measure.dirac fifthGap) A (lawAt i))
        (populationOutput A) (signMean (Measure.dirac fifthGap) (lawAt i).val)) i)
    _ = _ := by
      rw [← Finset.sum_mul, ← ENNReal.ofReal_sum_of_nonneg (fun i _ => prior_nonneg i)]
      norm_num [Fin.sum_univ_succ,prior]

end
end ThresholdHC.PilotFeedback.FixedHorizon
