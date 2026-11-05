import ThresholdHC.ObservedState.Experiment
import ThresholdHC.Tier4.Full

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace ThresholdHC.ObservedState
open ThresholdHC ThresholdHC.Proofs ThresholdHC.Tier3 ThresholdHC.Tier4
open ThresholdHC.CriticalEntropy ThresholdHC.ObservableSimulation

local instance (m : ℕ) : MeasurableSpace (Option (Fin m)) := ⊤

theorem fixed_word_law {m : ℕ} (p : Fin m → unitInterval) (n : ℕ)
    (pol : List Bool → Option (Fin m)) :
    (Measure.pi (fun i => Tier2.tapeMeasure (p i))).map
      (fun s => (populationSimulation pol n s).2) =
        finiteWeightMeasure (pathProb pol (fun i => (p i : ℝ))) := by
  classical
  apply Measure.ext_of_singleton
  intro w
  have h := populationSimulation_lintegral p n pol
    (({w} : Set (Fin n → Option Bool)).indicator (fun _ => 1))
  rw [← lintegral_map (measurable_const.indicator (measurableSet_singleton w))
    (measurable_populationSimulation_word n pol),lintegral_indicator_fun_one (measurableSet_singleton w)] at h
  simpa only [Set.indicator_apply,Set.mem_singleton_iff,mul_ite,mul_one,mul_zero,
    Finset.sum_ite_eq',Finset.mem_univ,ite_true,finiteWeightMeasure_singleton] using h

theorem model_prefix_integral {m : ℕ} {R : Type} [MeasurableSpace R]
    (A : Estimator m R) (d : Fin m → Tier6.Gap) (s : Fin m → Bool)
    (n : ℕ) (f : R → Prefix n → ℝ)
    (hf : ∀ w, Measurable (fun r => f r w)) (hb : ∃ C : ℝ, ∀ r w, |f r w| ≤ C) :
    (∫ z, f z.1 (processPrefix n z.2) ∂modelLaw A d s) =
      ∫ r, ∑ w, pathProb (A.policy r) (fun i => (gapParameter (s i) (d i) : ℝ)) w * f r w ∂A.randomLaw := by
  obtain ⟨C,hC⟩ := hb
  have hF : Measurable (fun z : R × Prefix n => f z.1 z.2) := measurable_from_prod_countable_left hf
  have hp : ∀ xs, Measurable (fun r => A.policy r xs) :=
    fun xs => measurable_to_countable' (fun a => A.policy_measurable xs a)
  have hm := measurable_fst.prodMk (measurable_seeded_populationSimulation n A.policy hp)
  have hi : Integrable (fun z : R × (Fin m → ℕ → Bool) =>
      f z.1 (populationSimulation (A.policy z.1) n z.2).2)
      (A.randomLaw.prod (Measure.pi (fun i => Tier2.tapeMeasure (gapParameter (s i) (d i))))) :=
    Tier5.integrable_of_abs_bound _ _ (hF.comp hm) C (fun z => hC _ _)
  have hprefix : Measurable (fun z : R × ProcessTape => f z.1 (processPrefix n z.2)) :=
    hF.comp (measurable_jointPrefix n)
  rw [modelLaw,integral_map (f := fun z : R × ProcessTape => f z.1 (processPrefix n z.2))
    (measurable_observation A).aemeasurable hprefix.aestronglyMeasurable]
  simp_rw [populationPath_prefix]
  rw [integral_prod _ hi]
  apply integral_congr_ae
  apply ae_of_all
  intro r
  dsimp only
  have hl := fixed_word_law (fun i => gapParameter (s i) (d i)) n (A.policy r)
  rw [← integral_map (measurable_populationSimulation_word n (A.policy r)).aemeasurable
      (measurable_of_countable (f r)).aestronglyMeasurable,hl]
  have : IsProbabilityMeasure
      (finiteWeightMeasure (pathProb (n := n) (A.policy r) (fun i => (gapParameter (s i) (d i) : ℝ)))) := by
    rw [← hl]
    infer_instance
  rw [integral_fintype (Integrable.of_finite)]
  apply Finset.sum_congr rfl
  intro w _
  rw [finiteWeightMeasure_real_singleton _ (fun w =>
    pathProb_nonneg _ _ (fun i => (gapParameter (s i) (d i)).property) w)]
  rfl

theorem signLaw_singleton {m : ℕ} (q : Fin m → unitInterval) (s : Fin m → Bool) :
    (signLaw q).real {s} = ∏ i, if s i then (q i : ℝ) else 1 - (q i : ℝ) := by
  rw [measureReal_def,signLaw,Measure.pi_singleton,ENNReal.toReal_prod]
  apply Finset.prod_congr rfl
  intro i _
  change (bernoulliMeasure true false (q i)).real {s i} = _
  cases s i <;> simp

theorem measurable_pathProb_policy {m n : ℕ} {R : Type} [MeasurableSpace R]
    (A : Estimator m R) (p : Fin m → ℝ) (w : Prefix n) :
    Measurable (fun r => pathProb (A.policy r) p w) := by
  unfold pathProb
  apply Finset.measurable_prod
  intro t _
  let g (a : Option (Fin m)) : ℝ :=
    match a, w t with
    | none, none => 1
    | some i, some true => p i
    | some i, some false => 1 - p i
    | _, _ => 0
  exact (measurable_of_countable g).comp
    (measurable_to_countable' (fun a => A.policy_measurable (histBefore w t) a))

theorem bayes_realizes {m : ℕ} {R : Type} [MeasurableSpace R]
    (A : Estimator m R) (d : Fin m → Tier6.Gap) (q : Fin m → unitInterval) :
    RealizesPrefixes A.randomLaw (bayesLaw A d q) Prod.fst Prod.snd A.policy
      (fun i => d i) (fun i => q i) := by
  intro n f hf hb
  obtain ⟨C,hC⟩ := hb
  have hfm : Measurable (fun z : R × Prefix n => f z.1 z.2) := measurable_from_prod_countable_left hf
  have hF : Measurable (fun z : R × ProcessTape => f z.1 (processPrefix n z.2)) :=
    hfm.comp (measurable_jointPrefix n)
  have hi s : Integrable (fun z : R × ProcessTape => f z.1 (processPrefix n z.2)) (modelLaw A d s) :=
    Tier5.integrable_of_abs_bound _ _ hF C (fun z => hC _ _)
  rw [bayesLaw,integral_finsetSum_measure (fun s _ => (hi s).smul_measure (measure_ne_top _ _))]
  simp_rw [integral_smul_measure,smul_eq_mul,model_prefix_integral A d _ n f hf ⟨C,hC⟩]
  have hsum (s : Fin m → Bool) : Integrable (fun r =>
      (signLaw q).real {s} * ∑ w, pathProb (A.policy r) (fun i => (gapParameter (s i) (d i) : ℝ)) w * f r w)
      A.randomLaw := by

    have hi' : Integrable (fun r => ∑ w, pathProb (A.policy r)
        (fun i => (gapParameter (s i) (d i) : ℝ)) w * f r w) A.randomLaw := by
      refine Tier5.integrable_of_abs_bound _ _ ?_ C ?_
      · apply Finset.measurable_sum
        intro w _
        exact (measurable_pathProb_policy A _ w).mul (hf w)
      · intro r
        apply (Finset.abs_sum_le_sum_abs _ _).trans
        calc
          _ ≤ ∑ w, pathProb (A.policy r) (fun i => (gapParameter (s i) (d i) : ℝ)) w * C := by
            apply Finset.sum_le_sum
            intro w _
            rw [abs_mul,abs_of_nonneg (pathProb_nonneg _ _ (fun i => (gapParameter (s i) (d i)).property) w)]
            exact mul_le_mul_of_nonneg_left (hC r w) (pathProb_nonneg _ _ (fun i => (gapParameter (s i) (d i)).property) w)
          _ = C := by rw [← Finset.sum_mul,pathProb_total,one_mul]
    exact hi'.const_mul _
  simp_rw [← integral_const_mul]
  change (∑ s, ∫ r, (signLaw q).real {s} * ∑ w,
    pathProb (A.policy r) (fun i => (gapParameter (s i) (d i) : ℝ)) w * f r w ∂A.randomLaw) = _
  rw [← integral_finsetSum _ (fun s _ => hsum s)]
  apply integral_congr_ae
  apply ae_of_all
  intro r
  simp only [signLaw_singleton,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro w _
  rw [transcriptLaw,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro s _
  simp only [gapParameter]
  ring

end ThresholdHC.ObservedState
