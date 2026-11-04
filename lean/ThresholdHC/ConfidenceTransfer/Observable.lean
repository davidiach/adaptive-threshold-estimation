import ThresholdHC.ConfidenceTransfer.Creation
import ThresholdHC.StoppingProgram.ObservableInformation
import ThresholdHC.Tier5.PriorRatio

noncomputable section
open MeasureTheory InformationTheory
open scoped ENNReal
namespace ThresholdHC.ConfidenceTransfer
open ThresholdHC.CriticalEntropy ThresholdHC.ObservableSimulation
open ThresholdHC.Tier3 ThresholdHC.Tier4 ThresholdHC.Tier6 ThresholdHC.RareAboveTwo

/-- The ratio of the quarter mixtures is bounded at each queried coin,
irrespective of the largest label the policy happens to use. -/
private theorem creation_quarter_le (μ : Measure Gap) [IsProbabilityMeasure μ]
    (q r : SignLaw) (pol : List Bool → Option ℕ) {n : ℕ} (w : Prefix n) :
    creationPopulationWeight μ pol (fun d : Gap => (d : ℝ))
        (fun d => (quarterPrior (signUnit q) (signUnit r) d : ℝ)) w ≤
      3^n * creationPopulationWeight μ pol (fun d : Gap => (d : ℝ))
        (fun d => (quarterPrior (signUnit r) (signUnit q) d : ℝ)) w := by
  let κ := Measure.infinitePi (fun _ : ℕ => μ)
  let F (s : Gap → unitInterval) (x : ℕ → Gap) :=
    Tier5.creationLaw pol (fun i => (x i : ℝ)) (fun i => (s (x i) : ℝ)) w
  have hint (s : Gap → unitInterval) (hs : Measurable s) : Integrable (F s) κ := by
    have hm : Measurable (F s) := Tier5.measurable_creationLaw (fun _ : ℕ → Gap => pol)
      (fun xs a => by by_cases h : pol xs = a <;> simp [h])
      (fun x i => (x i : ℝ)) (fun x i => (s (x i) : ℝ))
      (fun i => measurable_subtype_coe.comp (measurable_pi_apply i))
      (fun i => (measurable_subtype_coe.comp hs).comp (measurable_pi_apply i)) w
    apply Integrable.of_bound hm.aestronglyMeasurable 1
    apply ae_of_all
    intro x
    have h := Tier5.creationLaw_total n pol (fun i => (x i : ℝ)) (fun i => (s (x i) : ℝ))
      (fun i => ⟨(x i).property.1.le,(x i).property.2⟩) (fun i => (s (x i)).property)
    rw [Real.norm_eq_abs,abs_of_nonneg (h.1 w)]
    exact (Finset.single_le_sum (fun z _ => h.1 z) (Finset.mem_univ w)).trans_eq h.2
  let s := quarterPrior (signUnit q) (signUnit r)
  let t := quarterPrior (signUnit r) (signUnit q)
  change (∫ x, F s x ∂κ) ≤ 3^n * ∫ x, F t x ∂κ
  rw [← integral_const_mul]
  apply integral_mono (hint s (measurable_quarterPrior _ _ (measurable_signUnit _) (measurable_signUnit _)))
    ((hint t (measurable_quarterPrior _ _ (measurable_signUnit _) (measurable_signUnit _))).const_mul _)
  intro x
  apply Tier5.finite_transcript_le_of_prior_ratio_horizon
  · intro i; exact ⟨(x i.val).property.1.le,(x i.val).property.2⟩
  · intro i; exact (t (x i.val)).property
  · intro i; exact (s (x i.val)).property
  · norm_num
  · intro i; dsimp [s,t,quarterPrior,signUnit]; linarith [(r.property.2 (x i.val)).1]
  · intro i; dsimp [s,t,quarterPrior,signUnit]; linarith [(r.property.2 (x i.val)).2]

/-- The smoothed endpoint is still an actual measurable conditional sign law. -/
def smoothedSign (q r : SignLaw) : SignLaw :=
  ⟨fun d => (quarterPrior (signUnit q) (signUnit r) d : ℝ),
   measurable_subtype_coe.comp (measurable_quarterPrior _ _ (measurable_signUnit q) (measurable_signUnit r)),
   fun d => (quarterPrior (signUnit q) (signUnit r) d).property⟩

private theorem smoothedSign_eq_mix (q r : SignLaw) :
    smoothedSign q r = ThresholdHC.StoppingProgram.mixPrior q r (3/4) (by norm_num) := by
  apply Subtype.ext; funext d
  change (3*q.val d+r.val d)/4 = 3/4*q.val d+(1-3/4)*r.val d
  ring

theorem smoothedSign_rare (μ : Measure Gap) [IsProbabilityMeasure μ] {ρ : ℝ}
    (q r : SignLaw) (hq : RarePrior μ ρ q) (hr : RarePrior μ ρ r) :
    RarePrior μ ρ (smoothedSign q r) := by
  rw [smoothedSign_eq_mix]
  exact ThresholdHC.StoppingProgram.mixPrior_rare μ q r hq hr _ _

theorem smoothedSign_separation (μ : Measure Gap) [IsProbabilityMeasure μ] (q r : SignLaw) :
    signMean μ (smoothedSign r q).val - signMean μ (smoothedSign q r).val =
      (signMean μ r.val - signMean μ q.val)/2 := by
  simp only [smoothedSign_eq_mix,ThresholdHC.StoppingProgram.mixPrior_mean]
  ring

/-- The one-type transfer in the original experiment, including the independent
private seed, unrestricted creation labels and actual physical prefix work. -/
theorem observable_null_work_kl {R : Type} [MeasurableSpace R] (μ : Measure Gap)
    [IsProbabilityMeasure μ] (A : AdaptiveEstimator R) (q r : SignLaw)
    (hqhalf : ∀ d, q.val d ≤ 1/2) (hrhalf : ∀ d, r.val d ≤ 1/2) (n : ℕ)
    (κ : ℝ) (hκ : 0 ≤ κ) (hloc : LocalNullWorkBound μ (gapParameter false) (gapParameter true)
      (signUnit q) (signUnit r) κ) :
    klDiv (observablePrefixLaw μ A (smoothedSign q r) n)
      (observablePrefixLaw μ A (smoothedSign r q) n) ≤ ENNReal.ofReal
      ((16/3)*κ*∫ z, ThresholdHC.workOf (processPrefix n z.2) ∂experimentLaw μ A (smoothedSign q r)) := by
  let s := smoothedSign q r
  let t := smoothedSign r q
  let v (b : SignLaw) (u : R) := creationPopulationWeight (n := n) μ (A.policy u) (fun d : Gap => (d : ℝ)) b.val
  have htotal (b : SignLaw) (u : R) := creationPopulationWeight_total μ (A.policy u) (fun d : Gap => (d : ℝ)) b.val
    measurable_subtype_coe b.property.1 (fun d => ⟨d.property.1.le,d.property.2⟩) b.property.2 (n := n)
  have hm (b : SignLaw) (w) : Measurable (fun u => v b u w) := measurable_creationPopulationWeight μ
    A.policy A.policy_measurable _ _ measurable_subtype_coe b.property.1 w
  have hk (b : SignLaw) : ThresholdHC.Tier5.FiniteKernelRealization A.randomLaw (observablePrefixLaw μ A b n) (v b) :=
    observable_population_prefix_kernel A.randomLaw μ (experimentLaw μ A b) Prod.fst Prod.snd A.policy
      _ b.val measurable_fst observable_tape_measurable A.policy_measurable measurable_subtype_coe
      b.property.1 (fun d : Gap => ⟨d.property.1.le,d.property.2⟩) b.property.2 (population_realization R μ A b).2 n
  have hobs : Measurable (fun z : PopulationSeed R × ProcessTape => (z.1.1,processPrefix n z.2)) :=
    measurable_fst.fst.prodMk (measurable_processPrefix Prod.snd observable_tape_measurable n)
  let (b : SignLaw) : IsProbabilityMeasure (observablePrefixLaw μ A b n) :=
    (Measure.isProbabilityMeasure_map_iff hobs.aemeasurable).2 inferInstance
  have he (u) := creation_null_work_kl μ (gapParameter false) (gapParameter true) (signUnit q) (signUnit r)
    (measurable_gapParameter false) (measurable_gapParameter true) (measurable_signUnit q) (measurable_signUnit r)
    hqhalf hrhalf (fun d : Gap => (d : ℝ)) measurable_subtype_coe (fun d => ⟨d.property.1.le,d.property.2⟩)
    (ae_of_all _ (fun d => by simp [gapParameter,sub_eq_add_neg])) (ae_of_all _ (fun d => by simp [gapParameter]))
    (A.policy u) n κ hκ hloc
  have hscalar (u) : ThresholdHC.klFT (v s u) (v t u) ≤ (16/3)*κ*∑ w, v s u w*ThresholdHC.workOf w := by
    have hsupp (w) (hw : v t u w = 0) : v s u w = 0 := by
      have h := creation_quarter_le μ q r (A.policy u) w
      change v s u w ≤ 3^n * v t u w at h
      rw [hw,mul_zero] at h
      exact le_antisymm h ((htotal s u).1 w)
    have h := he u
    change klDiv (finiteWeightMeasure (v s u)) (finiteWeightMeasure (v t u)) ≤ _ at h
    rw [finite_weight_kl _ _ (htotal s u).1 (htotal t u).1 (htotal s u).2 (htotal t u).2 hsupp] at h
    have hnn : 0 ≤ (16/3)*κ*∑ w, v s u w*ThresholdHC.workOf w :=
      mul_nonneg (mul_nonneg (by norm_num) hκ) (Finset.sum_nonneg fun w _ =>
        mul_nonneg ((htotal s u).1 w) (workOf_nonneg w))
    exact (ENNReal.ofReal_le_ofReal_iff hnn).mp h
  have hb := Tier5.finite_kernel_kl_bound A.randomLaw (observablePrefixLaw μ A s n) (observablePrefixLaw μ A t n)
    (v s) (v t) (hm s) (hm t) (fun u => (htotal s u).1) (fun u w =>
      (Finset.single_le_sum (fun j _ => (htotal s u).1 j) (Finset.mem_univ w)).trans_eq (htotal s u).2)
    (fun u => (htotal t u).1) (3^n) (by positivity) (fun u => creation_quarter_le μ q r (A.policy u))
    (fun u => creation_quarter_le μ r q (A.policy u)) (hk s) (hk t) ThresholdHC.workOf ((16/3)*κ) hscalar
  have hf : Measurable (fun z : R × Prefix n => ThresholdHC.workOf z.2) :=
    (measurable_of_countable ThresholdHC.workOf).comp measurable_snd
  have hw := hk s (fun z => ThresholdHC.workOf z.2) hf
    ⟨n,fun z => by rw [abs_of_nonneg (workOf_nonneg z.2)]; exact workOf_le_length z.2⟩
  change (∫ z, ThresholdHC.workOf z.2 ∂(experimentLaw μ A s).map
    (fun z => (z.1.1, processPrefix n z.2))) = _ at hw
  rw [integral_map hobs.aemeasurable hf.aestronglyMeasurable] at hw
  rw [← hw] at hb
  exact hb

end ThresholdHC.ConfidenceTransfer
