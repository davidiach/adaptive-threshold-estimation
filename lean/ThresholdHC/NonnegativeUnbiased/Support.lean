import ThresholdHC.NonnegativeUnbiased.Specification
import ThresholdHC.StoppingProgram.TruncatedPrefix
import ThresholdHC.Tier6.Full
import ThresholdHC.Tier5.FiniteCreation
import ThresholdHC.Tier4.StoppedReconstruction
import ThresholdHC.Proofs.Tier2.TranscriptLikelihood

/-! The proof of Proposition prop:bounded, first sentence.

Under the all-negative sign law the target is zero, so a nonnegative unbiased
output vanishes almost surely. Under the law `1{d < 1/2}` every finite
transcript has positive probability only if it has positive probability under
the all-negative law: interior gaps give both signs positive likelihood, and
the endpoint gap is negative under both laws (`support_compare`). Once the
policy stops, a valid tape stays empty, so the output is a function of a
finite prefix. Hence the event that the policy has stopped by step `n` with
nonzero output has probability zero under `1{d < 1/2}` for every `n`, and
since the algorithm stops almost surely its output vanishes there too, while
its target is `μ((0,1/2)) > 0`. -/
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace ThresholdHC.NonnegativeUnbiased
open ThresholdHC ThresholdHC.Tier3 ThresholdHC.Tier4 ThresholdHC.Tier5 ThresholdHC.Tier6
open ThresholdHC.Proofs ThresholdHC.UnbiasedConverse

theorem history_succ (x : ProcessTape) (n : ℕ) :
    processHistory x (n+1) = processHistory x n ++ (x n).toList := by
  unfold processHistory
  rw [List.ofFn_succ', List.concat_eq_append, List.filterMap_append]
  cases h : x n <;> simp [processPrefix, h] <;> rfl

theorem stopped_tail (pol : List Bool → Option ℕ) (x : ProcessTape)
    (valid : ∀ k, (x k).isSome = (pol (processHistory x k)).isSome) (n : ℕ)
    (h : pol (processHistory x n) = none) :
    ∀ j, n ≤ j → x j = none ∧ processHistory x j = processHistory x n := by
  intro j hj
  induction j, hj using Nat.le_induction with
  | base =>
    refine ⟨?_, rfl⟩
    have hv := valid n
    rw [h] at hv
    simpa using hv
  | succ j hj ih =>
    have hh : processHistory x (j+1) = processHistory x n := by
      rw [history_succ, ih.1, ih.2]; simp
    refine ⟨?_, hh⟩
    have hv := valid (j+1)
    rw [hh, h] at hv
    simpa using hv

/-- The tape that repeats a prefix and then stays empty. -/
def pad {n : ℕ} (w : Prefix n) : ProcessTape := fun i => if h : i < n then w ⟨i, h⟩ else none

/-- The observed bits of a prefix. -/
def hist {n : ℕ} (w : Prefix n) : List Bool := (List.ofFn w).filterMap id

theorem pad_prefix (pol : List Bool → Option ℕ) (x : ProcessTape)
    (valid : ∀ k, (x k).isSome = (pol (processHistory x k)).isSome) (n : ℕ)
    (h : pol (processHistory x n) = none) : pad (processPrefix n x) = x := by
  funext i
  unfold pad
  split_ifs with hi
  · rfl
  · exact ((stopped_tail pol x valid n h i (by omega)).1).symm

theorem coinLike_ne_zero {m n : ℕ} (pol : List Bool → Option (Fin m)) (ω : Fin n → Option Bool)
    (i : Fin m) {p p' : ℝ} (hp' : 0 < p' ∧ p' < 1) (h : coinLike pol ω i p ≠ 0) :
    coinLike pol ω i p' ≠ 0 := by
  unfold coinLike at *
  rw [Finset.prod_ne_zero_iff] at *
  intro t ht
  have ht' := h t ht
  split_ifs at ht' ⊢ with hs
  · cases hω : ω t with
    | none => rw [hω] at ht'; simp [obsProb] at ht'
    | some b => cases b <;> simp [obsProb] <;> linarith [hp'.1, hp'.2]
  · exact one_ne_zero

/-- Interior gaps give both signs positive likelihood and the endpoint gap is
negative under both priors, so every transcript possible under the prior
`1{d < 1/2}` is possible under the all-negative prior. -/
theorem support_compare {n : ℕ} (pol : List Bool → Option ℕ) (d : ℕ → ℝ)
    (hd : ∀ i, 0 < d i ∧ d i ≤ 1/2) (w : Prefix n)
    (h1 : creationLaw pol d (fun i => if d i < 1/2 then 1 else 0) w ≠ 0) :
    creationLaw pol d (fun _ => 0) w ≠ 0 := by
  unfold creationLaw at *
  rw [transcriptLaw_factor] at *
  obtain ⟨hv, hp⟩ := mul_ne_zero_iff.mp h1
  refine mul_ne_zero hv ?_
  rw [Finset.prod_ne_zero_iff] at *
  intro i hi
  have hpi := hp i hi
  simp only [zero_mul, sub_zero, one_mul, zero_add]
  have hdi := hd i.val
  by_cases hlt : d i.val < 1/2
  · simp only [hlt, ite_true, one_mul, sub_self, zero_mul, add_zero] at hpi
    exact coinLike_ne_zero _ _ _ ⟨by linarith, by linarith⟩ hpi
  · simp only [hlt, ite_false, zero_mul, sub_zero, one_mul, zero_add] at hpi
    exact hpi

open Classical in
/-- The indicator, read from a prefix of length `n`, that the policy has
stopped and the output of the padded tape is nonzero. -/
def stopEvent {R : Type} [MeasurableSpace R] (A : AdaptiveEstimator R) (n : ℕ)
    (u : PopulationSeed R) (w : Prefix n) : ℝ :=
  if A.policy u.1 (hist w) = none ∧ A.output (u.1, pad w) ≠ 0 then 1 else 0

theorem stopEvent_measurable {R : Type} [MeasurableSpace R] (A : AdaptiveEstimator R) (n : ℕ)
    (w : Prefix n) : Measurable (fun u : PopulationSeed R => stopEvent A n u w) := by
  classical
  have hS : MeasurableSet {u : PopulationSeed R |
      A.policy u.1 (hist w) = none ∧ A.output (u.1, pad w) ≠ 0} := by
    exact (measurable_fst (A.policy_measurable (hist w) none)).inter
      ((A.output_measurable.comp (measurable_fst.prodMk measurable_const))
        (measurableSet_singleton (0:ℝ)).compl)
  unfold stopEvent
  exact Measurable.ite hS measurable_const measurable_const

theorem stopEvent_bound {R : Type} [MeasurableSpace R] (A : AdaptiveEstimator R) (n : ℕ)
    (u : PopulationSeed R) (w : Prefix n) : 0 ≤ stopEvent A n u w ∧ stopEvent A n u w ≤ 1 := by
  unfold stopEvent; split_ifs <;> norm_num

theorem stopEvent_joint {R : Type} [MeasurableSpace R] (A : AdaptiveEstimator R) (n : ℕ) :
    Measurable (fun z : PopulationSeed R × ProcessTape => stopEvent A n z.1 (processPrefix n z.2)) := by
  have hF : Measurable (fun p : PopulationSeed R × Prefix n => stopEvent A n p.1 p.2) :=
    measurable_from_prod_countable_left (fun w => stopEvent_measurable A n w)
  exact hF.comp (measurable_jointPrefix n)

/-- Proposition prop:bounded, first sentence: if `μ((0,1/2)) > 0`, no algorithm that stops almost
surely and has almost surely nonnegative output under every sign law is unbiased. -/
theorem nonnegative_not_unbiased (R : Type) [MeasurableSpace R] (μ : Measure Gap)
    [IsProbabilityMeasure μ] (A : AdaptiveEstimator R)
    (hμ : 0 < μ {d : Gap | (d : ℝ) < 1/2})
    (hstop : ∀ q : SignLaw, ∀ᵐ z ∂experimentLaw μ A q,
      ∃ n, A.policy z.1.1 (processHistory z.2 n) = none)
    (hnn : ∀ q : SignLaw, ∀ᵐ z ∂experimentLaw μ A q, 0 ≤ populationOutput A z) :
    ¬ UniformlyUnbiased μ A := by
  intro hu
  let q0 : SignLaw := ⟨fun _ => 0, measurable_const, fun _ => ⟨le_rfl, zero_le_one⟩⟩
  have hq1m : Measurable (fun d : Gap => if (d : ℝ) < 1/2 then (1 : ℝ) else 0) :=
    Measurable.ite (measurableSet_lt measurable_subtype_coe measurable_const)
      measurable_const measurable_const
  let q1 : SignLaw := ⟨fun d => if (d : ℝ) < 1/2 then 1 else 0, hq1m,
    fun d => by dsimp only; split_ifs <;> norm_num⟩
  -- Under the all-negative law the target is zero, so the output vanishes.
  have h0 : ∀ᵐ z ∂experimentLaw μ A q0, populationOutput A z = 0 := by
    obtain ⟨hi, he⟩ := hu q0
    have hθ : signMean μ q0.val = 0 := by simp [signMean, q0]
    rw [hθ] at he
    exact (integral_eq_zero_iff_of_nonneg_ae (hnn q0) hi).1 he
  -- Every stopped transcript with nonzero output has probability zero under `q1`.
  have hE : ∀ n, ∀ᵐ z ∂experimentLaw μ A q1, stopEvent A n z.1 (processPrefix n z.2) = 0 := by
    intro n
    have real (q : SignLaw) := (population_realization R μ A q).2 n (stopEvent A n)
      (fun w => stopEvent_measurable A n w)
      ⟨1, fun u w => by
        have hb := stopEvent_bound A n u w
        rw [abs_le]; constructor <;> linarith [hb.1, hb.2]⟩
    have hzero0 : (∫ z, stopEvent A n z.1 (processPrefix n z.2) ∂experimentLaw μ A q0) = 0 := by
      apply integral_eq_zero_of_ae
      filter_upwards [h0, StoppingProgram.original_path_valid μ A q0] with z hz hv
      change stopEvent A n z.1 (processPrefix n z.2) = 0
      unfold stopEvent
      rw [ite_eq_right_iff]
      rintro ⟨hs, ho⟩
      exact absurd (by rw [pad_prefix (A.policy z.1.1) z.2 hv n hs]; exact hz) ho
    rw [real q0] at hzero0
    let G (q : SignLaw) (u : PopulationSeed R) := ∑ w : Prefix n,
      creationLaw (populationPolicy A u) (populationGap u) (populationPrior q u) w * stopEvent A n u w
    have cnn (q : SignLaw) (u : PopulationSeed R) := (creationLaw_total n (populationPolicy A u)
      (populationGap u) (populationPrior q u) (populationGap_range u) (populationPrior_range q u))
    have Gm (q : SignLaw) : Measurable (G q) := Finset.measurable_sum _ fun w _ =>
      (measurable_creationLaw _ (measurable_populationPolicy A) _ _ measurable_populationGap
        (measurable_populationPrior q) w).mul (stopEvent_measurable A n w)
    have Gnn (q : SignLaw) (u : PopulationSeed R) : 0 ≤ G q u := Finset.sum_nonneg fun w _ =>
      mul_nonneg ((cnn q u).1 w) (stopEvent_bound A n u w).1
    have Gle (q : SignLaw) (u : PopulationSeed R) : G q u ≤ 1 := by
      calc G q u ≤ ∑ w : Prefix n,
            creationLaw (populationPolicy A u) (populationGap u) (populationPrior q u) w * 1 :=
            Finset.sum_le_sum fun w _ =>
              mul_le_mul_of_nonneg_left (stopEvent_bound A n u w).2 ((cnn q u).1 w)
        _ = 1 := by simp only [mul_one]; exact (cnn q u).2
    have Gi (q : SignLaw) : Integrable (G q) (populationSeedLaw μ A) :=
      (integrable_const (1:ℝ)).mono' (Gm q).aestronglyMeasurable (ae_of_all _ fun u => by
        rw [Real.norm_eq_abs, abs_of_nonneg (Gnn q u)]; exact Gle q u)
    have hG0 : G q0 =ᵐ[populationSeedLaw μ A] 0 :=
      (integral_eq_zero_iff_of_nonneg (Gnn q0) (Gi q0)).1 hzero0
    have hG1 : G q1 =ᵐ[populationSeedLaw μ A] 0 := by
      filter_upwards [hG0] with u hu0
      have hterms := (Finset.sum_eq_zero_iff_of_nonneg (fun w _ =>
        mul_nonneg ((cnn q0 u).1 w) (stopEvent_bound A n u w).1)).1 hu0
      apply Finset.sum_eq_zero
      intro w _
      by_cases hf : stopEvent A n u w = 0
      · rw [hf, mul_zero]
      · have hc0 : creationLaw (populationPolicy A u) (populationGap u) (populationPrior q0 u) w = 0 := by
          rcases mul_eq_zero.1 (hterms w (Finset.mem_univ w)) with h | h
          · exact h
          · exact absurd h hf
        have hc1 : creationLaw (populationPolicy A u) (populationGap u) (populationPrior q1 u) w = 0 := by
          by_contra hne
          exact support_compare (populationPolicy A u) (populationGap u)
            (fun i => ⟨(u.2 i).property.1, (u.2 i).property.2⟩) w hne hc0
        rw [hc1, zero_mul]
    have hint1 : (∫ z, stopEvent A n z.1 (processPrefix n z.2) ∂experimentLaw μ A q1) = 0 := by
      rw [real q1]
      exact (integral_congr_ae hG1).trans (by simp)
    have hjoint := stopEvent_joint A n
    have hi1 : Integrable (fun z : PopulationSeed R × ProcessTape =>
        stopEvent A n z.1 (processPrefix n z.2)) (experimentLaw μ A q1) :=
      (integrable_const (1:ℝ)).mono' hjoint.aestronglyMeasurable (ae_of_all _ fun z => by
        have hb := stopEvent_bound A n z.1 (processPrefix n z.2)
        rw [Real.norm_eq_abs, abs_of_nonneg hb.1]; exact hb.2)
    exact (integral_eq_zero_iff_of_nonneg
      (fun z : PopulationSeed R × ProcessTape => (stopEvent_bound A n z.1 (processPrefix n z.2)).1)
      hi1).1 hint1
  -- Hence the output vanishes under `q1` too.
  have h1 : ∀ᵐ z ∂experimentLaw μ A q1, populationOutput A z = 0 := by
    filter_upwards [ae_all_iff.2 hE, hstop q1, StoppingProgram.original_path_valid μ A q1]
      with z hz hs hv
    obtain ⟨n, hn⟩ := hs
    have hzn := hz n
    unfold stopEvent at hzn
    rw [ite_eq_right_iff] at hzn
    by_contra hne
    exact one_ne_zero (hzn ⟨hn, by rw [pad_prefix (A.policy z.1.1) z.2 hv n hn]; exact hne⟩)
  obtain ⟨-, he1⟩ := hu q1
  rw [integral_eq_zero_of_ae h1] at he1
  have hθ : signMean μ q1.val = μ.real {d : Gap | (d : ℝ) < 1/2} := by
    unfold signMean
    have hfun : (fun d : Gap => q1.val d) = Set.indicator {d : Gap | (d : ℝ) < 1/2} 1 := by
      funext d; simp [q1, Set.indicator_apply]
    rw [hfun, integral_indicator_one (measurableSet_lt measurable_subtype_coe measurable_const)]
  have hpos : 0 < μ.real {d : Gap | (d : ℝ) < 1/2} :=
    ENNReal.toReal_pos hμ.ne' (measure_ne_top _ _)
  linarith

end ThresholdHC.NonnegativeUnbiased
