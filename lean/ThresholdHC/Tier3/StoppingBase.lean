import ThresholdHC.Tier3.StoppingModel
import ThresholdHC.Proofs.Tier2.Transcript
import ThresholdHC.Tier3.RandomizedBase
import ThresholdHC.Tier3.TranscriptRatio

noncomputable section
open MeasureTheory Filter
open scoped ENNReal Topology
namespace ThresholdHC.Tier3

local instance optionMeasurableSpace (α : Type) : MeasurableSpace (Option α) := ⊤

theorem workOf_nonneg {n : ℕ} (w : Fin n → Option Bool) : 0 ≤ workOf w := by
  unfold workOf
  positivity

theorem workOf_le_length {n : ℕ} (w : Fin n → Option Bool) : workOf w ≤ n := by
  unfold workOf
  have h : (Finset.univ.filter (fun t => (w t).isSome = true)).card ≤ n := by simpa using (Finset.card_filter_le (s := Finset.univ) (fun t => (w t).isSome = true))
  exact_mod_cast h

theorem finiteHistory_processPrefix (n : ℕ) (x : ProcessTape) (k : Fin (n+1)) :
    finiteHistory (processPrefix n x) k = processHistory x k := rfl

theorem measurable_processPrefix {Ω : Type} [MeasurableSpace Ω] (tape : Ω → ProcessTape)
    (htape : ∀ n b, MeasurableSet {ω | tape ω n = b}) (n : ℕ) :
    Measurable (fun ω => processPrefix n (tape ω)) := by
  apply Measurable.of_eval
  intro i
  exact measurable_to_countable' (htape i)

theorem measurable_prefix_function {Seed Ω : Type} [MeasurableSpace Seed] [MeasurableSpace Ω]
    (seed : Ω → Seed) (tape : Ω → ProcessTape) (hs : Measurable seed)
    (htape : ∀ n b, MeasurableSet {ω | tape ω n = b}) (n : ℕ)
    {β : Type} [MeasurableSpace β] (f : Seed → (Fin n → Option Bool) → β)
    (hf : ∀ w, Measurable (fun u => f u w)) :
    Measurable (fun ω => f (seed ω) (processPrefix n (tape ω))) := by
  exact (measurable_from_prod_countable_left (f := fun p : Seed × (Fin n → Option Bool) => f p.1 p.2) hf).comp
    (hs.prodMk (measurable_processPrefix tape htape n))

theorem measurable_totalProcessWork {Ω : Type} [MeasurableSpace Ω] (tape : Ω → ProcessTape)
    (htape : ∀ n b, MeasurableSet {ω | tape ω n = b}) :
    Measurable (fun ω => totalProcessWork (tape ω)) := by
  apply Measurable.iSup
  intro n
  exact ((measurable_of_countable _ : Measurable (@workOf n)).comp
    (measurable_processPrefix tape htape n)).ennreal_ofReal

theorem prefix_work_le_total {Ω : Type} [MeasurableSpace Ω] (ν : Measure Ω)
    (tape : Ω → ProcessTape) (htape : ∀ n b, MeasurableSet {ω | tape ω n = b})
    (hfin : (∫⁻ ω, totalProcessWork (tape ω) ∂ν) < ∞) (n : ℕ) :
    (∫ ω, workOf (processPrefix n (tape ω)) ∂ν) ≤
      (∫⁻ ω, totalProcessWork (tape ω) ∂ν).toReal := by
  rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall
    (fun ω => workOf_nonneg _))
    (((measurable_of_countable _ : Measurable (@workOf n)).comp
      (measurable_processPrefix tape htape n)).aestronglyMeasurable)]
  apply ENNReal.toReal_mono hfin.ne
  exact lintegral_mono (fun ω => le_iSup (fun k => ENNReal.ofReal (workOf (processPrefix k (tape ω)))) n)

theorem pathProb_zero_of_invalid {m n : ℕ} (pol : List Bool → Option (Fin m))
    (p : Fin m → ℝ) (w : Fin n → Option Bool) (t : Fin n)
    (h : (w t).isSome ≠ (pol (histBefore w t)).isSome) : pathProb pol p w = 0 := by
  unfold pathProb
  apply Finset.prod_eq_zero (Finset.mem_univ t)
  cases hp : pol (histBefore w t) with
  | none => cases hw : w t <;> simp_all
  | some i => cases hw : w t <;> simp_all

theorem transcriptLaw_zero_of_invalid {m n : ℕ} (pol : List Bool → Option (Fin m))
    (d q : Fin m → ℝ) (w : Fin n → Option Bool) (t : Fin n)
    (h : (w t).isSome ≠ (pol (histBefore w t)).isSome) : transcriptLaw pol d q w = 0 := by
  unfold transcriptLaw
  apply Finset.sum_eq_zero
  intro s hs
  rw [pathProb_zero_of_invalid pol _ w t h, mul_zero]

theorem histBefore_processPrefix_last (n : ℕ) (x : ProcessTape) :
    histBefore (processPrefix (n+1) x) (Fin.last n) = processHistory x n := rfl

theorem measurable_policy {Seed : Type} [MeasurableSpace Seed] {m : ℕ}
    (pol : Seed → List Bool → Option (Fin m)) (hp : MeasurablePolicy pol) (xs : List Bool) :
    Measurable (fun u => pol u xs) := measurable_to_countable' (hp xs)

theorem realized_valid_step {Seed Ω : Type} [MeasurableSpace Seed] [MeasurableSpace Ω]
    (μ : Measure Seed) (ν : Measure Ω) [IsProbabilityMeasure ν] {m : ℕ}
    (seed : Ω → Seed) (tape : Ω → ProcessTape) (pol : Seed → List Bool → Option (Fin m))
    (d q : Fin m → ℝ) (hs : Measurable seed)
    (htape : ∀ n b, MeasurableSet {ω | tape ω n = b}) (hp : MeasurablePolicy pol)
    (hr : RealizesPrefixes μ ν seed tape pol d q) (n : ℕ) :
    ∀ᵐ ω ∂ν, (tape ω n).isSome = (pol (seed ω) (processHistory (tape ω) n)).isSome := by
  classical
  let f : Seed → (Fin (n+1) → Option Bool) → ℝ := fun u w =>
    if (w (Fin.last n)).isSome = (pol u (histBefore w (Fin.last n))).isSome then 0 else 1
  have hf : ∀ w, Measurable (fun u => f u w) := by
    intro w
    have hm := (measurable_of_countable _ : Measurable (@Option.isSome (Fin m))).comp
      (measurable_policy pol hp (histBefore w (Fin.last n)))
    exact measurable_const.ite (measurableSet_eq_fun measurable_const hm) measurable_const
  have hbound : ∃ C : ℝ, ∀ u w, |f u w| ≤ C := by
    refine ⟨1, ?_⟩
    intro u w
    dsimp [f]
    split_ifs <;> norm_num
  have hz : ∀ u, (∑ w, transcriptLaw (pol u) d q w * f u w) = 0 := by
    intro u
    apply Finset.sum_eq_zero
    intro w hw
    dsimp [f]
    split_ifs with h
    · simp
    · rw [transcriptLaw_zero_of_invalid (pol u) d q w (Fin.last n) h, zero_mul]
  have heq := hr (n+1) f hf hbound
  simp_rw [hz] at heq
  simp only [integral_zero] at heq
  let bad : Set Ω := {ω | (tape ω n).isSome ≠ (pol (seed ω) (processHistory (tape ω) n)).isSome}
  have hm : MeasurableSet bad := by
    have ha := (measurable_of_countable _ : Measurable (@Option.isSome Bool)).comp
      (measurable_to_countable' (htape n))
    have hb := (measurable_of_countable _ : Measurable (@Option.isSome (Fin m))).comp
      (measurable_prefix_function seed tape hs htape n
        (fun u w => pol u (Proofs.fullHist w))
        (fun w => measurable_policy pol hp (Proofs.fullHist w)))
    exact (measurableSet_eq_fun ha hb).compl
  have heq' : ν.real bad = 0 := by
    have hfun : (fun ω => f (seed ω) (processPrefix (n+1) (tape ω))) =
        bad.indicator (fun _ => (1:ℝ)) := by
      funext ω
      simp only [f, processPrefix, Fin.val_last, histBefore_processPrefix_last,
        Set.indicator, bad, Set.mem_ofPred_eq]
      split_ifs <;> simp_all
    rw [hfun, integral_indicator_const 1 hm] at heq
    simpa using heq
  exact (ae_iff).2 ((measureReal_eq_zero_iff).mp heq')

theorem finite_work_stops : FiniteWorkStopsStatement := by
  intro Seed Ω _ _ μ ν _ _ m seed tape pol d q hs htape hp hr hfin
  have hv : ∀ᵐ ω ∂ν, ∀ n, (tape ω n).isSome =
      (pol (seed ω) (processHistory (tape ω) n)).isSome :=
    ae_all_iff.2 (fun n => realized_valid_step μ ν seed tape pol d q hs htape hp hr n)
  have hfinite := ae_lt_top (measurable_totalProcessWork tape htape) hfin.ne
  filter_upwards [hv, hfinite] with ω hvalid hwork
  by_contra hn
  push Not at hn
  have hsome (n : ℕ) : (tape ω n).isSome = true := by
    rw [hvalid n]
    exact Option.isSome_iff_ne_none.mpr (hn n)
  have hcount (n : ℕ) : workOf (processPrefix n (tape ω)) = n := by
    simp [workOf, processPrefix, hsome]
  obtain ⟨n, hnlarge⟩ := exists_nat_gt (totalProcessWork (tape ω)).toReal
  have hle : ENNReal.ofReal (n : ℝ) ≤ totalProcessWork (tape ω) := by
    rw [← hcount n]
    exact le_iSup (fun k => ENNReal.ofReal (workOf (processPrefix k (tape ω)))) n
  have := ENNReal.toReal_mono hwork.ne hle
  simpa using (not_le.mpr hnlarge) (by simpa using this)

theorem processPrefix_snoc (n : ℕ) (x : ProcessTape) :
    processPrefix (n+1) x = Fin.snoc (processPrefix n x) (x n) := by
  ext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp [processPrefix]
  · simp [processPrefix]

theorem process_work_mono (x : ProcessTape) : Monotone (fun n => workOf (processPrefix n x)) := by
  apply monotone_nat_of_le_succ
  intro n
  rw [processPrefix_snoc, Proofs.workOf_snoc]
  split_ifs <;> linarith

theorem integrable_prefix_work {Ω : Type} [MeasurableSpace Ω] (ν : Measure Ω)
    [IsFiniteMeasure ν] (tape : Ω → ProcessTape)
    (htape : ∀ n b, MeasurableSet {ω | tape ω n = b}) (n : ℕ) :
    Integrable (fun ω => workOf (processPrefix n (tape ω))) ν := by
  apply (integrable_const (n:ℝ)).mono'
    (((measurable_of_countable _ : Measurable (@workOf n)).comp
      (measurable_processPrefix tape htape n)).aestronglyMeasurable)
  exact Filter.Eventually.of_forall (fun ω => by
    simp only [Function.comp_apply, Real.norm_eq_abs]
    rw [abs_of_nonneg (workOf_nonneg _)]
    exact workOf_le_length _)

theorem integral_total_work_eq_iSup {Ω : Type} [MeasurableSpace Ω] (ν : Measure Ω)
    [IsFiniteMeasure ν] (tape : Ω → ProcessTape)
    (htape : ∀ n b, MeasurableSet {ω | tape ω n = b}) :
    (∫⁻ ω, totalProcessWork (tape ω) ∂ν) =
      ⨆ n : ℕ, ENNReal.ofReal (∫ ω, workOf (processPrefix n (tape ω)) ∂ν) := by
  have hm : ∀ n, Measurable (fun ω => ENNReal.ofReal (workOf (processPrefix n (tape ω)))) := by
    intro n
    exact ((measurable_of_countable _ : Measurable (@workOf n)).comp
      (measurable_processPrefix tape htape n)).ennreal_ofReal
  have hmono : Monotone (fun n ω => ENNReal.ofReal (workOf (processPrefix n (tape ω)))) := by
    intro i j hij ω
    exact ENNReal.ofReal_le_ofReal (process_work_mono (tape ω) hij)
  unfold totalProcessWork
  rw [lintegral_iSup hm hmono]
  congr 1
  funext n
  exact (ofReal_integral_eq_lintegral_ofReal (integrable_prefix_work ν tape htape n)
    (Filter.Eventually.of_forall (fun ω => workOf_nonneg _))).symm

theorem realized_prefix_work_eq {Seed Ω : Type} [MeasurableSpace Seed] [MeasurableSpace Ω]
    (μ : Measure Seed) (ν : Measure Ω) {m : ℕ}
    (seed : Ω → Seed) (tape : Ω → ProcessTape) (pol : Seed → List Bool → Option (Fin m))
    (d q : Fin m → ℝ) (hr : RealizesPrefixes μ ν seed tape pol d q) (n : ℕ) :
    (∫ ω, workOf (processPrefix n (tape ω)) ∂ν) = randomizedWork μ pol d q n := by
  apply hr n (fun _ w => workOf w) (fun _ => measurable_const)
  refine ⟨n, fun _ w => ?_⟩
  rw [abs_of_nonneg (workOf_nonneg w)]
  exact workOf_le_length w

theorem randomized_work_prior_comparison {Seed : Type} [MeasurableSpace Seed]
    (μ : Measure Seed) [IsFiniteMeasure μ] {m : ℕ}
    (pol : Seed → List Bool → Option (Fin m)) (hp : MeasurablePolicy pol)
    (d η : Fin m → ℝ) (hd : ∀ i, 0 ≤ d i ∧ d i ≤ 1/2)
    (hη : ∀ i, 0 ≤ η i ∧ η i ≤ 1/8) (n : ℕ) :
    randomizedWork μ pol d (fun i => 1/2-η i) n ≤
      (5/3:ℝ)^m * randomizedWork μ pol d (fun i => 1/2+η i) n := by
  unfold randomizedWork
  rw [← integral_const_mul]
  apply integral_mono (integrable_conditional_work μ pol hp d _)
    ((integrable_conditional_work μ pol hp d _).const_mul _)
  intro u
  dsimp only
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro w hw
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_right
    (transcriptLaw_minus_le_plus (pol u) d η hd hη w) (workOf_nonneg w)

theorem unbounded_stopping : UnboundedStoppingStatement := by
  intro Seed Ω _ _ μ P Q _ _ _ m seed tape pol d η hs htape hp hrP hrQ hd hη hfin
  constructor
  · exact finite_work_stops Seed Ω μ P m seed tape pol d _ hs htape hp hrP hfin
  · apply finite_work_stops Seed Ω μ Q m seed tape pol d _ hs htape hp hrQ
    apply lt_of_le_of_lt (b := ENNReal.ofReal
      ((5/3:ℝ)^m * (∫⁻ ω, totalProcessWork (tape ω) ∂P).toReal)) _ ENNReal.ofReal_lt_top
    rw [integral_total_work_eq_iSup Q tape htape]
    apply iSup_le
    intro n
    apply ENNReal.ofReal_le_ofReal
    rw [realized_prefix_work_eq μ Q seed tape pol d _ hrQ]
    apply (randomized_work_prior_comparison μ pol hp d η
      (fun i => ⟨(hd i).1.le, (hd i).2⟩) hη n).trans
    rw [← realized_prefix_work_eq μ P seed tape pol d _ hrP]
    exact mul_le_mul_of_nonneg_left (prefix_work_le_total P tape htape hfin n) (by positivity)

end ThresholdHC.Tier3
