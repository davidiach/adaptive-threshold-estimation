import ThresholdHC.ReservoirTermination.Realized
import ThresholdHC.Tier6.Full

/-!
The paper's instances, the refutation of the naive countable-reservoir bridge, an
explicit realized counterexample, and the same counterexample in the original Tier 6
experiment. Realizations come from the canonical Ionescu-Tulcea process
`Tier6.creationProcessLaw`, and in Tier 6 from `population_realization` after the
point-mass seed law collapses.
-/

noncomputable section
open MeasureTheory Filter
open scoped ENNReal Topology
namespace ThresholdHC.ReservoirTermination
open ThresholdHC ThresholdHC.Tier3 ThresholdHC.Tier5 ThresholdHC.Tier6 ThresholdHC.Proofs

theorem walk_first_passage_holds : WalkFirstPassageStatement := by
  intro Seed Ω _ _ μ ν _ _ seed tape d η htape hd0 hd1 hη0 hη1
  have h := walk_first_passage_of_sums ν tape htape d η hd0 hd1 hη0 hη1
  exact ⟨fun hr => h.1 (realized_prefix_sum μ ν seed tape d _ hr),
    fun hr => h.2 (realized_prefix_sum μ ν seed tape d _ hr)⟩

theorem ofReal_two_fifths : ENNReal.ofReal (2/5) = 2/5 := by
  rw [ENNReal.ofReal_div_of_pos (by norm_num)]
  simp

theorem ofReal_three_fifths : ENNReal.ofReal (3/5) = 3/5 := by
  rw [ENNReal.ofReal_div_of_pos (by norm_num)]
  simp

theorem ofReal_two_ninths : ENNReal.ofReal (2/9) = 2/9 := by
  rw [ENNReal.ofReal_div_of_pos (by norm_num)]
  simp

theorem half_gap_example : HalfGapExampleStatement := by
  constructor
  · intro Seed Ω _ _ μ P _ _ seed tape htape hr
    have h := (walk_first_passage_holds Seed Ω μ P seed tape (1/2) (1/8) htape
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)).1
      (by rw [show (1/2 + 1/8 : ℝ) = 5/8 by norm_num]; exact hr)
    refine ⟨h.1, ?_⟩
    rw [h.2, show (1 / (4 * (1/2) * (1/8)) : ℝ) = 4 by norm_num, ENNReal.ofReal_ofNat]
  · intro Seed Ω _ _ μ Q _ _ seed tape htape hr
    have h := (walk_first_passage_holds Seed Ω μ Q seed tape (1/2) (1/8) htape
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)).2
      (by rw [show (1/2 - 1/8 : ℝ) = 3/8 by norm_num]; exact hr)
    rw [h.1, show (8 * (1/2) * (1/8) / (1 + 4 * (1/2) * (1/8)) : ℝ) = 2/5 by norm_num,
      ofReal_two_fifths]

theorem quarter_gap_example : QuarterGapExampleStatement := by
  constructor
  · intro Seed Ω _ _ μ P _ _ seed tape htape hr
    have h := (walk_first_passage_holds Seed Ω μ P seed tape (1/4) (1/8) htape
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)).1
      (by rw [show (1/2 + 1/8 : ℝ) = 5/8 by norm_num]; exact hr)
    refine ⟨h.1, ?_⟩
    rw [h.2, show (1 / (4 * (1/4) * (1/8)) : ℝ) = 8 by norm_num, ENNReal.ofReal_ofNat]
  · intro Seed Ω _ _ μ Q _ _ seed tape htape hr
    have h := (walk_first_passage_holds Seed Ω μ Q seed tape (1/4) (1/8) htape
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)).2
      (by rw [show (1/2 - 1/8 : ℝ) = 3/8 by norm_num]; exact hr)
    rw [h.1, show (8 * (1/4) * (1/8) / (1 + 4 * (1/4) * (1/8)) : ℝ) = 2/9 by norm_num,
      ofReal_two_ninths]

/-- The canonical process of the walk policy with a trivial seed. -/
theorem walk_process_exists (d q : ℝ) (hd : 0 ≤ d ∧ d ≤ 1/2) (hq : 0 ≤ q ∧ q ≤ 1) :
    ∃ P : Measure (Unit × ProcessTape), IsProbabilityMeasure P ∧
      RealizesCreationPrefixes (Measure.dirac ()) P Prod.fst Prod.snd (fun _ => walkPolicy)
        (fun _ _ => d) (fun _ _ => q) :=
  ⟨creationProcessLaw (Measure.dirac ()) (fun _ => walkPolicy) (fun _ _ => d) (fun _ _ => q)
      walkEstimator.policy_measurable (fun _ => measurable_const) (fun _ => measurable_const)
      (fun _ _ => hd) (fun _ _ => hq),
    creationProcessLaw_probability (Measure.dirac ()) _ _ _ _ _ _ _ _,
    creationProcessLaw_realizes (Measure.dirac ()) (fun _ => walkPolicy) (fun _ _ => d)
      (fun _ _ => q) walkEstimator.policy_measurable (fun _ => measurable_const)
      (fun _ => measurable_const) (fun _ _ => hd) (fun _ _ => hq)⟩

theorem measurableSet_tape_snd (n : ℕ) (b : Option Bool) :
    MeasurableSet {ω : Unit × ProcessTape | ω.2 n = b} :=
  measurableSet_eq_fun ((measurable_pi_apply n).comp measurable_snd) measurable_const

theorem measurableSet_runsForever {Ω : Type} [MeasurableSpace Ω] (tape : Ω → ProcessTape)
    (htape : ∀ n b, MeasurableSet {ω | tape ω n = b}) : MeasurableSet (RunsForever tape) := by
  have h : RunsForever tape =
      ⋂ n, {ω | processPrefix n (tape ω) ∈ {w : Prefix n | walkPolicy (fullHist w) ≠ none}} := by
    ext ω
    simp only [RunsForever, Set.mem_iInter, Set.mem_ofPred_eq]
    rfl
  rw [h]
  exact MeasurableSet.iInter (fun n => measurableSet_prefix_mem tape htape n _)

theorem naive_bridge_fails_proof : NaiveBridgeFailsStatement := by
  intro H
  obtain ⟨P, hPp, hrP⟩ := walk_process_exists (1/2) (1/2 + 1/8) (by norm_num) (by norm_num)
  obtain ⟨Q, hQp, hrQ⟩ := walk_process_exists (1/2) (1/2 - 1/8) (by norm_num) (by norm_num)
  have hP := (walk_first_passage_holds Unit (Unit × ProcessTape) (Measure.dirac ()) P
    Prod.fst Prod.snd (1/2) (1/8) measurableSet_tape_snd
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)).1 hrP
  have hQ := (walk_first_passage_holds Unit (Unit × ProcessTape) (Measure.dirac ()) Q
    Prod.fst Prod.snd (1/2) (1/8) measurableSet_tape_snd
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)).2 hrQ
  have hfinP : (∫⁻ ω, totalProcessWork ω.2 ∂P) < ∞ := by
    rw [hP.2]
    exact ENNReal.ofReal_lt_top
  have hstop := (H Unit (Unit × ProcessTape) (Measure.dirac ()) P Q Prod.fst Prod.snd
    (fun _ => walkPolicy) (fun _ => 1/2) (fun _ => 1/8) measurable_fst measurableSet_tape_snd
    walkEstimator.policy_measurable hrP hrQ (fun _ => by norm_num) (fun _ => by norm_num)
    hfinP).2
  rw [ae_iff] at hstop
  have hset : {ω : Unit × ProcessTape | ¬ ∃ n, walkPolicy (processHistory ω.2 n) = none} =
      RunsForever Prod.snd := by
    ext ω
    simp [RunsForever]
  rw [hset, hQ.1, ENNReal.ofReal_eq_zero] at hstop
  norm_num at hstop

theorem reservoir_counterexample_proof : ReservoirCounterexampleStatement := by
  obtain ⟨P, hPp, hrP⟩ := walk_process_exists (1/2) (5/8) (by norm_num) (by norm_num)
  obtain ⟨Q, hQp, hrQ⟩ := walk_process_exists (1/2) (3/8) (by norm_num) (by norm_num)
  have hP := half_gap_example.1 Unit (Unit × ProcessTape) (Measure.dirac ()) P Prod.fst Prod.snd
    measurableSet_tape_snd hrP
  have hQ := half_gap_example.2 Unit (Unit × ProcessTape) (Measure.dirac ()) Q Prod.fst Prod.snd
    measurableSet_tape_snd hrQ
  have hQw := (walk_first_passage_holds Unit (Unit × ProcessTape) (Measure.dirac ()) Q
    Prod.fst Prod.snd (1/2) (1/8) measurableSet_tape_snd
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)).2
    (by rw [show (1/2 - 1/8 : ℝ) = 3/8 by norm_num]; exact hrQ)
  have hcompl : Q (RunsForever (Prod.snd : Unit × ProcessTape → ProcessTape))ᶜ = 3/5 := by
    rw [prob_compl_eq_one_sub (measurableSet_runsForever _ measurableSet_tape_snd), hQ,
      ← ofReal_two_fifths, ← ofReal_three_fifths, ← ENNReal.ofReal_one,
      ← ENNReal.ofReal_sub _ (by norm_num)]
    norm_num
  exact ⟨Unit × ProcessTape, inferInstance, P, Q, Prod.snd, hPp, hQp, measurableSet_tape_snd,
    hrP, hrQ, hP.1, hP.2, hcompl, hQ, hQw.2⟩

/-- Point-mass gap law: the Tier 6 experiment computes prefix expectations by the
creation-model sums of the walk policy. -/
theorem experiment_prefix_sum (g : Gap) (p : ℝ) (hp : 0 ≤ p ∧ p ≤ 1) (n : ℕ)
    (F : Prefix n → ℝ) :
    (∫ z, F (processPrefix n z.2)
        ∂experimentLaw (Measure.dirac g) walkEstimator (constantSignLaw p hp)) =
      ∑ w, creationLaw walkPolicy (fun _ => (g : ℝ)) (fun _ => p) w * F w := by
  have hC : ∀ w, |F w| ≤ ∑ v, |F v| := fun w =>
    Finset.single_le_sum (f := fun v => |F v|) (fun v _ => abs_nonneg _) (Finset.mem_univ w)
  have hr := (population_realization Unit (Measure.dirac g) walkEstimator
    (constantSignLaw p hp)).2 n (fun _ => F) (fun _ => measurable_const) ⟨_, fun _ w => hC w⟩
  have hseed : populationSeedLaw (Measure.dirac g) walkEstimator =
      Measure.dirac ((), fun _ => g) := by
    simp [populationSeedLaw, walkEstimator, Measure.infinitePi_dirac, Measure.dirac_prod_dirac]
  rw [hseed, integral_dirac] at hr
  exact hr

theorem experiment_tape (n : ℕ) (b : Option Bool) :
    MeasurableSet {z : PopulationSeed Unit × ProcessTape | z.2 n = b} :=
  measurableSet_eq_fun ((measurable_pi_apply n).comp measurable_snd) measurable_const

/-- The walk in the Tier 6 experiment at a point-mass gap law. -/
theorem experiment_first_passage (g : Gap) (η p m : ℝ) (hp : 0 ≤ p ∧ p ≤ 1)
    (hm : 0 ≤ m ∧ m ≤ 1) (hpη : p = 1/2 + η) (hmη : m = 1/2 - η) (hη0 : 0 < η)
    (hη1 : η < 1/2) :
    expectedWork (Measure.dirac g) walkEstimator (constantSignLaw p hp) =
      ENNReal.ofReal (1 / (4 * g * η)) ∧
    experimentLaw (Measure.dirac g) walkEstimator (constantSignLaw m hm)
      (RunsForever (Ω := PopulationSeed Unit × ProcessTape) Prod.snd) =
      ENNReal.ofReal (8 * g * η / (1 + 4 * g * η)) ∧
    expectedWork (Measure.dirac g) walkEstimator (constantSignLaw m hm) = ∞ := by
  subst hpη hmη
  have h := walk_first_passage_of_sums
    (experimentLaw (Measure.dirac g) walkEstimator (constantSignLaw (1/2 + η) hp))
    Prod.snd experiment_tape (g : ℝ) η g.property.1 g.property.2 hη0 hη1
  have h' := walk_first_passage_of_sums
    (experimentLaw (Measure.dirac g) walkEstimator (constantSignLaw (1/2 - η) hm))
    Prod.snd experiment_tape (g : ℝ) η g.property.1 g.property.2 hη0 hη1
  have hplus := h.1 (experiment_prefix_sum g _ hp)
  have hminus := h'.2 (experiment_prefix_sum g _ hm)
  exact ⟨hplus.2, hminus.1, hminus.2⟩

theorem original_experiment_proof : OriginalExperimentStatement := by
  have hhalf := experiment_first_passage halfGap (1/8) (5/8) (3/8) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hquarter := experiment_first_passage quarterGap (1/8) (5/8) (3/8) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have vh : ((halfGap : Gap) : ℝ) = 1/2 := rfl
  have vq : ((quarterGap : Gap) : ℝ) = 1/4 := rfl
  rw [vh] at hhalf
  rw [vq] at hquarter
  have hinf := hhalf.2.2
  refine ⟨?_, ?_, hinf, ?_, ?_, ?_⟩
  · rw [hhalf.1, show (1 / (4 * (1/2) * (1/8)) : ℝ) = 4 by norm_num, ENNReal.ofReal_ofNat]
  · rw [hhalf.2.1, show (8 * (1/2) * (1/8) / (1 + 4 * (1/2) * (1/8)) : ℝ) = 2/5 by norm_num,
      ofReal_two_fifths]
  · rw [hquarter.1, show (1 / (4 * (1/4) * (1/8)) : ℝ) = 8 by norm_num, ENNReal.ofReal_ofNat]
  · rw [hquarter.2.1, show (8 * (1/4) * (1/8) / (1 + 4 * (1/4) * (1/8)) : ℝ) = 2/9 by norm_num,
      ofReal_two_ninths]
  · intro B hB
    have h := hB (constantSignLaw (3/8) (by norm_num))
    rw [hinf, top_le_iff] at h
    exact ENNReal.ofReal_ne_top h

end ThresholdHC.ReservoirTermination
