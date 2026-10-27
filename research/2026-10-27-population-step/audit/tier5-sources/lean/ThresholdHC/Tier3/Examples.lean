import ThresholdHC.Tier3.ExamplesModel
import ThresholdHC.Proofs.Tier2.TranscriptLikelihood

/-!
A concrete infinite-horizon randomized experiment. A geometric seed fixes the
finite number of queries on each outcome, but no deterministic cap bounds the
work. The finite-prefix distributions are computed from the frozen transcript
law, and the geometric first moment supplies the expected-work condition.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal
namespace ThresholdHC.Tier3
open ThresholdHC.Proofs

instance exampleSeedLaw_probability : IsProbabilityMeasure exampleSeedLaw := by
  unfold exampleSeedLaw
  infer_instance

instance exampleProcessLaw_probability (q : unitInterval) : IsProbabilityMeasure (exampleProcessLaw q) := by
  unfold exampleProcessLaw
  infer_instance

def examplePrefix (N : ℕ) (b : Bool) (n : ℕ) : Fin n → Option Bool :=
  processPrefix n (exampleTape (N,b))

theorem examplePrefix_snoc (N n : ℕ) (b : Bool) :
    examplePrefix N b (n+1) = Fin.snoc (examplePrefix N b n) (if n < N+1 then some b else none) := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp [examplePrefix, processPrefix, exampleTape]
  · simp [examplePrefix, processPrefix, exampleTape]

theorem fullHist_snoc_example {n : ℕ} (w : Fin n → Option Bool) (o : Option Bool) :
    fullHist (Fin.snoc w o) = fullHist w ++ o.toList := by
  unfold fullHist
  rw [List.ofFn_succ']
  simp only [Fin.snoc_castSucc, Fin.snoc_last]
  cases o <;> simp [List.concat_eq_append]

theorem examplePrefix_hist_length (N n : ℕ) (b : Bool) :
    (fullHist (examplePrefix N b n)).length = min n (N+1) := by
  induction n with
  | zero => simp [examplePrefix, fullHist]
  | succ n ih =>
    rw [examplePrefix_snoc, fullHist_snoc_example, List.length_append, ih]
    by_cases hn : n < N+1
    · simp [hn]
      omega
    · simp [hn]
      omega

theorem examplePolicy_prefix (N n : ℕ) (b : Bool) :
    examplePolicy N (fullHist (examplePrefix N b n)) =
      if n < N+1 then some 0 else none := by
  unfold examplePolicy
  rw [examplePrefix_hist_length]
  by_cases hn : n < N+1 <;> simp [hn, show (min n (N+1) < N+1) ↔ n < N+1 by omega]

theorem example_path_expect (N n : ℕ) (b : Bool) (f : (Fin n → Option Bool) → ℝ) :
    (∑ w : Fin n → Option Bool, pathProb (examplePolicy N) (fun _ => if b then 1 else 0) w * f w) =
      f (examplePrefix N b n) := by
  induction n with
  | zero =>
    simp only [pathProb, Fin.prod_univ_zero, one_mul, Fintype.sum_unique]
    exact congrArg f (Subsingleton.elim _ _)
  | succ n ih =>
    rw [sum_snoc]
    simp_rw [pathProb_snoc, mul_assoc, ← Finset.mul_sum]
    rw [ih]
    rw [examplePrefix_snoc]
    by_cases hn : n < N+1 <;> cases b <;>
      simp [stepProb, examplePolicy_prefix, hn, Fintype.sum_option]

theorem example_transcript_expect (N n : ℕ) (q : ℝ) (f : (Fin n → Option Bool) → ℝ) :
    (∑ w : Fin n → Option Bool, transcriptLaw (examplePolicy N) (fun _ => 1/2)
      (fun _ => q) w * f w) =
      q * f (examplePrefix N true n) + (1-q) * f (examplePrefix N false n) := by
  classical
  unfold transcriptLaw
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  simp_rw [mul_assoc, ← Finset.mul_sum]
  rw [← (Equiv.funUnique (Fin 1) Bool).symm.sum_comp]
  simp only [Equiv.funUnique_symm_apply, uniqueElim_const, Fintype.sum_bool, Fin.prod_univ_one]
  norm_num only [Bool.false_eq_true, ↓reduceIte, add_neg_cancel, add_halves]
  have htrue := example_path_expect N n true f
  have hfalse := example_path_expect N n false f
  simp only [Bool.false_eq_true, ↓reduceIte] at htrue hfalse
  rw [htrue, hfalse]

theorem examplePrefix_work (N n : ℕ) (b : Bool) :
    workOf (examplePrefix N b n) = (min n (N+1) : ℕ) := by
  induction n with
  | zero => simp [workOf]
  | succ n ih =>
    rw [examplePrefix_snoc, workOf_snoc, ih]
    by_cases hn : n < N+1
    · simp only [hn, ↓reduceIte, Option.isSome_some]
      norm_cast
      omega
    · simp only [hn, ↓reduceIte, Option.isSome_none, Bool.false_eq_true]
      norm_cast
      omega

theorem example_totalWork (ω : ℕ × Bool) : totalProcessWork (exampleTape ω) = (ω.1+1 : ℕ) := by
  obtain ⟨N,b⟩ := ω
  unfold totalProcessWork
  change (⨆ n, ENNReal.ofReal (workOf (examplePrefix N b n))) = _
  simp_rw [examplePrefix_work, ENNReal.ofReal_natCast]
  apply le_antisymm
  · apply iSup_le
    intro n
    exact_mod_cast min_le_right n (N+1)
  · exact le_iSup_of_le (N+1) (by simp)

theorem example_policy_measurable : MeasurablePolicy examplePolicy := by
  intro history action
  exact (Set.to_countable _).measurableSet

theorem example_realizes (q : unitInterval) :
    RealizesPrefixes exampleSeedLaw (exampleProcessLaw q) Prod.fst exampleTape
      examplePolicy (fun _ => 1/2) (fun _ => (q : ℝ)) := by
  intro n f hfmeas hbound
  obtain ⟨C,hC⟩ := hbound
  have hi : Integrable (fun ω : ℕ × Bool => f ω.1 (processPrefix n (exampleTape ω)))
      (exampleProcessLaw q) := by
    apply (integrable_const C).mono' (measurable_of_countable _).aestronglyMeasurable
    exact ae_of_all _ (fun ω => by simpa only [Real.norm_eq_abs] using hC ω.1 _)
  unfold exampleProcessLaw at hi ⊢
  rw [integral_prod _ hi]
  apply integral_congr_ae
  filter_upwards [] with N
  rw [integral_bernoulliMeasure]
  simpa only [smul_eq_mul, examplePrefix] using (example_transcript_expect N n (q:ℝ) (f N)).symm

theorem example_seed_work_integrable : Integrable (fun N : ℕ => ((N+1 : ℕ) : ℝ)) exampleSeedLaw := by
  unfold exampleSeedLaw
  have hp : (⟨1/2, by constructor <;> norm_num⟩ : unitInterval) ≠ 0 := by
    intro he
    have := congrArg (fun p : unitInterval => (p:ℝ)) he
    norm_num at this
  apply (integrable_geometricMeasure_iff hp).2
  have hn : Summable (fun n : ℕ => (n:ℝ) * (1/2:ℝ)^n) := by
    simpa using summable_pow_mul_geometric_of_norm_lt_one 1 (by norm_num : ‖(1/2:ℝ)‖ < 1)
  have hg : Summable (fun n : ℕ => (1/2:ℝ)^n) := summable_geometric_of_norm_lt_one (by norm_num)
  have hs := (hn.add hg).mul_right (1/2:ℝ)
  apply hs.congr
  intro n
  norm_num [Real.norm_of_nonneg (show (0:ℝ) ≤ (n+1:ℕ) by positivity), Nat.cast_add, Nat.cast_one]
  rw [abs_of_nonneg (by positivity : (0:ℝ) ≤ (n:ℝ) + 1)]
  ring

theorem example_finite_expected_work (q : unitInterval) :
    (∫⁻ ω, totalProcessWork (exampleTape ω) ∂exampleProcessLaw q) < ∞ := by
  have hi : Integrable (fun ω : ℕ × Bool => ((ω.1+1:ℕ):ℝ)) (exampleProcessLaw q) :=
    example_seed_work_integrable.comp_fst _
  have hn : (0:ℕ × Bool → ℝ) ≤ᵐ[exampleProcessLaw q] (fun ω => ((ω.1+1:ℕ):ℝ)) :=
    ae_of_all _ (fun _ => by positivity)
  have hf := (hasFiniteIntegral_iff_ofReal hn).1 hi.2
  simpa only [example_totalWork, ENNReal.ofReal_natCast] using hf

theorem example_unbounded_work (q : unitInterval) (n : ℕ) :
    0 < exampleProcessLaw q {ω | (n:ℝ≥0∞) < totalProcessWork (exampleTape ω)} := by
  have hs : ({n} : Set ℕ) ×ˢ (Set.univ : Set Bool) ⊆
      {ω | (n:ℝ≥0∞) < totalProcessWork (exampleTape ω)} := by
    intro ω hω
    have hN : ω.1 = n := hω.1
    simp only [Set.mem_ofPred_eq, example_totalWork, hN]
    exact_mod_cast Nat.lt_succ_self n
  have hp : (⟨1/2, by constructor <;> norm_num⟩ : unitInterval) ≠ 0 := by
    intro he
    have := congrArg (fun p : unitInterval => (p:ℝ)) he
    norm_num at this
  have hpos : 0 < exampleProcessLaw q (({n} : Set ℕ) ×ˢ (Set.univ : Set Bool)) := by
    rw [exampleProcessLaw, Measure.prod_prod]
    simp only [measure_univ, mul_one]
    rw [exampleSeedLaw, geometricMeasure_singleton hp]
    apply ENNReal.ofReal_pos.mpr
    norm_num
  exact hpos.trans_le (measure_mono hs)

theorem unbounded_example : UnboundedExampleStatement := by
  refine ⟨example_policy_measurable, ?_⟩
  intro q
  exact ⟨example_realizes q, example_totalWork, example_finite_expected_work q,
    example_unbounded_work q⟩

end ThresholdHC.Tier3
