import ThresholdHC.UnbiasedConverse.CreationInformation
import ThresholdHC.Tier6.Full

/-! The stopped-creation KL chain rule with a prior-ratio hypothesis.

`UnbiasedConverse.creation_finite_information` assumes priors in `[3/8,5/8]` at
every coin. A coin prior near zero cannot meet that range, so this copy replaces
it by strict bounds `0 < q, v < 1` and a two-sided prior-ratio bound with a
constant `K ≥ 1`. The proof is otherwise the same: the finite prefix laws are
mutually bounded by `K^n`, the per-seed transcript divergence is charged `C` per
actual flip, and stopping identifies the full divergence as the supremum of the
prefix divergences. The population form charges only the work of the first law. -/
noncomputable section
open MeasureTheory InformationTheory Filter
open scoped ENNReal
namespace ThresholdHC.LocalizationCounter
open ThresholdHC ThresholdHC.Proofs.Transcript
open ThresholdHC.Tier3 ThresholdHC.Tier4 ThresholdHC.Tier5 ThresholdHC.Tier6
  ThresholdHC.UnbiasedConverse

theorem ratio_creation_finite_information
    (Seed Ω : Type) [MeasurableSpace Seed] [MeasurableSpace Ω]
    (μ : Measure Seed) (P Q : Measure Ω)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (n : ℕ) (seed : Ω → Seed) (tape : Ω → ProcessTape)
    (pol : Seed → List Bool → Option ℕ) (d q v : Seed → ℕ → ℝ) (C K : ℝ)
    (hs : Measurable seed) (ht : ∀ n b, MeasurableSet {ω | tape ω n = b})
    (hp : MeasurableCreationPolicy pol) (hdm : MeasurableEnvironment d)
    (hqm : MeasurableEnvironment q) (hvm : MeasurableEnvironment v)
    (hP : RealizesCreationPrefixes μ P seed tape pol d q)
    (hQ : RealizesCreationPrefixes μ Q seed tape pol d v)
    (hd : ∀ u i, 0 < d u i ∧ d u i ≤ 1/2)
    (hq : ∀ u i, 0 < q u i ∧ q u i < 1)
    (hv : ∀ u i, 0 < v u i ∧ v u i < 1)
    (hK : 1 ≤ K)
    (hvq : ∀ u i, v u i ≤ K * q u i) (hvq' : ∀ u i, 1 - v u i ≤ K * (1 - q u i))
    (hqv : ∀ u i, q u i ≤ K * v u i) (hqv' : ∀ u i, 1 - q u i ≤ K * (1 - v u i))
    (hstep : ∀ u i A B, 0 ≤ A → 0 ≤ B → 0 < A+B →
      klB (mixPredict (d u i) (q u i) A B) (mixPredict (d u i) (v u i) A B) ≤ C) :
    klDiv (prefixTranscriptLaw P seed tape n) (prefixTranscriptLaw Q seed tape n) ≤
      ENNReal.ofReal (C * ∫ ω, workOf (processPrefix n (tape ω)) ∂P) := by
  let p : Seed → Prefix n → ℝ := fun u w => creationLaw (pol u) (d u) (q u) w
  let r : Seed → Prefix n → ℝ := fun u w => creationLaw (pol u) (d u) (v u) w
  have hpm w : Measurable (fun u => p u w) := measurable_creationLaw pol hp d q hdm hqm w
  have hrm w : Measurable (fun u => r u w) := measurable_creationLaw pol hp d v hdm hvm w
  have hpt u : (∀ w, 0 ≤ p u w) ∧ ∑ w, p u w = 1 := by
    apply creationLaw_total n (pol u) (d u) (q u) (fun i => ⟨(hd u i).1.le,(hd u i).2⟩)
    intro i; exact ⟨(hq u i).1.le, (hq u i).2.le⟩
  have hrt u : (∀ w, 0 ≤ r u w) ∧ ∑ w, r u w = 1 := by
    apply creationLaw_total n (pol u) (d u) (v u) (fun i => ⟨(hd u i).1.le,(hd u i).2⟩)
    intro i; exact ⟨(hv u i).1.le, (hv u i).2.le⟩
  have hp1 u w : p u w ≤ 1 := by
    rw [← (hpt u).2]
    exact Finset.single_le_sum (fun a ha => (hpt u).1 a) (Finset.mem_univ w)
  have ratio (u : Seed) (w : Prefix n) (a b : ℕ → ℝ)
      (ha : ∀ i, 0 < a i ∧ a i < 1) (hb : ∀ i, 0 < b i ∧ b i < 1)
      (hab : ∀ i, a i ≤ K * b i) (hab' : ∀ i, 1 - a i ≤ K * (1 - b i)) :
      creationLaw (pol u) (d u) a w ≤ K^n * creationLaw (pol u) (d u) b w := by
    apply finite_transcript_le_of_prior_ratio_horizon
      (capPolicy (coinCap n (pol u)) (pol u)) (fun i => d u i.val)
      (fun i => b i.val) (fun i => a i.val) K
    · intro i; exact ⟨(hd u i.val).1.le,(hd u i.val).2⟩
    · intro i; exact ⟨(hb i.val).1.le, (hb i.val).2.le⟩
    · intro i; exact ⟨(ha i.val).1.le, (ha i.val).2.le⟩
    · exact hK
    · intro i; exact hab i.val
    · intro i; exact hab' i.val
  have hpq u w : p u w ≤ K^n * r u w :=
    ratio u w (q u) (v u) (hq u) (hv u) (hqv u) (hqv' u)
  have hqp u w : r u w ≤ K^n * p u w :=
    ratio u w (v u) (q u) (hv u) (hq u) (hvq u) (hvq' u)
  let PN := prefixTranscriptLaw P seed tape n
  let QN := prefixTranscriptLaw Q seed tape n
  have : IsProbabilityMeasure PN := by dsimp [PN, prefixTranscriptLaw]; infer_instance
  have : IsProbabilityMeasure QN := by dsimp [QN, prefixTranscriptLaw]; infer_instance
  have hb := finite_kernel_kl_bound μ PN QN p r hpm hrm
    (fun u => (hpt u).1) hp1 (fun u => (hrt u).1) (K^n) (by positivity)
    hpq hqp (realized_creation_prefix_kernel μ P seed tape pol d q hs ht hP n)
    (realized_creation_prefix_kernel μ Q seed tape pol d v hs ht hQ n)
    workOf C (fun u =>
      transcript_kl_bound (coinCap n (pol u)) n
        (capPolicy (coinCap n (pol u)) (pol u)) (fun i => d u i.val)
        (fun i => q u i.val) (fun i => v u i.val) C (fun i => hd u i.val)
        (fun i => hq u i.val) (fun i => hv u i.val)
        (fun i => hstep u i.val))
  rw [realized_creation_prefix_work μ P seed tape pol d q hP n]
  exact hb

/-- The full stopped divergence is charged `C` per actual flip of the first law. -/
theorem ratio_creation_information_bound
    (Seed Ω : Type) [MeasurableSpace Seed] [MeasurableSpace Ω]
    (μ : Measure Seed) (P Q : Measure Ω)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (seed : Ω → Seed) (tape : Ω → ProcessTape)
    (pol : Seed → List Bool → Option ℕ) (d q v : Seed → ℕ → ℝ) (C K : ℝ)
    (hs : Measurable seed) (ht : ∀ n b, MeasurableSet {ω | tape ω n = b})
    (hp : MeasurableCreationPolicy pol) (hdm : MeasurableEnvironment d)
    (hqm : MeasurableEnvironment q) (hvm : MeasurableEnvironment v)
    (hP : RealizesCreationPrefixes μ P seed tape pol d q)
    (hQ : RealizesCreationPrefixes μ Q seed tape pol d v)
    (hd : ∀ u i, 0 < d u i ∧ d u i ≤ 1/2)
    (hq : ∀ u i, 0 < q u i ∧ q u i < 1)
    (hv : ∀ u i, 0 < v u i ∧ v u i < 1)
    (hK : 1 ≤ K)
    (hvq : ∀ u i, v u i ≤ K * q u i) (hvq' : ∀ u i, 1 - v u i ≤ K * (1 - q u i))
    (hqv : ∀ u i, q u i ≤ K * v u i) (hqv' : ∀ u i, 1 - q u i ≤ K * (1 - v u i))
    (hstep : ∀ u i A B, 0 ≤ A → 0 ≤ B → 0 < A+B →
      klB (mixPredict (d u i) (q u i) A B) (mixPredict (d u i) (v u i) A B) ≤ C)
    (hC : 0 ≤ C) (hwork : (∫⁻ ω, totalProcessWork (tape ω) ∂P) < ∞) :
    klDiv (infiniteTranscriptLaw P seed tape) (infiniteTranscriptLaw Q seed tape) ≤
      ENNReal.ofReal C * ∫⁻ ω, totalProcessWork (tape ω) ∂P := by
  have hfinite n := ratio_creation_finite_information Seed Ω μ P Q n seed tape pol d q v C K
    hs ht hp hdm hqm hvm hP hQ hd hq hv hK hvq hvq' hqv hqv' hstep
  rw [creation_kl_limit Seed Ω μ P Q seed tape pol d q v hs ht hp hP hQ hwork
    (fun n => ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hfinite n))]
  apply iSup_le
  intro n
  have hw := prefix_work_le_total P tape ht hwork n
  apply (hfinite n).trans
  calc
    _ ≤ ENNReal.ofReal (C * (∫⁻ ω, totalProcessWork (tape ω) ∂P).toReal) :=
      ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hw hC)
    _ = _ := by rw [ENNReal.ofReal_mul hC, ENNReal.ofReal_toReal hwork.ne]

/-- Population form in the unchanged observable experiment: two sign laws with
strict priors and a two-sided prior ratio `K`, and a per-step bound `C`. Only
the expected work of the first law is charged. -/
theorem ratio_experiment_information {R : Type} [MeasurableSpace R]
    (μ : Measure Gap) [IsProbabilityMeasure μ] (A : AdaptiveEstimator R)
    (q v : SignLaw) (C K W : ℝ) (hC : 0 ≤ C) (hK : 1 ≤ K)
    (hq : ∀ x, 0 < q.val x ∧ q.val x < 1) (hv : ∀ x, 0 < v.val x ∧ v.val x < 1)
    (hvq : ∀ x, v.val x ≤ K * q.val x) (hvq' : ∀ x, 1 - v.val x ≤ K * (1 - q.val x))
    (hqv : ∀ x, q.val x ≤ K * v.val x) (hqv' : ∀ x, 1 - q.val x ≤ K * (1 - v.val x))
    (hstep : ∀ (x : Gap) (a b : ℝ), 0 ≤ a → 0 ≤ b → 0 < a+b →
      klB (mixPredict (x:ℝ) (q.val x) a b) (mixPredict (x:ℝ) (v.val x) a b) ≤ C)
    (hw : expectedWork μ A q ≤ ENNReal.ofReal W) :
    klDiv (experimentLaw μ A q) (experimentLaw μ A v) ≤ ENNReal.ofReal (C * W) := by
  have ht n b : MeasurableSet {z : PopulationSeed R × ProcessTape | z.2 n = b} :=
    measurableSet_eq_fun ((measurable_pi_apply n).comp measurable_snd) measurable_const
  have hb := ratio_creation_information_bound (PopulationSeed R) (PopulationSeed R × ProcessTape)
    (populationSeedLaw μ A) (experimentLaw μ A q) (experimentLaw μ A v) Prod.fst Prod.snd
    (populationPolicy A) populationGap (populationPrior q) (populationPrior v)
    C K measurable_fst ht (measurable_populationPolicy A)
    measurable_populationGap (measurable_populationPrior q) (measurable_populationPrior v)
    (population_realization R μ A q).2 (population_realization R μ A v).2
    (fun u i => (u.2 i).property) (fun u i => hq (u.2 i)) (fun u i => hv (u.2 i)) hK
    (fun u i => hvq (u.2 i)) (fun u i => hvq' (u.2 i))
    (fun u i => hqv (u.2 i)) (fun u i => hqv' (u.2 i))
    (fun u i => hstep (u.2 i)) hC (lt_of_le_of_lt hw ENNReal.ofReal_lt_top)
  simp only [infiniteTranscriptLaw, Prod.mk.eta, Measure.map_id'] at hb
  apply hb.trans
  calc
    _ ≤ ENNReal.ofReal C * ENNReal.ofReal W :=
      mul_le_mul le_rfl hw bot_le bot_le
    _ = _ := (ENNReal.ofReal_mul hC).symm

end ThresholdHC.LocalizationCounter
