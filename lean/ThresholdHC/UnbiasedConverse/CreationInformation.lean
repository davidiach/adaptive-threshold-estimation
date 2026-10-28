import ThresholdHC.UnbiasedConverse.Transcript
import ThresholdHC.Tier5.FiniteCreation
import ThresholdHC.Tier5.StoppingEntropy

noncomputable section
open MeasureTheory InformationTheory Filter
open scoped ENNReal
namespace ThresholdHC.UnbiasedConverse
open ThresholdHC ThresholdHC.Proofs.Transcript
open ThresholdHC.Tier3 ThresholdHC.Tier4 ThresholdHC.Tier5

theorem creation_finite_information
    (Seed Ω : Type) [MeasurableSpace Seed] [MeasurableSpace Ω]
    (μ : Measure Seed) (P Q : Measure Ω)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (n : ℕ) (seed : Ω → Seed) (tape : Ω → ProcessTape)
    (pol : Seed → List Bool → Option ℕ) (d q v : Seed → ℕ → ℝ) (C : ℝ)
    (hs : Measurable seed) (ht : ∀ n b, MeasurableSet {ω | tape ω n = b})
    (hp : MeasurableCreationPolicy pol) (hdm : MeasurableEnvironment d)
    (hqm : MeasurableEnvironment q) (hvm : MeasurableEnvironment v)
    (hP : RealizesCreationPrefixes μ P seed tape pol d q)
    (hQ : RealizesCreationPrefixes μ Q seed tape pol d v)
    (hd : ∀ u i, 0 < d u i ∧ d u i ≤ 1/2)
    (hq : ∀ u i, (3/8:ℝ) ≤ q u i ∧ q u i ≤ 5/8)
    (hv : ∀ u i, (3/8:ℝ) ≤ v u i ∧ v u i ≤ 5/8)
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
    intro i; constructor <;> linarith [(hq u i).1,(hq u i).2]
  have hrt u : (∀ w, 0 ≤ r u w) ∧ ∑ w, r u w = 1 := by
    apply creationLaw_total n (pol u) (d u) (v u) (fun i => ⟨(hd u i).1.le,(hd u i).2⟩)
    intro i; constructor <;> linarith [(hv u i).1,(hv u i).2]
  have hp1 u w : p u w ≤ 1 := by
    rw [← (hpt u).2]
    exact Finset.single_le_sum (fun a ha => (hpt u).1 a) (Finset.mem_univ w)
  have ratio (u : Seed) (w : Prefix n) (a b : ℕ → ℝ)
      (ha : ∀ i, (3/8:ℝ) ≤ a i ∧ a i ≤ 5/8)
      (hb : ∀ i, (3/8:ℝ) ≤ b i ∧ b i ≤ 5/8) :
      creationLaw (pol u) (d u) a w ≤ (5/3:ℝ)^n * creationLaw (pol u) (d u) b w := by
    apply finite_transcript_le_of_prior_ratio_horizon
      (capPolicy (coinCap n (pol u)) (pol u)) (fun i => d u i.val)
      (fun i => b i.val) (fun i => a i.val) (5/3)
    · intro i; exact ⟨(hd u i.val).1.le,(hd u i.val).2⟩
    · intro i; constructor <;> linarith [(hb i.val).1,(hb i.val).2]
    · intro i; constructor <;> linarith [(ha i.val).1,(ha i.val).2]
    · norm_num
    · intro i; linarith [(ha i.val).2,(hb i.val).1]
    · intro i; linarith [(ha i.val).1,(hb i.val).2]
  have hpq u w : p u w ≤ (5/3:ℝ)^n * r u w := ratio u w (q u) (v u) (hq u) (hv u)
  have hqp u w : r u w ≤ (5/3:ℝ)^n * p u w := ratio u w (v u) (q u) (hv u) (hq u)
  let PN := prefixTranscriptLaw P seed tape n
  let QN := prefixTranscriptLaw Q seed tape n
  have : IsProbabilityMeasure PN := by dsimp [PN, prefixTranscriptLaw]; infer_instance
  have : IsProbabilityMeasure QN := by dsimp [QN, prefixTranscriptLaw]; infer_instance
  have hb := finite_kernel_kl_bound μ PN QN p r hpm hrm
    (fun u => (hpt u).1) hp1 (fun u => (hrt u).1) ((5/3:ℝ)^n) (by positivity)
    hpq hqp (realized_creation_prefix_kernel μ P seed tape pol d q hs ht hP n)
    (realized_creation_prefix_kernel μ Q seed tape pol d v hs ht hQ n)
    workOf C (fun u =>
      transcript_kl_bound (coinCap n (pol u)) n
        (capPolicy (coinCap n (pol u)) (pol u)) (fun i => d u i.val)
        (fun i => q u i.val) (fun i => v u i.val) C (fun i => hd u i.val)
        (fun i => ⟨by linarith [(hq u i.val).1], by linarith [(hq u i.val).2]⟩)
        (fun i => ⟨by linarith [(hv u i.val).1], by linarith [(hv u i.val).2]⟩)
        (fun i => hstep u i.val))
  rw [realized_creation_prefix_work μ P seed tape pol d q hP n]
  exact hb

/-- Stopping plus finite prefix information identifies the full divergence.
The two sign laws are arbitrary here; either direction can be used. -/
theorem creation_kl_limit
    (Seed Ω : Type) [MeasurableSpace Seed] [MeasurableSpace Ω]
    (μ : Measure Seed) (P Q : Measure Ω)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (seed : Ω → Seed) (tape : Ω → ProcessTape)
    (pol : Seed → List Bool → Option ℕ) (d q v : Seed → ℕ → ℝ)
    (hs : Measurable seed) (ht : ∀ n b, MeasurableSet {ω | tape ω n = b})
    (hp : MeasurableCreationPolicy pol)
    (hP : RealizesCreationPrefixes μ P seed tape pol d q)
    (hQ : RealizesCreationPrefixes μ Q seed tape pol d v)
    (hwork : (∫⁻ ω, totalProcessWork (tape ω) ∂P) < ∞)
    (hprefix : ∀ n, klDiv (prefixTranscriptLaw P seed tape n)
      (prefixTranscriptLaw Q seed tape n) ≠ ∞) :
    klDiv (infiniteTranscriptLaw P seed tape) (infiniteTranscriptLaw Q seed tape) =
      ⨆ n, klDiv (prefixTranscriptLaw P seed tape n) (prefixTranscriptLaw Q seed tape n) := by
  have hstop := creation_stops Seed Ω μ P seed tape pol d _ hs ht hp hP hwork
  have hflag := measurable_stoppingFlagPolicy pol hp
  let IP := infiniteTranscriptLaw P seed tape
  let IQ := infiniteTranscriptLaw Q seed tape
  let f : (n : ℕ) → (Seed × ProcessTape) → (Seed × Prefix n) :=
    fun n z => (z.1, processPrefix n z.2)
  let E : ℕ → Set (Seed × ProcessTape) :=
    fun n => f n ⁻¹' stoppedPrefixSet (stoppingFlagPolicy pol) n
  have heq (n : ℕ) : E n = stoppedFullSet (stoppingFlagPolicy pol) n := by
    ext z
    exact (stoppedFullSet_prefix (stoppingFlagPolicy pol) n z).symm
  haveI : IsFiniteMeasure IP := by dsimp [IP, infiniteTranscriptLaw]; infer_instance
  haveI : IsFiniteMeasure IQ := by dsimp [IQ, infiniteTranscriptLaw]; infer_instance
  have hrecP (n : ℕ) : ∀ᵐ z ∂IP.restrict (E n), padJoint n (f n z) = z := by
    rw [heq]
    exact (ae_restrict_iff' (measurableSet_stoppedFull _ hflag n)).mpr
      (realized_creation_stopped_reconstruction μ P seed tape pol d _ hs ht hp hP n)
  have hrecQ (n : ℕ) : ∀ᵐ z ∂IQ.restrict (E n), padJoint n (f n z) = z := by
    rw [heq]
    exact (ae_restrict_iff' (measurableSet_stoppedFull _ hflag n)).mpr
      (realized_creation_stopped_reconstruction μ Q seed tape pol d _ hs ht hp hQ n)
  have hlocal (n : ℕ) : IP.restrict (E n) ≪ IQ.restrict (E n) := by
    have hbound := klDiv_restrict_le_map_of_reconstruct IP IQ (f n) (padJoint n)
      (stoppedPrefixSet (stoppingFlagPolicy pol) n) (measurable_jointPrefix n)
      (measurable_padJoint n) (measurableSet_stoppedPrefix _ hflag n) (hrecP n) (hrecQ n)
    have hmaps : klDiv (IP.map (f n)) (IQ.map (f n)) ≠ ∞ := by
      change klDiv ((infiniteTranscriptLaw P seed tape).map (f n))
        ((infiniteTranscriptLaw Q seed tape).map (f n)) ≠ ∞
      simp only [f, infiniteTranscriptLaw_map_prefix P seed tape hs ht,
        infiniteTranscriptLaw_map_prefix Q seed tape hs ht]
      exact hprefix n
    exact (klDiv_ne_top_iff.mp (ne_top_of_le_ne_top hmaps hbound)).1
  have hcover : ∀ᵐ z ∂IP, z ∈ ⋃ n, E n := by
    simp_rw [heq]
    exact realized_creation_stopped_cover P seed tape pol hs ht hp hstop
  have hac : IP ≪ IQ := absolutelyContinuous_of_restrict_exhaustion IP IQ E hcover hlocal
  have hfull := joint_tape_kl_eq_iSup_prefix_of_ac Seed IP IQ hac
  simpa only [IP, IQ, infiniteTranscriptLaw_map_prefix P seed tape hs ht,
    infiniteTranscriptLaw_map_prefix Q seed tape hs ht] using hfull

/-- The exact per-query coefficient is charged only for actual flips. -/
theorem creation_information_bound
    (Seed Ω : Type) [MeasurableSpace Seed] [MeasurableSpace Ω]
    (μ : Measure Seed) (P Q : Measure Ω)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (seed : Ω → Seed) (tape : Ω → ProcessTape)
    (pol : Seed → List Bool → Option ℕ) (d q v : Seed → ℕ → ℝ) (C : ℝ)
    (hs : Measurable seed) (ht : ∀ n b, MeasurableSet {ω | tape ω n = b})
    (hp : MeasurableCreationPolicy pol) (hdm : MeasurableEnvironment d)
    (hqm : MeasurableEnvironment q) (hvm : MeasurableEnvironment v)
    (hP : RealizesCreationPrefixes μ P seed tape pol d q)
    (hQ : RealizesCreationPrefixes μ Q seed tape pol d v)
    (hd : ∀ u i, 0 < d u i ∧ d u i ≤ 1/2)
    (hq : ∀ u i, (3/8:ℝ) ≤ q u i ∧ q u i ≤ 5/8)
    (hv : ∀ u i, (3/8:ℝ) ≤ v u i ∧ v u i ≤ 5/8)
    (hstep : ∀ u i A B, 0 ≤ A → 0 ≤ B → 0 < A+B →
      klB (mixPredict (d u i) (q u i) A B) (mixPredict (d u i) (v u i) A B) ≤ C)
    (hC : 0 ≤ C) (hwork : (∫⁻ ω, totalProcessWork (tape ω) ∂P) < ∞) :
    klDiv (infiniteTranscriptLaw P seed tape) (infiniteTranscriptLaw Q seed tape) ≤
      ENNReal.ofReal C * ∫⁻ ω, totalProcessWork (tape ω) ∂P := by
  have hfinite n := creation_finite_information Seed Ω μ P Q n seed tape pol d q v C
    hs ht hp hdm hqm hvm hP hQ hd hq hv hstep
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

end ThresholdHC.UnbiasedConverse
