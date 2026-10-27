import ThresholdHC.Tier4.Model
import ThresholdHC.Tier4.FiniteDensity
import ThresholdHC.Tier3.StoppingBase

noncomputable section
open MeasureTheory InformationTheory
open scoped ENNReal
namespace ThresholdHC.Tier4
open ThresholdHC.Tier3

local instance (m : ℕ) : MeasurableSpace (Option (Fin m)) := ⊤

theorem finite_function_abs_bound {B : Type} [Finite B] (f : B → ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ b, |f b| ≤ C := by
  obtain ⟨C, hC⟩ := Finite.bddAbove_range (fun b => |f b|)
  exact ⟨max C 0, le_max_right _ _, fun b => (hC (Set.mem_range_self b)).trans (le_max_left _ _)⟩

theorem measurable_joint_prefix {Seed Ω : Type} [MeasurableSpace Seed] [MeasurableSpace Ω]
    (seed : Ω → Seed) (tape : Ω → ProcessTape) (hs : Measurable seed)
    (ht : ∀ n b, MeasurableSet {ω | tape ω n = b}) (n : ℕ) :
    Measurable (fun ω => (seed ω, processPrefix n (tape ω))) :=
  hs.prodMk (measurable_processPrefix tape ht n)

theorem integral_prefixTranscriptLaw {Seed Ω : Type} [MeasurableSpace Seed] [MeasurableSpace Ω]
    (μ : Measure Seed) (ν : Measure Ω) {m n : ℕ}
    (seed : Ω → Seed) (tape : Ω → ProcessTape)
    (pol : Seed → List Bool → Option (Fin m)) (d q : Fin m → ℝ)
    (hs : Measurable seed) (ht : ∀ n b, MeasurableSet {ω | tape ω n = b})
    (hR : RealizesPrefixes μ ν seed tape pol d q)
    (f : Seed × Prefix n → ℝ) (hf : Measurable f)
    (hb : ∃ C : ℝ, ∀ x, |f x| ≤ C) :
    (∫ x, f x ∂prefixTranscriptLaw ν seed tape n) =
      ∫ u, ∑ w : Prefix n, transcriptLaw (pol u) d q w * f (u,w) ∂μ := by
  rw [prefixTranscriptLaw, integral_map (measurable_joint_prefix seed tape hs ht n).aemeasurable
    hf.aestronglyMeasurable]
  apply hR n (fun u w => f (u,w))
  · intro w
    exact hf.comp (measurable_id.prodMk measurable_const)
  · obtain ⟨C,hC⟩ := hb
    exact ⟨C, fun u w => hC (u,w)⟩

def jointPolicyCode {Seed : Type} {m n : ℕ}
    (pol : Seed → List Bool → Option (Fin m)) (x : Seed × Prefix n) :
    PolicyCode m n × Prefix n := (policyCode pol x.1, x.2)

theorem measurable_jointPolicyCode {Seed : Type} [MeasurableSpace Seed] {m n : ℕ}
    (pol : Seed → List Bool → Option (Fin m)) (hp : MeasurablePolicy pol) :
    Measurable (jointPolicyCode (n := n) pol) :=
  ((measurable_policyCode pol hp).comp measurable_fst).prodMk measurable_snd

def finiteCodeRatio {m n : ℕ} (d η : Fin m → ℝ)
    (c : PolicyCode m n × Prefix n) : ℝ :=
  codeLaw c.1 d (fun i => 1/2 + η i) c.2 /
    codeLaw c.1 d (fun i => 1/2 - η i) c.2

theorem finite_prefix_kl_identity : FinitePrefixKLStatement := by
  intro Seed Ω _ _ μ P Q _ _ _ m n seed tape pol d η hs ht hp hRP hRQ hd hη
  let PN := prefixTranscriptLaw P seed tape n
  let QN := prefixTranscriptLaw Q seed tape n
  letI : IsProbabilityMeasure PN := by dsimp [PN, prefixTranscriptLaw]; infer_instance
  letI : IsProbabilityMeasure QN := by dsimp [QN, prefixTranscriptLaw]; infer_instance
  let g := jointPolicyCode (n := n) pol
  let r := finiteCodeRatio (n := n) d η
  have hg : Measurable g := measurable_jointPolicyCode pol hp
  have hrm : Measurable (fun x => r (g x)) := (measurable_of_countable r).comp hg
  have hp0 (u : Seed) (w : Prefix n) :
      0 ≤ transcriptLaw (pol u) d (fun i => 1/2 + η i) w := by
    apply (ThresholdHC.Proofs.transcript_law_total m n (pol u) d _
      (fun i => ⟨(hd i).1.le, (hd i).2⟩) (fun i => ?_)).1
    constructor <;> linarith [(hη i).1, (hη i).2]
  have hq0 (u : Seed) (w : Prefix n) :
      0 ≤ transcriptLaw (pol u) d (fun i => 1/2 - η i) w := by
    apply (ThresholdHC.Proofs.transcript_law_total m n (pol u) d _
      (fun i => ⟨(hd i).1.le, (hd i).2⟩) (fun i => ?_)).1
    constructor <;> linarith [(hη i).1, (hη i).2]
  have hr0 (x : Seed × Prefix n) : 0 ≤ r (g x) := div_nonneg (hp0 x.1 x.2) (hq0 x.1 x.2)
  have hratio (u : Seed) (w : Prefix n) :
      transcriptLaw (pol u) d (fun i => 1/2-η i) w * r (g (u,w)) =
      transcriptLaw (pol u) d (fun i => 1/2+η i) w := by
    change transcriptLaw (pol u) d (fun i => 1/2-η i) w *
      (transcriptLaw (pol u) d (fun i => 1/2+η i) w /
        transcriptLaw (pol u) d (fun i => 1/2-η i) w) = _
    by_cases hzero : transcriptLaw (pol u) d (fun i => 1/2-η i) w = 0
    · have hle := transcriptLaw_plus_le_minus (pol u) d η
        (fun i => ⟨(hd i).1.le, (hd i).2⟩) hη w
      have hz := hp0 u w
      simp only [hzero, mul_zero] at hle
      have : transcriptLaw (pol u) d (fun i => 1/2+η i) w = 0 := le_antisymm hle hz
      simp only [hzero, this, zero_mul, zero_div]
    · exact mul_div_cancel₀ _ hzero
  obtain ⟨C,hC0,hC⟩ := finite_function_abs_bound r
  have hdensity : QN.withDensity (fun x => ENNReal.ofReal (r (g x))) = PN := by
    symm
    apply measure_eq_withDensity_of_setIntegral PN QN _
      (integrable_finite_comp QN g hg r) hr0
    intro s hsm
    let f : Seed × Prefix n → ℝ := s.indicator 1
    have hfm : Measurable f := measurable_const.indicator hsm
    have hfb (x : Seed × Prefix n) : |f x| ≤ 1 := by
      by_cases hx : x ∈ s <;> simp [f, hx]
    have hpf := integral_prefixTranscriptLaw μ P seed tape pol d _ hs ht hRP
      f hfm ⟨1,hfb⟩
    have hqf := integral_prefixTranscriptLaw μ Q seed tape pol d _ hs ht hRQ
      (fun x => r (g x) * f x) (hrm.mul hfm) ⟨C, fun x => by
        rw [abs_mul]
        exact (mul_le_mul_of_nonneg_left (hfb x) (abs_nonneg _)).trans (by simpa using hC (g x))⟩
    calc
      PN.real s = ∫ x, f x ∂PN := (integral_indicator_one hsm).symm
      _ = ∫ u, ∑ w : Prefix n, transcriptLaw (pol u) d (fun i => 1/2+η i) w * f (u,w) ∂μ := hpf
      _ = ∫ u, ∑ w : Prefix n, transcriptLaw (pol u) d (fun i => 1/2-η i) w *
          (r (g (u,w)) * f (u,w)) ∂μ := by
        apply integral_congr_ae
        filter_upwards [] with u
        apply Finset.sum_congr rfl
        intro w hw
        rw [← mul_assoc, hratio]
      _ = ∫ x, r (g x) * f x ∂QN := hqf.symm
      _ = ∫ x in s, r (g x) ∂QN := by
        rw [← integral_indicator hsm]
        congr 1
        funext x
        by_cases hx : x ∈ s <;> simp [f, hx]
  rw [show prefixTranscriptLaw P seed tape n = PN from rfl,
    show prefixTranscriptLaw Q seed tape n = QN from rfl,
    klDiv_of_finite_likelihood PN QN g hg r hr0 hdensity]
  congr 1
  obtain ⟨L,hL0,hL⟩ := finite_function_abs_bound (fun c => Real.log (r c))
  exact integral_prefixTranscriptLaw μ P seed tape pol d _ hs ht hRP
    (fun x => Real.log (r (g x))) hrm.log ⟨L,fun x => hL (g x)⟩

end ThresholdHC.Tier4
