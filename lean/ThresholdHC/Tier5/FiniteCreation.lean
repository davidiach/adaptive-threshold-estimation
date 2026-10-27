import ThresholdHC.Tier5.Model
import ThresholdHC.Tier5.CreationBase
import ThresholdHC.Tier5.FiniteJoint
import ThresholdHC.Tier5.PriorRatio
import ThresholdHC.Tier3.StoppingBase

noncomputable section
open MeasureTheory InformationTheory
open scoped ENNReal

namespace ThresholdHC.Tier5
open ThresholdHC.Tier3 ThresholdHC.Tier4

local instance (m : ℕ) : MeasurableSpace (Option (Fin m)) := ⊤

theorem measurable_creationLaw {Seed : Type} [MeasurableSpace Seed] {n : ℕ}
    (pol : Seed → List Bool → Option ℕ) (hp : MeasurableCreationPolicy pol)
    (d q : Seed → ℕ → ℝ) (hdm : MeasurableEnvironment d) (hqm : MeasurableEnvironment q)
    (w : Prefix n) : Measurable (fun u => creationLaw (pol u) (d u) (q u) w) := by
  have hpol xs : Measurable (fun u => pol u xs) := measurable_to_countable' (hp xs)
  refine measurable_variable_finite_eval (fun u => coinCap n (pol u))
    (measurable_coinCap n pol hpol)
    (fun m u => transcriptLaw (capPolicy m (pol u))
      (fun i => d u i.val) (fun i => q u i.val) w) ?_
  intro m
  apply measurable_variable_transcriptLaw (fun u => capPolicy m (pol u))
  · intro xs a
    exact measurableSet_eq_fun (measurable_capPolicy m pol hpol xs) measurable_const
  · intro i
    exact hdm i.val
  · intro i
    exact hqm i.val

theorem realized_creation_prefix_kernel {Seed Ω : Type}
    [MeasurableSpace Seed] [MeasurableSpace Ω]
    (μ : Measure Seed) (ν : Measure Ω)
    (seed : Ω → Seed) (tape : Ω → ProcessTape)
    (pol : Seed → List Bool → Option ℕ) (d q : Seed → ℕ → ℝ)
    (hs : Measurable seed) (ht : ∀ n b, MeasurableSet {ω | tape ω n = b})
    (hr : RealizesCreationPrefixes μ ν seed tape pol d q) (n : ℕ) :
    FiniteKernelRealization μ (prefixTranscriptLaw ν seed tape n)
      (fun u w => creationLaw (pol u) (d u) (q u) w) := by
  intro f hf hb
  rw [prefixTranscriptLaw, integral_map
    (hs.prodMk (measurable_processPrefix tape ht n)).aemeasurable hf.aestronglyMeasurable]
  apply hr n (fun u w => f (u,w))
  · intro w
    exact hf.comp (measurable_id.prodMk measurable_const)
  · obtain ⟨C,hC⟩ := hb
    exact ⟨C,fun u w => hC (u,w)⟩

theorem realized_creation_prefix_work {Seed Ω : Type}
    [MeasurableSpace Seed] [MeasurableSpace Ω]
    (μ : Measure Seed) (ν : Measure Ω)
    (seed : Ω → Seed) (tape : Ω → ProcessTape)
    (pol : Seed → List Bool → Option ℕ) (d q : Seed → ℕ → ℝ)
    (hr : RealizesCreationPrefixes μ ν seed tape pol d q) (n : ℕ) :
    (∫ ω, workOf (processPrefix n (tape ω)) ∂ν) =
      ∫ u, ∑ w : Prefix n, creationLaw (pol u) (d u) (q u) w * workOf w ∂μ := by
  apply hr n (fun _ w => workOf w) (fun _ => measurable_const)
  refine ⟨n, fun _ w => ?_⟩
  rw [abs_of_nonneg (workOf_nonneg w)]
  exact workOf_le_length w

theorem creation_finite_kl_bound : CreationFiniteKLStatement := by
  intro Seed Ω _ _ μ P Q _ _ _ n seed tape pol d η h hs ht hp hdm hηm hP hQ
    hh hd hη hdη
  let p : Seed → Prefix n → ℝ := fun u w => creationLaw (pol u) (d u) (fun i => 1/2+η u i) w
  let q : Seed → Prefix n → ℝ := fun u w => creationLaw (pol u) (d u) (fun i => 1/2-η u i) w
  have hpm w : Measurable (fun u => p u w) :=
    measurable_creationLaw pol hp d _ hdm (fun i => measurable_const.add (hηm i)) w
  have hqm w : Measurable (fun u => q u w) :=
    measurable_creationLaw pol hp d _ hdm (fun i => measurable_const.sub (hηm i)) w
  have hpt u : (∀ w, 0 ≤ p u w) ∧ ∑ w, p u w = 1 := by
    apply creationLaw_total n (pol u) (d u) (fun i => 1/2+η u i)
      (fun i => ⟨(hd u i).1.le,(hd u i).2⟩)
    intro i
    constructor <;> linarith [(hη u i).1,(hη u i).2]
  have hqt u : (∀ w, 0 ≤ q u w) ∧ ∑ w, q u w = 1 := by
    apply creationLaw_total n (pol u) (d u) (fun i => 1/2-η u i)
      (fun i => ⟨(hd u i).1.le,(hd u i).2⟩)
    intro i
    constructor <;> linarith [(hη u i).1,(hη u i).2]
  have hp1 u w : p u w ≤ 1 := by
    rw [← (hpt u).2]
    exact Finset.single_le_sum (fun a ha => (hpt u).1 a) (Finset.mem_univ w)
  have hpq u w : p u w ≤ (5/3:ℝ)^n * q u w :=
    finite_transcript_plus_le_minus_horizon (capPolicy (coinCap n (pol u)) (pol u))
      (fun i => d u i.val) (fun i => η u i.val)
      (fun i => ⟨(hd u i.val).1.le,(hd u i.val).2⟩) (fun i => hη u i.val) w
  have hqp u w : q u w ≤ (5/3:ℝ)^n * p u w :=
    finite_transcript_minus_le_plus_horizon (capPolicy (coinCap n (pol u)) (pol u))
      (fun i => d u i.val) (fun i => η u i.val)
      (fun i => ⟨(hd u i.val).1.le,(hd u i.val).2⟩) (fun i => hη u i.val) w
  let PN := prefixTranscriptLaw P seed tape n
  let QN := prefixTranscriptLaw Q seed tape n
  letI : IsProbabilityMeasure PN := by dsimp [PN, prefixTranscriptLaw]; infer_instance
  letI : IsProbabilityMeasure QN := by dsimp [QN, prefixTranscriptLaw]; infer_instance
  have hb := finite_kernel_kl_bound μ PN QN p q hpm hqm
    (fun u => (hpt u).1) hp1 (fun u => (hqt u).1) ((5/3:ℝ)^n) (by positivity)
    hpq hqp (realized_creation_prefix_kernel μ P seed tape pol d _ hs ht hP n)
    (realized_creation_prefix_kernel μ Q seed tape pol d _ hs ht hQ n)
    workOf ((128/225:ℝ)*h^2) (fun u =>
      ThresholdHC.Proofs.stopped_transcript_kl (coinCap n (pol u)) n
        (capPolicy (coinCap n (pol u)) (pol u)) (fun i => d u i.val) (fun i => η u i.val)
        h hh (fun i => hd u i.val) (fun i => hη u i.val) (fun i => hdη u i.val))
  rw [realized_creation_prefix_work μ P seed tape pol d _ hP n]
  exact hb

end ThresholdHC.Tier5
