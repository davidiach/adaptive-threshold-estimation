import ThresholdHC.Tier5.StoppingBase
import ThresholdHC.Tier5.EntropyPrefix

noncomputable section
open MeasureTheory Filter InformationTheory
open scoped ENNReal

namespace ThresholdHC.Tier5
open ThresholdHC.Tier3 ThresholdHC.Tier4

local instance stoppingFlagSpace : MeasurableSpace (Option (Fin 1)) := ⊤

/-- Only the stopped/running status is used for tape reconstruction. -/
def stoppingFlagPolicy {Seed : Type} (pol : Seed → List Bool → Option ℕ)
    (u : Seed) (xs : List Bool) : Option (Fin 1) :=
  (pol u xs).map (fun _ => 0)

theorem measurable_stoppingFlagPolicy {Seed : Type} [MeasurableSpace Seed]
    (pol : Seed → List Bool → Option ℕ) (hp : MeasurableCreationPolicy pol) :
    MeasurablePolicy (stoppingFlagPolicy pol) := by
  intro xs a
  exact measurableSet_eq_fun
    ((measurable_of_countable (fun o : Option ℕ => o.map (fun _ => (0 : Fin 1)))).comp
      (measurable_creation_policy pol hp xs)) measurable_const

theorem realized_creation_stopped_reconstruction {Seed Ω : Type}
    [MeasurableSpace Seed] [MeasurableSpace Ω]
    (μ : Measure Seed) (ν : Measure Ω) [IsProbabilityMeasure ν]
    (seed : Ω → Seed) (tape : Ω → ProcessTape)
    (pol : Seed → List Bool → Option ℕ) (d q : Seed → ℕ → ℝ)
    (hs : Measurable seed) (ht : ∀ n b, MeasurableSet {ω | tape ω n = b})
    (hp : MeasurableCreationPolicy pol) (hr : RealizesCreationPrefixes μ ν seed tape pol d q)
    (n : ℕ) :
    ∀ᵐ z ∂infiniteTranscriptLaw ν seed tape,
      z ∈ stoppedFullSet (stoppingFlagPolicy pol) n →
      padJoint n (z.1, processPrefix n z.2) = z := by
  have hflag := measurable_stoppingFlagPolicy pol hp
  apply (ae_map_iff (hs.prodMk (measurable_processTape tape ht)).aemeasurable ?_).mpr
  · have hv : ∀ᵐ ω ∂ν, ∀ k, (tape ω k).isSome =
        (pol (seed ω) (processHistory (tape ω) k)).isSome :=
      ae_all_iff.2 (fun k => realized_creation_valid_step μ ν seed tape pol d q hs ht hp hr k)
    filter_upwards [hv] with ω hvalid hz
    apply stopped_valid_reconstruction (stoppingFlagPolicy pol) (seed ω, tape ω) _ n hz
    simpa only [stoppingFlagPolicy, Option.isSome_map] using hvalid
  · exact (measurableSet_stoppedFull _ hflag n).imp (measurableSet_reconstructed n)

theorem realized_creation_stopped_cover {Seed Ω : Type}
    [MeasurableSpace Seed] [MeasurableSpace Ω]
    (ν : Measure Ω) (seed : Ω → Seed) (tape : Ω → ProcessTape)
    (pol : Seed → List Bool → Option ℕ)
    (hs : Measurable seed) (ht : ∀ n b, MeasurableSet {ω | tape ω n = b})
    (hp : MeasurableCreationPolicy pol)
    (hstop : ∀ᵐ ω ∂ν, ∃ n, pol (seed ω) (processHistory (tape ω) n) = none) :
    ∀ᵐ z ∂infiniteTranscriptLaw ν seed tape,
      z ∈ ⋃ n, stoppedFullSet (stoppingFlagPolicy pol) n := by
  apply (ae_map_iff (hs.prodMk (measurable_processTape tape ht)).aemeasurable ?_).mpr
  · filter_upwards [hstop] with ω hω
    obtain ⟨n, hn⟩ := hω
    apply Set.mem_iUnion.mpr
    exact ⟨n, n, le_rfl, by simp [stoppingFlagPolicy, hn]⟩
  · exact MeasurableSet.iUnion fun n =>
      measurableSet_stoppedFull _ (measurable_stoppingFlagPolicy pol hp) n

/-- The second law need not halt. Absolute continuity follows from the first
law's stopped cover and local prefix absolute continuity; the entropy limit
then follows from the generating-prefix martingale theorem. -/
theorem creationKLSupremum_of_finiteKL (hfinite : CreationFiniteKLStatement) :
    CreationKLSupremumStatement := by
  intro Seed Ω _ _ μ P Q _ _ _ seed tape pol d η hs ht hp hdm hηm hP hQ hd hη hwork
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
    have hcap := hfinite Seed Ω μ P Q n seed tape pol d η 1 hs ht hp hdm hηm hP hQ
      (by norm_num) hd hη (fun u i => by
        have hm : d u i * η u i ≤ (1/2:ℝ) * (1/8:ℝ) :=
          mul_le_mul (hd u i).2 (hη u i).2 (hη u i).1 (by norm_num)
        linarith)
    have hmaps : klDiv (IP.map (f n)) (IQ.map (f n)) ≠ ∞ := by
      change klDiv ((infiniteTranscriptLaw P seed tape).map (f n))
        ((infiniteTranscriptLaw Q seed tape).map (f n)) ≠ ∞
      simp only [f, infiniteTranscriptLaw_map_prefix P seed tape hs ht,
        infiniteTranscriptLaw_map_prefix Q seed tape hs ht]
      exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top hcap
    exact (klDiv_ne_top_iff.mp (ne_top_of_le_ne_top hmaps hbound)).1
  have hcover : ∀ᵐ z ∂IP, z ∈ ⋃ n, E n := by
    simp_rw [heq]
    exact realized_creation_stopped_cover P seed tape pol hs ht hp hstop
  have hac : IP ≪ IQ := absolutelyContinuous_of_restrict_exhaustion IP IQ E hcover hlocal
  have hfull := joint_tape_kl_eq_iSup_prefix_of_ac Seed IP IQ hac
  simpa only [IP, IQ, infiniteTranscriptLaw_map_prefix P seed tape hs ht,
    infiniteTranscriptLaw_map_prefix Q seed tape hs ht] using hfull

end ThresholdHC.Tier5
