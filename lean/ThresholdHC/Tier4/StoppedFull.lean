import ThresholdHC.Tier4.StoppedReconstruction
import ThresholdHC.Tier4.Entropy

noncomputable section
open MeasureTheory Filter
open scoped ENNReal

namespace ThresholdHC.Tier4
open ThresholdHC.Tier3

/-- The entire seed and infinite tape are recovered by stopped finite prefixes.
The generic restriction-exhaustion entropy theorem gives the actual KL limit. -/
theorem infinite_kl_eq_iSup : InfiniteKLSupremumStatement := by
  intro Seed Ω _ _ μ P Q _ _ _ m seed tape pol d η hs htape hp hrP hrQ hd hη hfin
  obtain ⟨hstopP, hstopQ⟩ :=
    unbounded_stopping Seed Ω μ P Q m seed tape pol d η hs htape hp hrP hrQ hd hη hfin
  let f : (n : ℕ) → (Seed × ProcessTape) → (Seed × Prefix n) :=
    fun n z => (z.1, processPrefix n z.2)
  have heq (n : ℕ) : f n ⁻¹' stoppedPrefixSet pol n = stoppedFullSet pol n := by
    ext z
    exact (stoppedFullSet_prefix pol n z).symm
  have hcoverP : ∀ᵐ z ∂infiniteTranscriptLaw P seed tape,
      z ∈ ⋃ n, f n ⁻¹' stoppedPrefixSet pol n := by
    simp_rw [heq, Set.mem_iUnion]
    exact realized_stopped_cover μ P seed tape pol d _ hs htape hp hrP hstopP
  have hcoverQ : ∀ᵐ z ∂infiniteTranscriptLaw Q seed tape,
      z ∈ ⋃ n, f n ⁻¹' stoppedPrefixSet pol n := by
    simp_rw [heq, Set.mem_iUnion]
    exact realized_stopped_cover μ Q seed tape pol d _ hs htape hp hrQ hstopQ
  have hrecP (n : ℕ) : ∀ᵐ z ∂(infiniteTranscriptLaw P seed tape).restrict
      (f n ⁻¹' stoppedPrefixSet pol n), padJoint n (f n z) = z := by
    rw [heq]
    exact (ae_restrict_iff' (measurableSet_stoppedFull pol hp n)).mpr
      (realized_stopped_reconstruction μ P seed tape pol d _ hs htape hp hrP n)
  have hrecQ (n : ℕ) : ∀ᵐ z ∂(infiniteTranscriptLaw Q seed tape).restrict
      (f n ⁻¹' stoppedPrefixSet pol n), padJoint n (f n z) = z := by
    rw [heq]
    exact (ae_restrict_iff' (measurableSet_stoppedFull pol hp n)).mpr
      (realized_stopped_reconstruction μ Q seed tape pol d _ hs htape hp hrQ n)
  have hm : Monotone (fun n => f n ⁻¹' stoppedPrefixSet pol n) := by
    simp_rw [heq]
    exact stoppedFullSet_mono pol
  letI : IsFiniteMeasure (infiniteTranscriptLaw P seed tape) := by
    unfold infiniteTranscriptLaw
    infer_instance
  letI : IsFiniteMeasure (infiniteTranscriptLaw Q seed tape) := by
    unfold infiniteTranscriptLaw
    infer_instance
  have hfull := klDiv_eq_iSup_map_of_reconstruction
    (infiniteTranscriptLaw P seed tape) (infiniteTranscriptLaw Q seed tape)
    f padJoint (stoppedPrefixSet pol) measurable_jointPrefix measurable_padJoint
    (measurableSet_stoppedPrefix pol hp) hm hcoverP hcoverQ hrecP hrecQ
  simpa only [f, infiniteTranscriptLaw_map_prefix P seed tape hs htape,
    infiniteTranscriptLaw_map_prefix Q seed tape hs htape] using hfull

end ThresholdHC.Tier4
