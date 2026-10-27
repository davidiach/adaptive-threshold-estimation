import ThresholdHC.Tier5.Specification
import ThresholdHC.Tier5.BoundReduction
import ThresholdHC.Tier5.StoppingFull
import ThresholdHC.Tier5.CreationExample

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace ThresholdHC.Tier5
open ThresholdHC.Tier3 ThresholdHC.Tier4

theorem creation_infinite_kl_bound : CreationInfiniteKLStatement :=
  creationInfiniteKL_of_prefix creation_finite_kl_bound creation_kl_eq_iSup

theorem creation_observable_kl_bound : CreationObservableKLStatement :=
  creationObservableKL_of_bound creation_infinite_kl_bound

theorem tier5_landmark : Tier5LandmarkStatement :=
  ⟨creation_law_total, creation_law_consistent, creation_finite_kl_bound,
    creation_stops, creation_kl_eq_iSup, creation_infinite_kl_bound,
    creation_observable_kl_bound, unbounded_creation_example⟩

/-- Extended-real formulation covering infinite expected work as well. -/
theorem creation_infinite_kl_bound_extended
    (Seed Ω : Type) [MeasurableSpace Seed] [MeasurableSpace Ω]
    (μ : Measure Seed) (P Q : Measure Ω)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (seed : Ω → Seed) (tape : Ω → ProcessTape)
    (pol : Seed → List Bool → Option ℕ) (d η : Seed → ℕ → ℝ) (h : ℝ)
    (hs : Measurable seed) (ht : ∀ n b, MeasurableSet {ω | tape ω n = b})
    (hp : MeasurableCreationPolicy pol) (hdm : MeasurableEnvironment d)
    (hηm : MeasurableEnvironment η)
    (hP : RealizesCreationPrefixes μ P seed tape pol d (fun u i => 1/2+η u i))
    (hQ : RealizesCreationPrefixes μ Q seed tape pol d (fun u i => 1/2-η u i))
    (hh : 0 < h) (hd : ∀ u i, 0 < d u i ∧ d u i ≤ 1/2)
    (hη : ∀ u i, 0 ≤ η u i ∧ η u i ≤ 1/8)
    (hdη : ∀ u i, d u i * η u i ≤ h/8) :
    InformationTheory.klDiv (infiniteTranscriptLaw P seed tape)
      (infiniteTranscriptLaw Q seed tape) ≤
      ENNReal.ofReal ((128/225) * h^2) * ∫⁻ ω, totalProcessWork (tape ω) ∂P := by
  by_cases hwork : (∫⁻ ω, totalProcessWork (tape ω) ∂P) < ∞
  · exact creation_infinite_kl_bound Seed Ω μ P Q seed tape pol d η h hs ht hp hdm hηm
      hP hQ hh hd hη hdη hwork
  · have htop : (∫⁻ ω, totalProcessWork (tape ω) ∂P) = ∞ :=
      eq_top_iff.mpr (not_lt.mp hwork)
    have hc : ENNReal.ofReal ((128/225:ℝ) * h^2) ≠ 0 := by positivity
    rw [htop, ENNReal.mul_top hc]
    exact le_top

end ThresholdHC.Tier5
