import ThresholdHC.Tier4.Specification
import ThresholdHC.Tier4.FiniteBase
import ThresholdHC.Tier4.StoppedFull
import ThresholdHC.Tier4.BoundReduction

noncomputable section
open MeasureTheory
open scoped ENNReal

namespace ThresholdHC.Tier4
open ThresholdHC.Tier3

theorem infinite_kl_bound : InfiniteKLBoundStatement :=
  infiniteKLBound_of_supremum finite_prefix_kl_identity infinite_kl_eq_iSup

theorem infinite_kl_finite : InfiniteKLFiniteStatement :=
  infiniteKLFinite_of_bound infinite_kl_bound

theorem observable_kl_bound : ObservableKLBoundStatement :=
  observableKLBound_of_bound infinite_kl_bound

theorem tier4_landmark : Tier4LandmarkStatement :=
  ⟨finite_prefix_kl_identity, infinite_kl_eq_iSup, infinite_kl_bound,
    infinite_kl_finite, observable_kl_bound⟩

/-- The extended-real information/work inequality also covers infinite expected
work. Its substantive finite-work case is the locked infinite-transcript bound. -/
theorem infinite_kl_bound_extended
    (Seed Ω : Type) [MeasurableSpace Seed] [MeasurableSpace Ω]
    (μ : Measure Seed) (P Q : Measure Ω)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (m : ℕ) (seed : Ω → Seed) (tape : Ω → ProcessTape)
    (pol : Seed → List Bool → Option (Fin m)) (d η : Fin m → ℝ) (h : ℝ)
    (hs : Measurable seed) (ht : ∀ n b, MeasurableSet {ω | tape ω n = b})
    (hp : MeasurablePolicy pol)
    (hP : RealizesPrefixes μ P seed tape pol d (fun i => 1/2 + η i))
    (hQ : RealizesPrefixes μ Q seed tape pol d (fun i => 1/2 - η i))
    (hh : 0 < h) (hd : ∀ i, 0 < d i ∧ d i ≤ 1/2)
    (hη : ∀ i, 0 ≤ η i ∧ η i ≤ 1/8) (hdη : ∀ i, d i * η i ≤ h/8) :
    InformationTheory.klDiv (infiniteTranscriptLaw P seed tape)
      (infiniteTranscriptLaw Q seed tape) ≤
      ENNReal.ofReal ((128/225) * h^2) * ∫⁻ ω, totalProcessWork (tape ω) ∂P := by
  by_cases hwork : (∫⁻ ω, totalProcessWork (tape ω) ∂P) < ∞
  · exact infinite_kl_bound Seed Ω μ P Q m seed tape pol d η h hs ht hp hP hQ
      hh hd hη hdη hwork
  · have htop : (∫⁻ ω, totalProcessWork (tape ω) ∂P) = ∞ :=
      eq_top_iff.mpr (not_lt.mp hwork)
    have hc : ENNReal.ofReal ((128/225:ℝ) * h^2) ≠ 0 := by positivity
    rw [htop, ENNReal.mul_top hc]
    exact le_top

end ThresholdHC.Tier4
