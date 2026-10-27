import ThresholdHC.Tier5.Model
import ThresholdHC.Tier3.StoppingBase
import ThresholdHC.Tier4.BoundReduction

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace ThresholdHC.Tier5
open ThresholdHC.Tier3 ThresholdHC.Tier4

theorem creationInfiniteKL_of_prefix
    (hprefix : CreationFiniteKLStatement) (hsup : CreationKLSupremumStatement) :
    CreationInfiniteKLStatement := by
  intro Seed Ω _ _ μ P Q _ _ _ seed tape pol d η h hs ht hp hdm hηm
    hP hQ hh hd hη hdη hwork
  rw [hsup Seed Ω μ P Q seed tape pol d η hs ht hp hdm hηm hP hQ hd hη hwork]
  apply iSup_le
  intro n
  have hfinite := hprefix Seed Ω μ P Q n seed tape pol d η h hs ht hp hdm hηm
    hP hQ hh hd hη hdη
  have hbudget := prefix_work_le_total P tape ht hwork n
  have hC : 0 ≤ (128/225:ℝ) * h^2 := by positivity
  apply hfinite.trans
  calc
    ENNReal.ofReal ((128/225:ℝ) * h^2 * ∫ ω, workOf (processPrefix n (tape ω)) ∂P)
        ≤ ENNReal.ofReal ((128/225:ℝ) * h^2 *
          (∫⁻ ω, totalProcessWork (tape ω) ∂P).toReal) :=
      ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hbudget hC)
    _ = _ := by rw [ENNReal.ofReal_mul hC, ENNReal.ofReal_toReal hwork.ne]

theorem creationObservableKL_of_bound (hbound : CreationInfiniteKLStatement) :
    CreationObservableKLStatement := by
  intro Seed Ω Z _ _ _ μ P Q _ _ _ seed tape pol d η h observe
    hs ht hp hdm hηm ho hP hQ hh hd hη hdη hwork
  have hm := measurable_infinite_observation seed tape hs ht
  let IP := infiniteTranscriptLaw P seed tape
  let IQ := infiniteTranscriptLaw Q seed tape
  haveI : IsFiniteMeasure IP := by dsimp [IP, infiniteTranscriptLaw]; infer_instance
  haveI : IsFiniteMeasure IQ := by dsimp [IQ, infiniteTranscriptLaw]; infer_instance
  have hdata := InformationTheory.klDiv_map_le IP IQ ho
  rw [show IP.map observe = P.map (fun ω => observe (seed ω, tape ω)) by
    exact Measure.map_map ho hm,
    show IQ.map observe = Q.map (fun ω => observe (seed ω, tape ω)) by
    exact Measure.map_map ho hm] at hdata
  exact hdata.trans (hbound Seed Ω μ P Q seed tape pol d η h hs ht hp hdm hηm
    hP hQ hh hd hη hdη hwork)

end ThresholdHC.Tier5
