import ThresholdHC.Tier4.Model
import ThresholdHC.Tier3.RandomizedBase
import ThresholdHC.Tier3.StoppingBase

noncomputable section
open MeasureTheory
open scoped ENNReal

namespace ThresholdHC.Tier4
open ThresholdHC.Tier3

theorem infiniteKLBound_of_supremum
    (hprefix : FinitePrefixKLStatement) (hsup : InfiniteKLSupremumStatement) :
    InfiniteKLBoundStatement := by
  intro Seed Ω _ _ μ P Q _ _ _ m seed tape pol d η h hs ht hp hP hQ hh hd hη hdη hwork
  rw [hsup Seed Ω μ P Q m seed tape pol d η hs ht hp hP hQ hd hη hwork]
  apply iSup_le
  intro n
  rw [hprefix Seed Ω μ P Q m n seed tape pol d η hs ht hp hP hQ hd hη]
  have hfinite := randomized_information_bound Seed μ m n pol d η h hp hh hd hη hdη
  have hbudget := prefix_work_le_total P tape ht hwork n
  rw [realized_prefix_work_eq μ P seed tape pol d _ hP n] at hbudget
  have hC : 0 ≤ (128/225:ℝ) * h^2 := by positivity
  calc
    ENNReal.ofReal (conditionalInformation μ pol d η n)
        ≤ ENNReal.ofReal ((128/225:ℝ) * h^2 *
          (∫⁻ ω, totalProcessWork (tape ω) ∂P).toReal) :=
      ENNReal.ofReal_le_ofReal (hfinite.trans (mul_le_mul_of_nonneg_left hbudget hC))
    _ = _ := by rw [ENNReal.ofReal_mul hC, ENNReal.ofReal_toReal hwork.ne]

theorem infiniteKLFinite_of_bound (hbound : InfiniteKLBoundStatement) :
    InfiniteKLFiniteStatement := by
  intro Seed Ω _ _ μ P Q _ _ _ m seed tape pol d η hs ht hp hP hQ hd hη hwork
  have hdη i : d i * η i ≤ (1:ℝ)/8 := by
    have : d i * η i ≤ (1/2:ℝ) * (1/8:ℝ) :=
      mul_le_mul (hd i).2 (hη i).2 (hη i).1 (by norm_num)
    linarith
  have hle := hbound Seed Ω μ P Q m seed tape pol d η 1 hs ht hp hP hQ
    (by norm_num) hd hη hdη hwork
  have hfin : InformationTheory.klDiv (infiniteTranscriptLaw P seed tape)
      (infiniteTranscriptLaw Q seed tape) < ∞ :=
    hle.trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hwork)
  exact ⟨hfin, InformationTheory.klDiv_ne_top_iff.mp hfin.ne⟩

theorem measurable_infinite_observation {Seed Ω : Type}
    [MeasurableSpace Seed] [MeasurableSpace Ω]
    (seed : Ω → Seed) (tape : Ω → ProcessTape) (hs : Measurable seed)
    (ht : ∀ n b, MeasurableSet {ω | tape ω n = b}) :
    Measurable (fun ω => (seed ω, tape ω)) := by
  exact hs.prodMk (Measurable.of_eval fun n => measurable_to_countable' (ht n))

theorem observableKLBound_of_bound (hbound : InfiniteKLBoundStatement) :
    ObservableKLBoundStatement := by
  intro Seed Ω Z _ _ _ μ P Q _ _ _ m seed tape pol d η h observe
    hs ht hp ho hP hQ hh hd hη hdη hwork
  have hm := measurable_infinite_observation seed tape hs ht
  let IP := infiniteTranscriptLaw P seed tape
  let IQ := infiniteTranscriptLaw Q seed tape
  haveI : IsFiniteMeasure IP := by
    dsimp [IP, infiniteTranscriptLaw]
    infer_instance
  haveI : IsFiniteMeasure IQ := by
    dsimp [IQ, infiniteTranscriptLaw]
    infer_instance
  have hdata := InformationTheory.klDiv_map_le IP IQ ho
  rw [show IP.map observe = P.map (fun ω => observe (seed ω, tape ω)) by
    exact Measure.map_map ho hm,
    show IQ.map observe = Q.map (fun ω => observe (seed ω, tape ω)) by
    exact Measure.map_map ho hm] at hdata
  exact hdata.trans (hbound Seed Ω μ P Q m seed tape pol d η h hs ht hp hP hQ
    hh hd hη hdη hwork)

end ThresholdHC.Tier4
