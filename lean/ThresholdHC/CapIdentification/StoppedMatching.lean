import ThresholdHC.CapIdentification.CountMatching
import ThresholdHC.ObservableSimulation.OriginalExperiment
import ThresholdHC.CriticalEntropy.CappedObservation

/-! Moment matching gives equality of the actual seed-and-stopped-word law
for every independently randomized one-unit procedure with the given cap. -/

noncomputable section
open MeasureTheory
open scoped ENNReal

namespace ThresholdHC.CapIdentification
open ThresholdHC.Tier6 (Gap SignLaw)
open ThresholdHC.StoppingProgram ThresholdHC.CriticalEntropy ThresholdHC.ObservableSimulation

theorem gap_wordLikelihood (s : Bool) (d : Gap) (n k : ℕ) :
    wordLikelihood (gapParameter s d) n k = ENNReal.ofReal (prefixLikelihood s n k d) := by
  cases s <;> simp only [wordLikelihood,gapParameter,prefixLikelihood,
    Bool.false_eq_true,ite_false,ite_true]
  · congr 1
    rw [show 1/2+ -(d:ℝ) = 1/2-(d:ℝ) by ring,
      show 1-(1/2-(d:ℝ)) = 1/2+(d:ℝ) by ring]
  · congr 1
    rw [show 1-(1/2+(d:ℝ)) = 1/2-(d:ℝ) by ring]

theorem original_wordLikelihood_integral (μ : Measure Gap) [IsFiniteMeasure μ]
    (q : SignLaw) (n k : ℕ) :
    populationWordLikelihood μ (gapParameter false) (gapParameter true) (signUnit q) n k =
      ENNReal.ofReal (∫ d, q.val d*prefixLikelihood true n k d+
        (1-q.val d)*prefixLikelihood false n k d ∂μ) := by
  have hi : Integrable (fun d => q.val d*prefixLikelihood true n k d+
      (1-q.val d)*prefixLikelihood false n k d) μ := by
    convert (integrable_weighted_prefix μ q true n k).add
      ((integrable_prefixLikelihood μ false n k).sub (integrable_weighted_prefix μ q false n k)) using 1
    ext d
    simp only [Pi.add_apply,Pi.sub_apply]
    ring
  have hnonneg (d : Gap) : 0 ≤ q.val d*prefixLikelihood true n k d+
      (1-q.val d)*prefixLikelihood false n k d :=
    add_nonneg (mul_nonneg (q.property.2 d).1 (prefixLikelihood_nonneg true n k d))
      (mul_nonneg (sub_nonneg.mpr (q.property.2 d).2) (prefixLikelihood_nonneg false n k d))
  rw [ofReal_integral_eq_lintegral_ofReal hi (Filter.Eventually.of_forall hnonneg)]
  unfold populationWordLikelihood
  apply lintegral_congr
  intro d
  rw [gap_wordLikelihood,gap_wordLikelihood,ENNReal.ofReal_add
    (mul_nonneg (q.property.2 d).1 (prefixLikelihood_nonneg true n k d))
    (mul_nonneg (sub_nonneg.mpr (q.property.2 d).2) (prefixLikelihood_nonneg false n k d)),
    ENNReal.ofReal_mul (q.property.2 d).1,
    ENNReal.ofReal_mul (sub_nonneg.mpr (q.property.2 d).2)]
  rfl

theorem wordLikelihood_eq_of_count_match (μ : Measure Gap) [IsFiniteMeasure μ]
    (qH qL : SignLaw) (N : ℕ) (h : CountMatch μ qH qL N)
    (n k : ℕ) (hn : n ≤ N) (hk : k ≤ n) :
    populationWordLikelihood μ (gapParameter false) (gapParameter true) (signUnit qH) n k =
      populationWordLikelihood μ (gapParameter false) (gapParameter true) (signUnit qL) n k := by
  have hm := h ⟨⟨n,by omega⟩,⟨k,by change k < n+1; omega⟩⟩
  have hc : (n.choose k:ℝ) ≠ 0 := by exact_mod_cast (Nat.choose_pos hk).ne'
  unfold countCoefficient at hm
  have hi := mul_left_cancel₀ hc hm
  rw [original_wordLikelihood_integral,original_wordLikelihood_integral,hi]

theorem stopped_law_eq_of_odd_moments {R E : Type} [MeasurableSpace R] [MeasurableSpace E]
    (μ : Measure Gap) [IsProbabilityMeasure μ] (ν : Measure R) [IsProbabilityMeasure ν]
    (qH qL : SignLaw) (N : ℕ) (h : OddMomentMatch μ qH qL N)
    (A : StoppedProcedure R E) (hcap : ∀ z, A.stop z ≤ N) :
    cappedTranscriptLaw μ ν (gapParameter false) (gapParameter true) (signUnit qH) A N =
      cappedTranscriptLaw μ ν (gapParameter false) (gapParameter true) (signUnit qL) A N := by
  rw [cappedTranscriptLaw_density μ ν _ _ _ (measurable_gapParameter false)
      (measurable_gapParameter true) (measurable_signUnit qH) A N hcap,
    cappedTranscriptLaw_density μ ν _ _ _ (measurable_gapParameter false)
      (measurable_gapParameter true) (measurable_signUnit qL) A N hcap]
  congr 1
  funext z
  apply wordLikelihood_eq_of_count_match μ qH qL N ((odd_moments_iff_count_match μ qH qL N).mp h)
  · have hn := z.2.1.isLt
    omega
  · unfold wordHeads
    simpa only [Finset.card_univ,Fintype.card_fin] using
      Finset.card_filter_le (s := Finset.univ) (fun i => z.2.2 i = true)

end ThresholdHC.CapIdentification
