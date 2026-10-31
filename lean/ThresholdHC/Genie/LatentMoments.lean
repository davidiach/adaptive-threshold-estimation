import ThresholdHC.Genie.LatentTape
import ThresholdHC.StoppingProgram.TapeMoments

/-! Signed and nonnegative moments of the actual latent-reference experiment. -/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace ThresholdHC.Genie
open ThresholdHC.Tier6 ThresholdHC.StoppingProgram ThresholdHC.CriticalEntropy
open ThresholdHC.ObservableSimulation ThresholdHC.Tier2

theorem latentReference_integral (μ : Measure Gap) [IsProbabilityMeasure μ] (q : SignLaw)
    (F : LatentState → ℝ) (hF : Measurable F) (hi : Integrable F (latentReference μ q)) :
    (∫ z, F z ∂latentReference μ q) =
      ∫ d, q.val d*F (d,true)+(1-q.val d)*F (d,false) ∂μ := by
  have hc : Integrable (fun z => F (latentSelector q z)) (μ.prod uniformUnitMeasure) :=
    (integrable_map_measure hF.aestronglyMeasurable (measurable_latentSelector q).aemeasurable).mp hi
  rw [latentReference,integral_map (measurable_latentSelector q).aemeasurable hF.aestronglyMeasurable,
    integral_prod _ hc]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun d => by
    have hm : Measurable (uniformCoinFlip (signUnit q d)) :=
      measurable_uniformCoinFlip.comp (measurable_const.prodMk measurable_id)
    change (∫ u, F (d,uniformCoinFlip (signUnit q d) u) ∂uniformUnitMeasure) = _
    rw [←integral_map hm.aemeasurable (measurable_of_countable (fun b : Bool => F (d,b))).aestronglyMeasurable,
      uniformCoinFlip_map,integral_bernoulliMeasure]
    rfl)

theorem latentTapeScore_secondMoment (μ : Measure Gap) [IsProbabilityMeasure μ]
    (Q : FourPriors) (hC : latentDivergence μ Q ≠ ⊤) :
    (∫⁻ z, ENNReal.ofReal ((latentTapeScore Q z)^2) ∂latentTapeLaw μ Q.variance) =
      latentDivergence μ Q := by
  rw [latentTapeLaw,lintegral_prod _ ((measurable_latentTapeScore Q).pow_const 2).ennreal_ofReal.aemeasurable]
  simp only [latentTapeScore,lintegral_const,measure_univ,mul_one]
  exact latentScore_secondMoment μ Q hC

theorem weighted_score (x y : ℝ) (hfin : perspective x y ≠ ⊤) : y*(x/y) = x := by
  by_cases hy : y = 0
  · have hx : x = 0 := by
      by_contra hx
      exact hfin (by rw [hy,perspective_nonzero_zero hx])
    simp [hy,hx]
  · field_simp

theorem uniform_gap_prefix_real (s : Bool) (d : Gap) (n : ℕ) (w : Fin n → Bool) :
    uniformTapeMeasure.real ((fun u => tapePrefix n (uniformCoinTape (gapParameter s d) u)) ⁻¹' {w}) =
      prefixLikelihood s n (wordHeads w) d := by
  have hm : Measurable (uniformCoinTape (gapParameter s d)) :=
    measurable_uniformCoinTape.comp (measurable_const.prodMk measurable_id)
  rw [←gap_tape_prefix_real s d n w,←uniformCoinTape_map]
  simp only [Measure.real]
  rw [Measure.map_apply hm ((measurable_prefix n) (measurableSet_singleton w))]
  rfl

theorem latent_prefix_integral (μ : Measure Gap) [IsProbabilityMeasure μ] (q : SignLaw)
    (n : ℕ) (w : Fin n → Bool) (F : LatentState → ℝ) (hF : Measurable F)
    (hi : Integrable F (latentReference μ q)) :
    (∫ z in observedPrefix latentObservedTape n ⁻¹' {w}, F z.1 ∂latentTapeLaw μ q) =
      ∫ d, q.val d*(prefixLikelihood true n (wordHeads w) d*F (d,true))+
        (1-q.val d)*(prefixLikelihood false n (wordHeads w) d*F (d,false)) ∂μ := by
  let E := observedPrefix latentObservedTape n ⁻¹' {w}
  have hX : Measurable (observedPrefix latentObservedTape n) :=
    (measurable_prefix n).comp measurable_latentObservedTape
  have hE : MeasurableSet E := hX (measurableSet_singleton w)
  have hFi : Integrable (fun z : LatentTapeState => F z.1) (latentTapeLaw μ q) :=
    measurePreserving_fst.integrable_comp_of_integrable hi
  have hI := hFi.indicator hE
  have hinner (z : LatentState) :
      (∫ u, E.indicator (fun y : LatentTapeState => F y.1) (z,u) ∂uniformTapeMeasure) =
        prefixLikelihood z.2 n (wordHeads w) z.1*F z := by
    change (∫ u, (observedPrefix latentObservedTape n ⁻¹' {w}).indicator
      (fun y : LatentTapeState => F y.1) (z,u) ∂uniformTapeMeasure) = _
    have he : (fun u => (observedPrefix latentObservedTape n ⁻¹' {w}).indicator
        (fun y : LatentTapeState => F y.1) (z,u)) =
        ((fun u => tapePrefix n (uniformCoinTape (gapParameter z.2 z.1) u)) ⁻¹' {w}).indicator
          (fun _ => F z) := rfl
    rw [he,integral_indicator_const]
    · rw [uniform_gap_prefix_real,smul_eq_mul]
    · exact ((measurable_prefix n).comp (measurable_uniformCoinTape.comp
        (measurable_const.prodMk measurable_id))) (measurableSet_singleton w)
  have hG : Measurable (fun z : LatentState => prefixLikelihood z.2 n (wordHeads w) z.1*F z) := by
    have he : (fun z : LatentState => prefixLikelihood z.2 n (wordHeads w) z.1) =
        fun z => if z.2 = true then prefixLikelihood true n (wordHeads w) z.1
          else prefixLikelihood false n (wordHeads w) z.1 := by
      funext z; cases z.2 <;> simp
    rw [show (fun z : LatentState => prefixLikelihood z.2 n (wordHeads w) z.1*F z) =
      (fun z => prefixLikelihood z.2 n (wordHeads w) z.1)*(F) by rfl]
    apply Measurable.mul _ hF
    rw [he]
    exact Measurable.ite (measurableSet_eq_fun measurable_snd measurable_const)
      ((measurable_prefixLikelihood true n (wordHeads w)).comp measurable_fst)
      ((measurable_prefixLikelihood false n (wordHeads w)).comp measurable_fst)
  have hGi : Integrable (fun z : LatentState => prefixLikelihood z.2 n (wordHeads w) z.1*F z)
      (latentReference μ q) := by
    simpa only [hinner] using hI.integral_prod_left
  rw [←integral_indicator hE]
  change (∫ z, E.indicator (fun y : LatentTapeState => F y.1) z ∂(latentReference μ q).prod uniformTapeMeasure) = _
  rw [integral_prod _ hI]
  simp_rw [hinner]
  exact latentReference_integral μ q _ hG hGi

end ThresholdHC.Genie
