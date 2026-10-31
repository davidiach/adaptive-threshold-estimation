import ThresholdHC.Genie.LatentMoments
import ThresholdHC.Genie.FinitePosterior
import ThresholdHC.Genie.RevealResidual
import ThresholdHC.StoppingProgram.WordFlow

/-! The finite-prefix posterior score has exactly the terminal information
in the count-flow program. -/

noncomputable section
open MeasureTheory
open scoped ENNReal BigOperators
namespace ThresholdHC.Genie
open ThresholdHC.Tier6 ThresholdHC.StoppingProgram ThresholdHC.CriticalEntropy
open ThresholdHC.ObservableSimulation ThresholdHC.Tier2

theorem latent_prefix_mass (μ : Measure Gap) [IsProbabilityMeasure μ] (q : SignLaw)
    (n : ℕ) (w : Fin n → Bool) :
    (latentTapeLaw μ q).real (observedPrefix latentObservedTape n ⁻¹' {w}) =
      prefixCoefficient μ q n (wordHeads w) := by
  simpa only [setIntegral_const,smul_eq_mul,mul_one,prefixCoefficient] using
    latent_prefix_integral μ q n w (fun _ => 1) measurable_const (integrable_const 1)

theorem latent_prefix_score (μ : Measure Gap) [IsProbabilityMeasure μ] (Q : FourPriors)
    (hC : latentDivergence μ Q ≠ ⊤) (n : ℕ) (w : Fin n → Bool) :
    (∫ z in observedPrefix latentObservedTape n ⁻¹' {w}, latentTapeScore Q z ∂latentTapeLaw μ Q.variance) =
      prefixCoefficient μ Q.high n (wordHeads w)-prefixCoefficient μ Q.low n (wordHeads w) := by
  rw [show latentTapeScore Q = fun z : LatentTapeState => latentScore Q z.1 from rfl,
    latent_prefix_integral μ Q.variance n w (latentScore Q) (measurable_latentScore Q)
      (latentScore_integrable μ Q hC)]
  unfold prefixCoefficient
  have hiH := prefixDensity_integrable μ Q.high n (wordHeads w)
  have hiL := prefixDensity_integrable μ Q.low n (wordHeads w)
  change Integrable (fun d => Q.high.val d*prefixLikelihood true n (wordHeads w) d+
    (1-Q.high.val d)*prefixLikelihood false n (wordHeads w) d) μ at hiH
  change Integrable (fun d => Q.low.val d*prefixLikelihood true n (wordHeads w) d+
    (1-Q.low.val d)*prefixLikelihood false n (wordHeads w) d) μ at hiL
  rw [←integral_sub hiH hiL]
  apply integral_congr_ae
  filter_upwards [finite_latent_perspectives_ae μ Q hC] with d hd
  have hpos := weighted_score (Q.high.val d-Q.low.val d) (Q.variance.val d) hd.1
  have hneg := weighted_score (Q.high.val d-Q.low.val d) (1-Q.variance.val d) hd.2
  simp only [latentScore,ite_true,Bool.false_eq_true,ite_false,neg_div]
  calc
    _ = prefixLikelihood true n (wordHeads w) d*(Q.variance.val d*((Q.high.val d-Q.low.val d)/Q.variance.val d))-
        prefixLikelihood false n (wordHeads w) d*((1-Q.variance.val d)*((Q.high.val d-Q.low.val d)/(1-Q.variance.val d))) := by ring
    _ = _ := by rw [hpos,hneg]; ring

theorem sum_words_by_heads_ennreal (n : ℕ) (F : ℕ → ℝ≥0∞) :
    (∑ w : Fin n → Bool, F (wordHeads w)) =
      ∑ k ∈ Finset.range (n+1), ENNReal.ofReal (n.choose k:ℝ)*F k := by
  induction n generalizing F with
  | zero => simp [wordHeads]
  | succ n ih =>
    have he := (Fin.snocEquiv (fun _ : Fin (n+1) => Bool)).sum_comp (fun w => F (wordHeads w))
    rw [←he,Fintype.sum_prod_type]
    simp only [Fintype.sum_bool,Fin.snocEquiv_apply,wordHeads_snoc,ite_true,
      Bool.false_eq_true,ite_false,add_zero]
    rw [ih (fun k => F (k+1)),ih F]
    simp only [ENNReal.ofReal_natCast]
    rw [add_comm]
    exact (Finset.sum_choose_succ_mul (fun i _ => F i) n).symm

theorem posterior_secondMoment_eq_terminal (μ : Measure Gap) [IsProbabilityMeasure μ]
    (Q : FourPriors) (hC : latentDivergence μ Q ≠ ⊤) (n : ℕ) :
    (∫⁻ z, ENNReal.ofReal ((((latentTapeLaw μ Q.variance)[latentTapeScore Q |
      observationFiltration latentObservedTape measurable_latentObservedTape n]) z)^2)
        ∂latentTapeLaw μ Q.variance) = terminalInformation μ Q n := by
  rw [observationFiltration_eq_comap]
  have hX : Measurable (observedPrefix latentObservedTape n) :=
    (measurable_prefix n).comp measurable_latentObservedTape
  rw [finite_posterior_secondMoment _ _ hX _ (latentTapeScore_integrable μ Q hC)]
  simp_rw [latent_prefix_mass,latent_prefix_score μ Q hC]
  exact sum_words_by_heads_ennreal n (prefixInformation μ Q n)

end ThresholdHC.Genie
