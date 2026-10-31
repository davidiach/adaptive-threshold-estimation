import ThresholdHC.Genie.LatentPrefix
import ThresholdHC.Genie.CapLimits

/-! Finite latent divergence makes the posterior second moments exhaustive.
The reveal residual vanishes, and the genie information converges to the
ordinary infinite-cap information. -/

noncomputable section
open MeasureTheory Filter
open scoped ENNReal Topology
namespace ThresholdHC.Genie
open ThresholdHC.Tier6 ThresholdHC.StoppingProgram

theorem terminalInformation_le_latent (μ : Measure Gap) [IsFiniteMeasure μ]
    (Q : FourPriors) (n : ℕ) : terminalInformation μ Q n ≤ latentDivergence μ Q := by
  rw [←revealResidual_add_terminal μ Q n]
  exact le_add_left le_rfl

theorem terminalInformation_tendsto (μ : Measure Gap) [IsProbabilityMeasure μ]
    (Q : FourPriors) (hC : latentDivergence μ Q ≠ ⊤) :
    Tendsto (terminalInformation μ Q) atTop (𝓝 (latentDivergence μ Q)) := by
  let P := latentTapeLaw μ Q.variance
  let ℱ := observationFiltration latentObservedTape measurable_latentObservedTape
  let f (n : ℕ) (z : LatentTapeState) := ENNReal.ofReal (((P[latentTapeScore Q | ℱ n]) z)^2)
  have hf (n : ℕ) : Measurable (f n) :=
    (((stronglyMeasurable_condExp (μ := P) (f := latentTapeScore Q) (m := ℱ n)).mono
      (ℱ.le n)).measurable.pow_const 2).ennreal_ofReal
  have he (n : ℕ) : (∫⁻ z, f n z ∂P) = terminalInformation μ Q n :=
    posterior_secondMoment_eq_terminal μ Q hC n
  have ha : ∀ᵐ z ∂P, Tendsto (fun n => f n z) atTop (𝓝 (ENNReal.ofReal ((latentTapeScore Q z)^2))) := by
    filter_upwards [latent_score_posterior_tendsto μ Q hC] with z hz
    exact ENNReal.continuous_ofReal.continuousAt.tendsto.comp (hz.pow 2)
  have hlo : latentDivergence μ Q ≤ liminf (terminalInformation μ Q) atTop := by
    calc
      _ = ∫⁻ z, ENNReal.ofReal ((latentTapeScore Q z)^2) ∂P := (latentTapeScore_secondMoment μ Q hC).symm
      _ = ∫⁻ z, liminf (fun n => f n z) atTop ∂P :=
        lintegral_congr_ae (ha.mono (fun _ h => h.liminf_eq.symm))
      _ ≤ liminf (fun n => ∫⁻ z, f n z ∂P) atTop := lintegral_liminf_le hf
      _ = _ := by simp only [he]
  apply tendsto_of_le_liminf_of_limsup_le hlo
  exact limsup_le_of_le (by isBoundedDefault)
    (Eventually.of_forall (terminalInformation_le_latent μ Q))

theorem revealResidual_tendsto_zero (μ : Measure Gap) [IsProbabilityMeasure μ]
    (Q : FourPriors) (hC : latentDivergence μ Q ≠ ⊤) :
    Tendsto (revealResidual μ Q) atTop (𝓝 0) := by
  have h := (ENNReal.continuous_sub_left hC).continuousAt.tendsto.comp
    (terminalInformation_tendsto μ Q hC)
  simpa only [Function.comp_def,tsub_self,←revealResidual_eq_sub μ Q hC] using h

theorem genieInformationRatio_tendsto (μ : Measure Gap) [IsProbabilityMeasure μ]
    (Q : FourPriors) (hC : latentDivergence μ Q ≠ ⊤) :
    Tendsto (fun n : ℕ => genieInformationRatio μ (n+1) Q) atTop
      (𝓝 (infiniteInformationRatio μ Q)) := by
  have hr := (revealResidual_tendsto_zero μ Q hC).comp (tendsto_add_atTop_nat 1)
  have hi := informationRatio_tendsto μ Q
  have hu : Tendsto (fun n : ℕ => informationRatio μ (n+1) Q+revealResidual μ Q (n+1)) atTop
      (𝓝 (infiniteInformationRatio μ Q)) := by simpa using hi.add hr
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le hi hu
    (fun n => informationRatio_le_genie μ (n+1) Q)
    (fun n => genieInformationRatio_le_add_residual μ (n+1) Q)

end ThresholdHC.Genie
