import ThresholdHC.Genie.LatentScore
import ThresholdHC.Genie.TapeIdentification
import ThresholdHC.Genie.ObservationFiltration
import Mathlib.Probability.Martingale.Convergence

/-! The joint latent-state and iid tape experiment. Almost-sure parameter
identification makes the latent score measurable from the full observation
tape, so its finite-prefix conditional expectations converge almost surely. -/

noncomputable section
open MeasureTheory Filter
open scoped ENNReal Topology
namespace ThresholdHC.Genie
open ThresholdHC.Tier6 ThresholdHC.StoppingProgram ThresholdHC.CriticalEntropy
open ThresholdHC.ObservableSimulation

abbrev LatentTapeState := LatentState × (ℕ → ℝ)

def latentTapeLaw (μ : Measure Gap) (q : SignLaw) : Measure LatentTapeState :=
  (latentReference μ q).prod uniformTapeMeasure

instance latentTapeLaw_probability (μ : Measure Gap) [IsProbabilityMeasure μ] (q : SignLaw) :
    IsProbabilityMeasure (latentTapeLaw μ q) := by unfold latentTapeLaw; infer_instance

def latentObservedTape (z : LatentTapeState) : ℕ → Bool :=
  uniformCoinTape (gapParameter z.1.2 z.1.1) z.2

theorem measurable_latentObservedTape : Measurable latentObservedTape := by
  have hp : Measurable (fun z : LatentState => gapParameter z.2 z.1) :=
    measurable_latentParameter.subtype_mk
  exact measurable_uniformCoinTape.comp ((hp.comp measurable_fst).prodMk measurable_snd)

def latentTapeScore (Q : FourPriors) (z : LatentTapeState) : ℝ := latentScore Q z.1

theorem measurable_latentTapeScore (Q : FourPriors) : Measurable (latentTapeScore Q) :=
  (measurable_latentScore Q).comp measurable_fst

theorem latentTapeScore_integrable (μ : Measure Gap) [IsProbabilityMeasure μ]
    (Q : FourPriors) (hC : latentDivergence μ Q ≠ ⊤) :
    Integrable (latentTapeScore Q) (latentTapeLaw μ Q.variance) :=
  measurePreserving_fst.integrable_comp_of_integrable (latentScore_integrable μ Q hC)

theorem latentTape_parameter_ae (μ : Measure Gap) [IsProbabilityMeasure μ] (q : SignLaw) :
    ∀ᵐ z ∂latentTapeLaw μ q, tapeParameter (latentObservedTape z) = latentParameter z.1 := by
  apply (Measure.ae_prod_iff_ae_ae (measurableSet_eq_fun
    (measurable_tapeParameter.comp measurable_latentObservedTape)
    (measurable_latentParameter.comp measurable_fst))).mpr
  exact Filter.Eventually.of_forall (fun z => uniform_tapeParameter_ae (gapParameter z.2 z.1))

theorem latentTape_score_reconstruction (μ : Measure Gap) [IsProbabilityMeasure μ] (Q : FourPriors) :
    (fun z => parameterScore Q (tapeParameter (latentObservedTape z))) =ᵐ[latentTapeLaw μ Q.variance]
      latentTapeScore Q := by
  filter_upwards [latentTape_parameter_ae μ Q.variance] with z hz
  rw [hz,parameterScore_latent]
  rfl

theorem latent_score_posterior_tendsto (μ : Measure Gap) [IsProbabilityMeasure μ]
    (Q : FourPriors) (hC : latentDivergence μ Q ≠ ⊤) :
    let P := latentTapeLaw μ Q.variance
    let ℱ := observationFiltration latentObservedTape measurable_latentObservedTape
    ∀ᵐ z ∂P, Tendsto (fun N => (P[latentTapeScore Q | ℱ N]) z) atTop (𝓝 (latentTapeScore Q z)) := by
  intro P ℱ
  have hle : (⨆ n, ℱ n) ≤ (inferInstance : MeasurableSpace LatentTapeState) := iSup_le ℱ.le
  have hrep : StronglyMeasurable[⨆ n, ℱ n]
      (fun z => parameterScore Q (tapeParameter (latentObservedTape z))) :=
    ((measurable_parameterScore Q).comp (measurable_tapeParameter.comp
      (observedTape_measurable_iSup latentObservedTape measurable_latentObservedTape))).stronglyMeasurable
  have hae : AEStronglyMeasurable[⨆ n, ℱ n] (latentTapeScore Q) P :=
    hrep.aestronglyMeasurable.congr (latentTape_score_reconstruction μ Q)
  have he := condExp_of_aestronglyMeasurable' hle hae (latentTapeScore_integrable μ Q hC)
  have ht := tendsto_ae_condExp (ℱ := ℱ) (μ := P) (latentTapeScore Q)
  filter_upwards [he,ht] with z hz htz
  rwa [hz] at htz

end ThresholdHC.Genie
