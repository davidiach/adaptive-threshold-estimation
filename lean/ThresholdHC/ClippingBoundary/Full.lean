import ThresholdHC.ClippingBoundary.Uniform
import ThresholdHC.ClippingBoundary.NoisyEstimator

/-! The clipping-boundary note
(`research/2026-10-27-nonlinear-population/audit/CLIPPING_BOUNDARY.tex`).

`kurtosis_transfer` and `kurtosis_rms` are the bounded-kurtosis transfer in
squared and RMS form (`Kurtosis.lean`), and `uniform_clipped_floor` is its
uniform corollary over the rare sign laws of the original experiment
(`Uniform.lean`). `noise_counterexample` is the proposition that no
unrestricted variance transfer exists, in abstract form, and `noisy_estimator`
is the same construction in the original experiment together with the
transfer of the uniform properties that stand in for the inherited additive
class. Both are assembled from the
unbundled component lemmas of `Noise.lean` and `NoisyEstimator.lean`. -/
noncomputable section
namespace ThresholdHC.ClippingBoundary
open MeasureTheory
open ThresholdHC.Tier6 ThresholdHC.RareAboveTwo ThresholdHC.RobustContinuation

/-- Proposition (a bounded-kurtosis transfer), squared form. -/
theorem kurtosis_transfer : KurtosisTransferStatement :=
  fun _ _ _ _ F θ ρ K hF hmean hθ0 hθρ hK h4 =>
    clipped_squared_floor F θ ρ K hF hmean hθ0 hθρ hK h4

/-- Proposition (a bounded-kurtosis transfer), RMS form `min(ρ,σ)/(16K)`. -/
theorem kurtosis_rms : KurtosisRMSStatement :=
  fun _ _ _ _ F θ ρ K hF hmean hθ0 hθρ hK h4 =>
    clipped_rms_floor F θ ρ K hF hmean hθ0 hθρ hK h4

/-- The uniform clipped floor over the rare sign laws. -/
theorem uniform_clipped_floor : UniformClippedFloorStatement := by
  intro R _ μ _ A ρ K hK hprem
  rw [mul_min_iSup_rpow]
  refine iSup_le fun q => ?_
  rw [mul_min_iSup_rpow]
  refine iSup_le fun hq => ?_
  obtain ⟨h4mem, hmean, h4⟩ := hprem q hq
  exact le_iSup₂_of_le (f := fun (q : SignLaw) (_ : RarePrior μ ρ q) =>
    rootMeanRisk (experimentLaw μ (clippedEstimator A ρ) q)
      (populationOutput (clippedEstimator A ρ)) (signMean μ q.val)) q hq
    (rare_term_floor μ A hK q hq h4mem hmean h4)

/-- Proposition (why there is no unrestricted variance transfer), abstract form. -/
theorem noise_counterexample : NoiseCounterexampleStatement := by
  intro Ω _ P _ F₀ θ ρ ε M hF hmean hθ0 hθρ h0 h1
  exact ⟨seedNoise_probability M h0 h1,
    (noisy_integral M h0 h1 (hF.integrable (by norm_num))).trans hmean,
    noisy_variance M h0 h1 hF,
    noisy_clip_risk M h0 hF.aestronglyMeasurable.aemeasurable hθ0 hθρ⟩

/-- The noise counterexample in the original experiment, with the transfer of
the uniform unbiasedness, budget and variance-bound properties. -/
theorem noisy_estimator : NoisyEstimatorStatement := by
  intro R _ μ _ A ε M h0 h1
  refine ⟨noisyEstimator A M h0 h1, rfl, fun u => rfl, fun z => rfl,
    fun q => ⟨noisy_expectedWork μ A M h0 h1 q, noisy_mean μ A M h0 h1 q,
      noisy_variance_eq μ A M h0 h1 q,
      fun θ ρ hθ0 hθρ => noisy_clip_squaredRisk μ A M h0 h1 q hθ0 hθρ⟩, ?_, ?_, ?_⟩
  · intro hU q
    obtain ⟨hi, hm⟩ := hU q
    obtain ⟨hi', hm'⟩ := noisy_mean μ A M h0 h1 q hi
    exact ⟨hi', hm'.trans hm⟩
  · intro W
    exact forall_congr' fun q => by rw [noisy_expectedWork μ A M h0 h1 q]
  · intro V hV hB q
    have hfin : ProbabilityTheory.evariance (populationOutput A) (experimentLaw μ A q) < ⊤ :=
      (hB q).trans_lt ENNReal.ofReal_lt_top
    have hmem : MemLp (populationOutput A) 2 (experimentLaw μ A q) :=
      (ProbabilityTheory.evariance_lt_top_iff_memLp
        (measurable_populationOutput A).aestronglyMeasurable).1 hfin
    have hmem' := noisy_memLp_two μ A M h0 h1 q hmem
    have hεM : 0 ≤ ε * M ^ 2 := mul_nonneg h0 (sq_nonneg M)
    rw [← ProbabilityTheory.ofReal_variance hmem', noisy_variance_eq μ A M h0 h1 q hmem,
      ENNReal.ofReal_add (ProbabilityTheory.variance_nonneg _ _) hεM,
      ProbabilityTheory.ofReal_variance hmem, ENNReal.ofReal_add hV hεM]
    exact add_le_add (hB q) le_rfl

end ThresholdHC.ClippingBoundary
