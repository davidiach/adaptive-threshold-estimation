import ThresholdHC.EntropyTailQuantile.EntropyMoment
import ThresholdHC.EntropyTailAssembly.BandWeights

/-! Finite-band approximation for every selected measure of finite entropy.
The discarded inverse moment vanishes. Entropy monotonicity suffices; no
entropy-continuity assumption or finite moment of the population is used. -/

noncomputable section
open MeasureTheory Set Real Filter
open scoped ENNReal Topology

namespace ThresholdHC.EntropyTailAssembly
open ThresholdHC.Tier6 ThresholdHC.EntropyTailQuantile

theorem inverseSquare_integrable_of_entropy (σ : Measure Gap) [IsFiniteMeasure σ]
    (hΓ : measureCostEntropy σ < ⊤) : Integrable (fun d : Gap => (d:ℝ)⁻¹^2) σ := by
  refine ⟨(show Measurable (fun d : Gap => (d:ℝ)⁻¹^2) by fun_prop).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (ae_of_all _ (fun d : Gap => sq_nonneg ((d:ℝ)⁻¹)))]
  exact (inverseSquare_lintegral_le_entropy σ).trans_lt hΓ

theorem inverse_integrable_of_entropy (σ : Measure Gap) [IsFiniteMeasure σ]
    (hΓ : measureCostEntropy σ < ⊤) : Integrable (fun d : Gap => (d:ℝ)⁻¹) σ := by
  apply (inverseSquare_integrable_of_entropy σ hΓ).mono'
    (show AEStronglyMeasurable (fun d : Gap => (d:ℝ)⁻¹) σ by fun_prop)
  apply ae_of_all
  intro d
  have hd : 1 ≤ (d:ℝ)⁻¹ := (one_le_inv₀ d.property.1).mpr (by linarith [d.property.2])
  rw [Real.norm_of_nonneg (inv_nonneg.mpr d.property.1.le)]
  nlinarith

def selectedTruncation (σ : Measure Gap) (n : ℕ) : Measure Gap :=
  σ.restrict {d : Gap | bandEdge n ≤ (d:ℝ)}

def selectedRemainder (σ : Measure Gap) (n : ℕ) : Measure Gap :=
  σ.restrict {d : Gap | (d:ℝ) < bandEdge n}

theorem selectedTruncation_add_remainder (σ : Measure Gap) (n : ℕ) :
    selectedTruncation σ n + selectedRemainder σ n = σ := by
  have he : {d : Gap | (d:ℝ) < bandEdge n} = {d : Gap | bandEdge n ≤ (d:ℝ)}ᶜ := by
    ext d
    simp
  unfold selectedTruncation selectedRemainder
  rw [he]
  exact Measure.restrict_add_restrict_compl (measurableSet_le measurable_const measurable_subtype_coe)

theorem selectedTruncation_le (σ : Measure Gap) (n : ℕ) : selectedTruncation σ n ≤ σ :=
  Measure.restrict_le_self

theorem selectedRemainder_le (σ : Measure Gap) (n : ℕ) : selectedRemainder σ n ≤ σ :=
  Measure.restrict_le_self

instance selectedTruncation_finite (σ : Measure Gap) [IsFiniteMeasure σ] (n : ℕ) :
    IsFiniteMeasure (selectedTruncation σ n) := isFiniteMeasure_of_le σ (selectedTruncation_le σ n)

instance selectedRemainder_finite (σ : Measure Gap) [IsFiniteMeasure σ] (n : ℕ) :
    IsFiniteMeasure (selectedRemainder σ n) := isFiniteMeasure_of_le σ (selectedRemainder_le σ n)

theorem selectedTruncation_support (σ : Measure Gap) (n : ℕ) :
    ∀ᵐ d : Gap ∂selectedTruncation σ n, bandEdge n ≤ (d:ℝ) :=
  ae_restrict_mem (measurableSet_le measurable_const measurable_subtype_coe)

theorem selectedTruncation_entropy_le (σ : Measure Gap) [IsFiniteMeasure σ] (n : ℕ) :
    measureCostEntropy (selectedTruncation σ n) ≤ measureCostEntropy σ :=
  measureCostEntropy_mono (selectedTruncation_le σ n)

theorem selectedTruncation_entropy_finite (σ : Measure Gap) [IsFiniteMeasure σ] (n : ℕ) :
    measureCostEntropy (selectedTruncation σ n) < ⊤ :=
  measureCostEntropy_lt_top_of_support _ (bandEdge_pos n) (selectedTruncation_support σ n)

theorem bandEdge_tendsto_zero : Tendsto bandEdge atTop (𝓝 0) := by
  change Tendsto (fun n : ℕ => (2:ℝ)⁻¹^(n+1)) atTop (𝓝 0)
  have h := (tendsto_pow_atTop_nhds_zero_of_lt_one
    (by norm_num : (0:ℝ) ≤ (2:ℝ)⁻¹) (by norm_num : (2:ℝ)⁻¹ < 1)).mul_const (2:ℝ)⁻¹
  simpa only [pow_succ, zero_mul] using h

theorem selectedRemainder_inverse_tendsto (σ : Measure Gap) [IsFiniteMeasure σ]
    (hΓ : measureCostEntropy σ < ⊤) :
    Tendsto (fun n => ∫ d : Gap, (d:ℝ)⁻¹ ∂selectedRemainder σ n) atTop (𝓝 0) := by
  let F := fun n => ({d : Gap | (d:ℝ) < bandEdge n}).indicator (fun d : Gap => (d:ℝ)⁻¹)
  have hm (n : ℕ) : Measurable (F n) :=
    (show Measurable (fun d : Gap => (d:ℝ)⁻¹) by fun_prop).indicator
      (measurableSet_lt measurable_subtype_coe measurable_const)
  have ht (d : Gap) : Tendsto (fun n => F n d) atTop (𝓝 0) := by
    have he := bandEdge_tendsto_zero.eventually (gt_mem_nhds d.property.1)
    apply tendsto_congr' (he.mono (fun n hn => show F n d = (0:ℝ) by
      simp [F, not_lt_of_ge hn.le])) |>.mpr
    exact tendsto_const_nhds
  have h := tendsto_integral_of_dominated_convergence (μ := σ) (fun d : Gap => (d:ℝ)⁻¹)
    (F := F) (f := fun _ => (0:ℝ)) (fun n => (hm n).aestronglyMeasurable)
    (inverse_integrable_of_entropy σ hΓ)
    (fun n => ae_of_all _ (fun d => by
      by_cases hd : (d:ℝ) < bandEdge n
      · simp [F, hd, Real.norm_of_nonneg (inv_nonneg.mpr d.property.1.le)]
      · simp [F, hd, inv_nonneg.mpr d.property.1.le]))
    (ae_of_all _ ht)
  have he (n : ℕ) : (∫ d : Gap, F n d ∂σ) = ∫ d : Gap, (d:ℝ)⁻¹ ∂selectedRemainder σ n :=
    integral_indicator (measurableSet_lt measurable_subtype_coe measurable_const)
  simpa only [he, integral_zero] using h

end ThresholdHC.EntropyTailAssembly
