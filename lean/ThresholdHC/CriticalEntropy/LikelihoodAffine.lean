import ThresholdHC.CriticalEntropy.ObservationInformation
import ThresholdHC.CriticalEntropy.PopulationCompactness

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace ThresholdHC.CriticalEntropy

theorem wordLikelihood_real_bounds (p : unitInterval) (n k : ℕ) :
    0 ≤ (wordLikelihood p n k).toReal ∧ (wordLikelihood p n k).toReal ≤ 1 := by
  refine ⟨ENNReal.toReal_nonneg,?_⟩
  simpa using ENNReal.toReal_mono (by norm_num : (1 : ℝ≥0∞) ≠ ∞) (wordLikelihood_le_one p n k)

theorem wordLikelihood_real_memLp {D : Type} [MeasurableSpace D]
    (μ : Measure D) [IsProbabilityMeasure μ] (p : D → unitInterval) (hp : Measurable p)
    (n k : ℕ) : MemLp (fun d => (wordLikelihood (p d) n k).toReal) 2 μ := by
  have hm : Measurable (fun d => (wordLikelihood (p d) n k).toReal) := by
    unfold wordLikelihood
    fun_prop
  apply MemLp.of_bound hm.aestronglyMeasurable 1
  exact ae_of_all _ (fun d => by
    rw [Real.norm_eq_abs,abs_of_nonneg (wordLikelihood_real_bounds (p d) n k).1]
    exact (wordLikelihood_real_bounds (p d) n k).2)

theorem populationWordLikelihood_real {D : Type} [MeasurableSpace D]
    (μ : Measure D) [IsProbabilityMeasure μ] (p₀ p₁ q : D → unitInterval)
    (h₀ : Measurable p₀) (h₁ : Measurable p₁) (hq : Measurable q) (n k : ℕ) :
    (populationWordLikelihood μ p₀ p₁ q n k).toReal =
      ∫ d, (q d : ℝ)*(wordLikelihood (p₁ d) n k).toReal +
        (1-(q d : ℝ))*(wordLikelihood (p₀ d) n k).toReal ∂μ := by
  let F := fun d => ENNReal.ofReal (q d : ℝ)*wordLikelihood (p₁ d) n k +
    ENNReal.ofReal (1-(q d : ℝ))*wordLikelihood (p₀ d) n k
  have hm : Measurable F := by unfold F wordLikelihood; fun_prop
  have ht (d : D) : F d ≠ ∞ := by dsimp [F,wordLikelihood]; finiteness
  change (∫⁻ d, F d ∂μ).toReal = _
  rw [← integral_toReal hm.aemeasurable (ae_of_all _ (fun d => lt_top_iff_ne_top.mpr (ht d)))]
  apply integral_congr_ae
  apply ae_of_all
  intro d
  dsimp only [F]
  rw [ENNReal.toReal_add (by unfold wordLikelihood; finiteness) (by unfold wordLikelihood; finiteness),
    ENNReal.toReal_mul,ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (q d).property.1,
    ENNReal.toReal_ofReal (sub_nonneg.mpr (q d).property.2)]

/-- Every likelihood coordinate is an actual affine L2 moment of the sign law. -/
theorem populationWordLikelihood_affine_moment {D : Type} [MeasurableSpace D]
    (μ : Measure D) [IsProbabilityMeasure μ] (p₀ p₁ : D → unitInterval)
    (h₀ : Measurable p₀) (h₁ : Measurable p₁) (n k : ℕ) :
    ∃ (g : Lp ℝ 2 μ) (b : ℝ), ∀ q : D → unitInterval, Measurable q →
      (populationWordLikelihood μ p₀ p₁ q n k).toReal = (∫ d, (q d : ℝ)*g d ∂μ)+b := by
  let l₀ := fun d => (wordLikelihood (p₀ d) n k).toReal
  let l₁ := fun d => (wordLikelihood (p₁ d) n k).toReal
  have hl₀ : MemLp l₀ 2 μ := wordLikelihood_real_memLp μ p₀ h₀ n k
  have hl₁ : MemLp l₁ 2 μ := wordLikelihood_real_memLp μ p₁ h₁ n k
  have hdiff : MemLp (fun d => l₁ d-l₀ d) 2 μ := hl₁.sub hl₀
  let g := hdiff.toLp (fun d => l₁ d-l₀ d)
  refine ⟨g,∫ d, l₀ d ∂μ,?_⟩
  intro q hq
  have hqL : MemLp (fun d => (q d : ℝ)) 2 μ :=
    MemLp.of_bound (measurable_subtype_coe.comp hq).aestronglyMeasurable 1 (ae_of_all _ (fun d => by
      rw [Real.norm_eq_abs,abs_of_nonneg (q d).property.1]
      exact (q d).property.2))
  have hg : g =ᵐ[μ] (fun d => l₁ d-l₀ d) := hdiff.coeFn_toLp
  rw [populationWordLikelihood_real μ p₀ p₁ q h₀ h₁ hq n k]
  calc
    _ = ∫ d, (q d : ℝ)*(l₁ d-l₀ d)+l₀ d ∂μ := by
      apply integral_congr_ae
      exact ae_of_all _ (fun d => by dsimp [l₀,l₁]; ring)
    _ = (∫ d, (q d : ℝ)*(l₁ d-l₀ d) ∂μ)+(∫ d, l₀ d ∂μ) :=
      integral_add (hqL.integrable_mul hdiff) (hl₀.integrable (by norm_num))
    _ = _ := by
      congr 1
      exact integral_congr_ae (hg.symm.mono (fun d hd => congrArg (fun t : ℝ => (q d : ℝ)*t) hd))

theorem cappedStatisticLaw_real_mass {D R E : Type}
    [MeasurableSpace D] [MeasurableSpace R] [MeasurableSpace E]
    (μ : Measure D) [IsProbabilityMeasure μ] (ν : Measure R) [IsProbabilityMeasure ν]
    (p₀ p₁ q : D → unitInterval) (h₀ : Measurable p₀) (h₁ : Measurable p₁)
    (hq : Measurable q) (A : StoppedProcedure R E) (m : ℕ) (hcap : ∀ z, A.stop z ≤ m)
    (i : Fin (m+1) × Fin (m+1)) :
    (cappedStatisticLaw μ ν p₀ p₁ q A m).real {i} =
      (populationWordLikelihood μ p₀ p₁ q i.1.val i.2.val).toReal *
        ((stoppedReference ν A m).map (fun z => stoppedStatistic m z.2)).real {i} := by
  rw [measureReal_def,cappedStatisticLaw_density μ ν p₀ p₁ q h₀ h₁ hq A m hcap,
    withDensity_apply _ (measurableSet_singleton i),lintegral_singleton,ENNReal.toReal_mul]
  rfl

end ThresholdHC.CriticalEntropy
