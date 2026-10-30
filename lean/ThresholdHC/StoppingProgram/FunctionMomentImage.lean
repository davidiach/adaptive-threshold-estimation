import ThresholdHC.StoppingProgram.RareCompactness
import ThresholdHC.StoppingProgram.CompactMaximum
import ThresholdHC.RareAboveTwo.Nonvacuity

/-! Compact actual-prior moment images for arbitrary bounded measurable
functions, extending the polynomial/count-coordinate construction. -/

noncomputable section
open MeasureTheory Set

namespace ThresholdHC.StoppingProgram
open ThresholdHC.Tier6 (Gap SignLaw signMean)
open ThresholdHC.RareAboveTwo

def functionMomentImage {I : Type} (μ : Measure Gap) (ρ : ℝ) (f : I → Gap → ℝ)
    (b : I → ℝ) : Set (I → ℝ) :=
  {u | ∃ q : SignLaw, RarePrior μ ρ q ∧ ∀ i, u i = (∫ d, q.val d*f i d ∂μ)+b i}

theorem functionMomentImage_compact_convex {I : Type} (μ : Measure Gap) [IsProbabilityMeasure μ]
    (ρ : ℝ) (f : I → Gap → ℝ) (b : I → ℝ) (hf : ∀ i, MemLp (f i) 2 μ) :
    IsCompact (functionMomentImage μ ρ f b) ∧ Convex ℝ (functionMomentImage μ ρ f b) := by
  let g : I → Lp ℝ 2 μ := fun i => (hf i).toLp (f i)
  have he (q : SignLaw) (i : I) : (∫ d, q.val d*f i d ∂μ) = ∫ d, q.val d*g i d ∂μ := by
    apply integral_congr_ae
    filter_upwards [(hf i).coeFn_toLp] with d hd
    change q.val d*f i d = q.val d*((hf i).toLp (f i)) d
    rw [hd]
  have heq : functionMomentImage μ ρ f b = rareMomentSet μ ρ g b := by
    ext u
    simp only [functionMomentImage,rareMomentSet,he]
  rw [heq]
  exact rareMomentSet_compact_convex μ ρ g b

theorem functionMomentImage_nonempty {I : Type} (μ : Measure Gap) {ρ : ℝ} (hρ : 0 ≤ ρ)
    (f : I → Gap → ℝ) (b : I → ℝ) : (functionMomentImage μ ρ f b).Nonempty := by
  let q : SignLaw := ⟨fun _ => 0,measurable_const,fun _ => ⟨le_rfl,by norm_num⟩⟩
  refine ⟨b,q,?_,?_⟩
  · simpa [RarePrior,signMean,q] using hρ
  · intro i
    simp [q]

theorem integrable_prior_function (μ : Measure Gap) (q : SignLaw) {f : Gap → ℝ}
    (hf : Integrable f μ) : Integrable (fun d => q.val d*f d) μ := by
  apply hf.bdd_mul q.property.1.aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun d => by
    simpa only [Real.norm_eq_abs,abs_of_nonneg (q.property.2 d).1] using (q.property.2 d).2)

def rareFunctional (μ : Measure Gap) (ρ : ℝ) (f : Gap → ℝ) : ℝ :=
  compactMaximum (functionMomentImage μ ρ (fun _ : Unit => f) (fun _ => 0)) (fun u => u ())

theorem rareFunctional_attained (μ : Measure Gap) [IsProbabilityMeasure μ]
    {ρ : ℝ} (hρ : 0 ≤ ρ) (f : Gap → ℝ) (hf : MemLp f 2 μ) :
    ∃ q : SignLaw, RarePrior μ ρ q ∧ rareFunctional μ ρ f = ∫ d, q.val d*f d ∂μ := by
  obtain ⟨u,hu,he⟩ := compactMaximum_attained _ (functionMomentImage_nonempty μ hρ _ _)
    (functionMomentImage_compact_convex μ ρ (fun _ : Unit => f) (fun _ => 0) (fun _ => hf)).1
    (fun u => u ()) (continuous_apply ()).continuousOn
  obtain ⟨q,hq,hu⟩ := hu
  refine ⟨q,hq,?_⟩
  change compactMaximum _ _ = _
  rw [he,hu (),add_zero]

theorem prior_function_le_rareFunctional (μ : Measure Gap) [IsProbabilityMeasure μ]
    {ρ : ℝ} (f : Gap → ℝ) (hf : MemLp f 2 μ) (q : SignLaw) (hq : RarePrior μ ρ q) :
    (∫ d, q.val d*f d ∂μ) ≤ rareFunctional μ ρ f := by
  have hu : (fun _ : Unit => ∫ d, q.val d*f d ∂μ) ∈ functionMomentImage μ ρ (fun _ : Unit => f) (fun _ => 0) :=
    ⟨q,hq,fun _ => by simp⟩
  exact le_compactMaximum _
    (functionMomentImage_compact_convex μ ρ (fun _ : Unit => f) (fun _ => 0) (fun _ => hf)).1
    (fun u => u ()) (continuous_apply ()).continuousOn hu

end ThresholdHC.StoppingProgram
