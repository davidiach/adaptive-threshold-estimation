import ThresholdHC.NestedAssumptions.Binary
import ThresholdHC.ContinuousObserved.Density

/-!
# Every model of the nested-simulation class satisfies the transcribed assumptions

For a model `p` of the class, the normalized absolute conditional mean is
`normalizedGap` of the half magnitude `D(U)`, whose law is `4 • Leb` on `(0, 1/4]`.
Its law therefore has the explicit density `normalizedDensity ≤ 2`. Since
`D(U) ≤ 1/4` almost surely, the standardized conditional moments are at most
`3^(q/2)` almost surely.
-/

noncomputable section
namespace ThresholdHC.NestedAssumptions
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
open ThresholdHC.Tier6 ThresholdHC.ObservableSimulation ThresholdHC.ContinuousObserved

theorem measurable_halfMagnitude {p : unitInterval → unitInterval} (hp : Measurable p) :
    Measurable (fun u => |condMean (binaryLaw p) u| / 2) := by
  have he : (fun u => |condMean (binaryLaw p) u| / 2) = (fun u => |2 * (p u : ℝ) - 1| / 2) := by
    funext u
    rw [condMean_binaryLaw]
  rw [he]
  exact ((measurable_const.mul (measurable_subtype_coe.comp hp)).sub_const 1).abs.div_const 2

theorem normalizedMean_comp (p : unitInterval → unitInterval) :
    normalizedMean (binaryLaw p) = normalizedGap ∘ (fun u => |condMean (binaryLaw p) u| / 2) := by
  funext u
  exact normalizedMean_binaryLaw p u

theorem measurable_normalizedMean {p : unitInterval → unitInterval} (hp : Measurable p) :
    Measurable (normalizedMean (binaryLaw p)) := by
  rw [normalizedMean_comp]
  exact measurable_normalizedGap.comp (measurable_halfMagnitude hp)

theorem nested_density {p : unitInterval → unitInterval} (hp : NestedModel p) :
    volume.map (normalizedMean (binaryLaw p)) =
      volume.withDensity (fun z => ENNReal.ofReal (normalizedDensity z)) := by
  rw [normalizedMean_comp, ← Measure.map_map measurable_normalizedGap
    (measurable_halfMagnitude hp.1), hp.2, ← uniformGaps_real_law,
    Measure.map_map measurable_normalizedGap measurable_subtype_coe]
  exact normalizedGap_density

theorem nested_bounded_density {p : unitInterval → unitInterval} (hp : NestedModel p)
    {δ₀ : ℝ} (hδ : 0 < δ₀) : GHABoundedDensity volume (binaryLaw p) 2 δ₀ := by
  refine ⟨hδ, (measurable_normalizedMean hp.1).aemeasurable,
    fun z => ENNReal.ofReal (normalizedDensity z), measurable_normalizedDensity.ennreal_ofReal,
    nested_density hp, ?_⟩
  intro z _
  exact ENNReal.ofReal_le_ofReal (normalizedDensity_bounds z).2

theorem nested_halfMagnitude_ae {p : unitInterval → unitInterval} (hp : NestedModel p) :
    ∀ᵐ u, |condMean (binaryLaw p) u| / 2 ≤ 1 / 4 := by
  have hs : MeasurableSet {x : ℝ | x ≤ 1 / 4} := measurableSet_Iic
  apply (ae_map_iff (measurable_halfMagnitude hp.1).aemeasurable hs).mp
  rw [hp.2]
  apply (Measure.ae_ennreal_smul_measure_iff (by norm_num)).mpr
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
  exact hx.2

theorem nested_moment {p : unitInterval → unitInterval} (hp : NestedModel p)
    {q : ℝ} (hq : 2 < q) : GHAStandardizedMoment volume (binaryLaw p) q ((3 : ℝ) ^ (q / 2)) := by
  refine ⟨hq, ?_⟩
  filter_upwards [nested_halfMagnitude_ae hp] with u hu
  exact ⟨inferInstance, binaryLaw_moment p u hu (by linarith)⟩

end ThresholdHC.NestedAssumptions
