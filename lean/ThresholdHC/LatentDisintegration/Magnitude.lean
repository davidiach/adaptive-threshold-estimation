import ThresholdHC.LatentDisintegration.Specification

/-! The magnitude map and the magnitude law of `G_{μ,q}`. Every value of the
selector `mixtureParameter` is `1/2 ± d` for the gap `d` of its first
coordinate, so `gapOf` and `|· - 1/2|` read the gap back, and the push-forward
of `μ ⊗ uniform` is the first marginal `μ`. -/
noncomputable section
open MeasureTheory Set
namespace ThresholdHC.LatentDisintegration
open ThresholdHC.Tier6 ThresholdHC.CriticalEntropy ThresholdHC.ObservableSimulation
  ThresholdHC.SmoothDensity

theorem measurable_gapOf : Measurable gapOf := by
  apply Measurable.subtype_mk
  exact Measurable.ite (measurableSet_eq_fun measurable_subtype_coe measurable_const)
    measurable_const (measurable_subtype_coe.sub_const _).abs

/-- Off the null point `P = 1/2`, `gapOf p` is `|p - 1/2|`. -/
theorem gapOf_coe (p : unitInterval) (h : (p : ℝ) ≠ 1/2) :
    (gapOf p : ℝ) = |(p : ℝ) - 1/2| := by
  change (if (p : ℝ) = 1/2 then (1/2 : ℝ) else |(p : ℝ) - 1/2|) = _
  rw [ite_eq_right h]

theorem coe_gapParameter_true (d : Gap) : (gapParameter true d : ℝ) = 1/2 + d := by
  change (1/2 : ℝ) + (if true = true then (d : ℝ) else -(d : ℝ)) = _
  rw [ite_eq_left rfl]

theorem coe_gapParameter_false (d : Gap) : (gapParameter false d : ℝ) = 1/2 - d := by
  change (1/2 : ℝ) + (if false = true then (d : ℝ) else -(d : ℝ)) = _
  rw [ite_eq_right Bool.false_ne_true, sub_eq_add_neg]

theorem abs_gapParameter (s : Bool) (d : Gap) : |(gapParameter s d : ℝ) - 1/2| = d := by
  have hd := d.property.1
  cases s
  · rw [coe_gapParameter_false, show (1/2 : ℝ) - d - 1/2 = -d by ring, abs_neg,
      abs_of_pos hd]
  · rw [coe_gapParameter_true, show (1/2 : ℝ) + d - 1/2 = d by ring, abs_of_pos hd]

theorem gapParameter_ne_half (s : Bool) (d : Gap) : (gapParameter s d : ℝ) ≠ 1/2 := by
  have hd := d.property.1
  cases s
  · rw [coe_gapParameter_false]; linarith
  · rw [coe_gapParameter_true]; linarith

theorem gapOf_gapParameter (s : Bool) (d : Gap) : gapOf (gapParameter s d) = d :=
  Subtype.ext ((gapOf_coe _ (gapParameter_ne_half s d)).trans (abs_gapParameter s d))

theorem gapParameter_true_gapOf (p : unitInterval) (h : (1/2 : ℝ) < p) :
    gapParameter true (gapOf p) = p := by
  apply Subtype.ext
  rw [coe_gapParameter_true, gapOf_coe p h.ne', abs_of_pos (by linarith)]
  ring

theorem gapParameter_false_gapOf (p : unitInterval) (h : (p : ℝ) < 1/2) :
    gapParameter false (gapOf p) = p := by
  apply Subtype.ext
  rw [coe_gapParameter_false, gapOf_coe p h.ne, abs_of_neg (by linarith)]
  ring

theorem mixtureParameter_eq (q : SignLaw) (z : Gap × ℝ) :
    ∃ s : Bool, mixtureParameter (gapParameter false) (gapParameter true) (signUnit q) z =
      gapParameter s z.1 := by
  unfold mixtureParameter
  split_ifs
  · exact ⟨true, rfl⟩
  · exact ⟨false, rfl⟩

theorem measurable_latentMixture (q : SignLaw) :
    Measurable (mixtureParameter (gapParameter false) (gapParameter true) (signUnit q)) :=
  measurable_mixtureParameter _ _ _ (measurable_gapParameter false)
    (measurable_gapParameter true) (measurable_signUnit q)

theorem measurable_absHalf : Measurable (fun p : unitInterval => |(p : ℝ) - 1/2|) :=
  (measurable_subtype_coe.sub_const _).abs

/-- The latent law of a probability gap law is a probability law. -/
theorem latentLaw_probability (μ : Measure Gap) [IsProbabilityMeasure μ] (q : SignLaw) :
    IsProbabilityMeasure (latentLaw μ q) :=
  populationParameterLaw_probability μ _ _ _
    (measurable_gapParameter false) (measurable_gapParameter true) (measurable_signUnit q)

/-- `G_{μ,q}` has no atom at `1/2`, and `gapOf` pushes it forward to `μ`. -/
theorem latent_gapOf_magnitude (μ : Measure Gap) [IsProbabilityMeasure μ] (q : SignLaw) :
    (latentLaw μ q).map gapOf = μ ∧ latentLaw μ q {p : unitInterval | (p : ℝ) = 1/2} = 0 := by
  have hm := measurable_latentMixture q
  constructor
  · have hc : gapOf ∘ mixtureParameter (gapParameter false) (gapParameter true) (signUnit q) =
        Prod.fst := by
      funext z
      obtain ⟨s, hs⟩ := mixtureParameter_eq q z
      rw [Function.comp_apply, hs, gapOf_gapParameter]
    rw [latentLaw, populationParameterLaw, Measure.map_map measurable_gapOf hm, hc,
      Measure.map_fst_prod, measure_univ, one_smul]
  · have hs : MeasurableSet {p : unitInterval | (p : ℝ) = 1/2} :=
      measurableSet_eq_fun measurable_subtype_coe measurable_const
    have he : mixtureParameter (gapParameter false) (gapParameter true) (signUnit q) ⁻¹'
        {p : unitInterval | (p : ℝ) = 1/2} = ∅ := by
      ext z
      obtain ⟨s, hs⟩ := mixtureParameter_eq q z
      simp only [mem_preimage, mem_ofPred_eq, hs, mem_empty_iff_false, iff_false]
      exact gapParameter_ne_half s z.1
    rw [latentLaw, populationParameterLaw, Measure.map_apply hm hs, he, measure_empty]

/-- `|P - 1/2|` under `G_{μ,q}` has the law of the gap under `μ`. -/
theorem latent_magnitude_eq (μ : Measure Gap) [IsProbabilityMeasure μ] (q : SignLaw) :
    (latentLaw μ q).map (fun p : unitInterval => |(p : ℝ) - 1/2|) = μ.map Subtype.val := by
  have hm := measurable_latentMixture q
  have hc : (fun p : unitInterval => |(p : ℝ) - 1/2|) ∘
      mixtureParameter (gapParameter false) (gapParameter true) (signUnit q) =
        Subtype.val ∘ Prod.fst := by
    funext z
    obtain ⟨s, hs⟩ := mixtureParameter_eq q z
    rw [Function.comp_apply, hs, abs_gapParameter, Function.comp_apply]
  rw [latentLaw, populationParameterLaw, Measure.map_map measurable_absHalf hm, hc,
    ← Measure.map_map measurable_subtype_coe measurable_fst, Measure.map_fst_prod, measure_univ,
    one_smul]

end ThresholdHC.LatentDisintegration
