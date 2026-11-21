import ThresholdHC.LatentDisintegration.Magnitude

/-! The converse: a law `G` of `P` with no atom at `1/2` is `G_{μ,q}` for
`μ = L(gapOf P)`. Split `G` into its parts on `P > 1/2` and `P < 1/2` and push
both forward by `gapOf`: `μ = ν₊ + ν₋`. The sign law is the Radon-Nikodym
density `q = dν₊/dμ`, clipped at `1` (it is at most `1` almost everywhere,
since `ν₊ ≤ μ`). For a bounded test `F`, with `F± = F(1/2 ± d)`,
`∫ q F₊ + (1 - q) F₋ dμ = ∫ F₊ dν₊ + ∫ F₋ dν₋ = ∫ F dG`. -/
noncomputable section
open MeasureTheory Set
namespace ThresholdHC.LatentDisintegration
open ThresholdHC.Tier6 ThresholdHC.CriticalEntropy ThresholdHC.ObservableSimulation
  ThresholdHC.SmoothDensity

/-- A bounded measurable function times a `[0,1]`-valued one is integrable. -/
theorem integrable_unit_mul {X : Type} [MeasurableSpace X] (ν : Measure X) [IsFiniteMeasure ν]
    (r f : X → ℝ) (hr : Measurable r) (hr1 : ∀ x, 0 ≤ r x ∧ r x ≤ 1) (hf : Measurable f)
    (C : ℝ) (hb : ∀ x, |f x| ≤ C) : Integrable (fun x => r x * f x) ν := by
  refine ThresholdHC.Tier5.integrable_of_abs_bound ν _ (hr.mul hf) C (fun x => ?_)
  rw [abs_mul, abs_of_nonneg (hr1 x).1]
  calc r x * |f x| ≤ 1 * C := mul_le_mul (hr1 x).2 (hb x) (abs_nonneg _) zero_le_one
    _ = C := one_mul C

theorem exists_latentLaw_eq (G : Measure unitInterval) [IsProbabilityMeasure G]
    (hG : G {p : unitInterval | (p : ℝ) = 1/2} = 0) :
    ∃ q : SignLaw, latentLaw (G.map gapOf) q = G := by
  obtain ⟨Sp, hSpdef⟩ : ∃ S : Set unitInterval, S = {p : unitInterval | (1/2 : ℝ) < p} :=
    ⟨_, rfl⟩
  obtain ⟨Sm, hSmdef⟩ : ∃ S : Set unitInterval, S = {p : unitInterval | (p : ℝ) < 1/2} :=
    ⟨_, rfl⟩
  have hSp : MeasurableSet Sp := hSpdef ▸ measurableSet_lt measurable_const measurable_subtype_coe
  have hSm : MeasurableSet Sm := hSmdef ▸ measurableSet_lt measurable_subtype_coe measurable_const
  have hmemp (p : unitInterval) : p ∈ Sp ↔ (1/2 : ℝ) < p := by rw [hSpdef]; rfl
  have hmemm (p : unitInterval) : p ∈ Sm ↔ (p : ℝ) < 1/2 := by rw [hSmdef]; rfl
  have hdisj : Disjoint Sp Sm := by
    rw [Set.disjoint_left]
    intro p hp hm
    exact lt_asymm ((hmemp p).1 hp) ((hmemm p).1 hm)
  have hsplit : G.restrict Sp + G.restrict Sm = G := by
    rw [← Measure.restrict_union hdisj hSm]
    apply Measure.restrict_eq_self_of_ae_mem
    rw [ae_iff]
    apply measure_mono_null _ hG
    intro p hp
    have hp' : ¬ (p ∈ Sp ∨ p ∈ Sm) := hp
    rw [hmemp, hmemm, not_or, not_lt, not_lt] at hp'
    exact le_antisymm hp'.1 hp'.2
  obtain ⟨μ, hμdef⟩ : ∃ μ : Measure Gap, μ = G.map gapOf := ⟨_, rfl⟩
  obtain ⟨νp, hνp⟩ : ∃ ν : Measure Gap, ν = (G.restrict Sp).map gapOf := ⟨_, rfl⟩
  obtain ⟨νm, hνm⟩ : ∃ ν : Measure Gap, ν = (G.restrict Sm).map gapOf := ⟨_, rfl⟩
  rw [← hμdef]
  have : IsProbabilityMeasure μ := by
    rw [hμdef]
    exact (Measure.isProbabilityMeasure_map_iff measurable_gapOf.aemeasurable).2 inferInstance
  have : IsFiniteMeasure νp := by rw [hνp]; infer_instance
  have : IsFiniteMeasure νm := by rw [hνm]; infer_instance
  have hμ : μ = νp + νm := by
    rw [hμdef, hνp, hνm, ← Measure.map_add _ _ measurable_gapOf, hsplit]
  have hle : νp ≤ μ := by
    rw [hμ]; exact Measure.le_add_right le_rfl
  have hac : νp ≪ μ := Measure.absolutelyContinuous_of_le hle
  obtain ⟨q, hq⟩ : ∃ q : SignLaw, q.val = fun d => min 1 (νp.rnDeriv μ d).toReal :=
    ⟨⟨fun d => min 1 (νp.rnDeriv μ d).toReal,
      measurable_const.min (Measure.measurable_rnDeriv _ _).ennreal_toReal,
      fun d => ⟨le_min zero_le_one ENNReal.toReal_nonneg, min_le_left _ _⟩⟩, rfl⟩
  have hqae : q.val =ᵐ[μ] fun d => (νp.rnDeriv μ d).toReal := by
    filter_upwards [Measure.rnDeriv_le_one_of_le hle] with d hd
    rw [hq]
    apply min_eq_right
    have h1 := ENNReal.toReal_mono ENNReal.one_ne_top hd
    simpa using h1
  refine ⟨q, ?_⟩
  have := latentLaw_probability μ q
  apply measure_eq_of_bounded_real_tests
  rintro F hF ⟨C, hb⟩
  have hFp : Measurable (fun d => F (gapParameter true d)) :=
    hF.comp (measurable_gapParameter true)
  have hFm : Measurable (fun d => F (gapParameter false d)) :=
    hF.comp (measurable_gapParameter false)
  have hq1 : ∀ d, 0 ≤ q.val d ∧ q.val d ≤ 1 := q.property.2
  have hint (ν : Measure Gap) [IsFiniteMeasure ν] (s : Bool) :
      Integrable (fun d => F (gapParameter s d)) ν :=
    ThresholdHC.Tier5.integrable_of_abs_bound ν _ (hF.comp (measurable_gapParameter s)) C
      (fun d => hb _)
  have hintq (s : Bool) : Integrable (fun d => q.val d * F (gapParameter s d)) μ :=
    integrable_unit_mul μ q.val _ q.property.1 hq1 (hF.comp (measurable_gapParameter s)) C
      (fun d => hb _)
  have hrn (s : Bool) :
      ∫ d, q.val d * F (gapParameter s d) ∂μ = ∫ d, F (gapParameter s d) ∂νp := by
    rw [← integral_toReal_rnDeriv_mul hac]
    apply integral_congr_ae
    filter_upwards [hqae] with d hd
    rw [hd]
  have hsum : ∫ d, F (gapParameter false d) ∂μ =
      ∫ d, F (gapParameter false d) ∂νp + ∫ d, F (gapParameter false d) ∂νm := by
    rw [hμ]
    exact integral_add_measure (hint νp false) (hint νm false)
  have hL : ∫ p, F p ∂latentLaw μ q =
      ∫ d, F (gapParameter true d) ∂νp + ∫ d, F (gapParameter false d) ∂νm := by
    rw [latentLaw, populationParameterLaw_integral μ _ _ _ (measurable_gapParameter false)
      (measurable_gapParameter true) (measurable_signUnit q) F hF C hb]
    have he : ∀ d, (signUnit q d : ℝ) * F (gapParameter true d) +
        (1 - (signUnit q d : ℝ)) * F (gapParameter false d) =
        (q.val d * F (gapParameter true d) + F (gapParameter false d)) -
          q.val d * F (gapParameter false d) := by
      intro d
      change q.val d * F (gapParameter true d) + (1 - q.val d) * F (gapParameter false d) = _
      ring
    simp_rw [he]
    have hadd : Integrable
        (fun d => q.val d * F (gapParameter true d) + F (gapParameter false d)) μ :=
      (hintq true).add (hint μ false)
    rw [integral_sub hadd (hintq false),
      integral_add (hintq true) (hint μ false), hrn true, hrn false, hsum]
    ring
  have hpos : ∫ d, F (gapParameter true d) ∂νp = ∫ p in Sp, F p ∂G := by
    rw [hνp, integral_map measurable_gapOf.aemeasurable hFp.aestronglyMeasurable]
    apply setIntegral_congr_fun hSp
    intro p hp
    change F (gapParameter true (gapOf p)) = F p
    rw [gapParameter_true_gapOf p ((hmemp p).1 hp)]
  have hneg : ∫ d, F (gapParameter false d) ∂νm = ∫ p in Sm, F p ∂G := by
    rw [hνm, integral_map measurable_gapOf.aemeasurable hFm.aestronglyMeasurable]
    apply setIntegral_congr_fun hSm
    intro p hp
    change F (gapParameter false (gapOf p)) = F p
    rw [gapParameter_false_gapOf p ((hmemm p).1 hp)]
  have hiG (s : Set unitInterval) : Integrable F (G.restrict s) :=
    ThresholdHC.Tier5.integrable_of_abs_bound _ _ hF C hb
  rw [hL, hpos, hneg, ← integral_add_measure (hiG Sp) (hiG Sm), hsplit]

/-- A law `G` of `P` with `|P - 1/2| ~ μ` is a probability law with no atom at
`1/2`, and `gapOf` pushes it forward to `μ`. -/
theorem of_magnitude (μ : Measure Gap) [IsProbabilityMeasure μ] (G : Measure unitInterval)
    (h : G.map (fun p : unitInterval => |(p : ℝ) - 1/2|) = μ.map Subtype.val) :
    IsProbabilityMeasure G ∧ G {p : unitInterval | (p : ℝ) = 1/2} = 0 ∧ G.map gapOf = μ := by
  have hA := measurable_absHalf
  have hprob : IsProbabilityMeasure G := by
    have hv : IsProbabilityMeasure (μ.map Subtype.val) :=
      (Measure.isProbabilityMeasure_map_iff measurable_subtype_coe.aemeasurable).2 inferInstance
    rw [← h] at hv
    exact (Measure.isProbabilityMeasure_map_iff hA.aemeasurable).1 hv
  have h0 : G {p : unitInterval | (p : ℝ) = 1/2} = 0 := by
    have hpre : {p : unitInterval | (p : ℝ) = 1/2} =
        (fun p : unitInterval => |(p : ℝ) - 1/2|) ⁻¹' {0} := by
      ext p
      rw [mem_preimage, mem_singleton_iff, abs_eq_zero, sub_eq_zero]
      rfl
    have hv : (Subtype.val : Gap → ℝ) ⁻¹' {0} = ∅ := by
      ext d
      rw [mem_preimage, mem_singleton_iff]
      simp only [mem_empty_iff_false, iff_false]
      exact d.property.1.ne'
    rw [hpre, ← Measure.map_apply hA (measurableSet_singleton 0), h,
      Measure.map_apply measurable_subtype_coe (measurableSet_singleton 0), hv, measure_empty]
  refine ⟨hprob, h0, ?_⟩
  have he : MeasurableEmbedding (Subtype.val : Gap → ℝ) :=
    MeasurableEmbedding.subtype_coe (measurableSet_Ioc (a := (0 : ℝ)) (b := 1/2))
  have h2 : (G.map gapOf).map Subtype.val = μ.map Subtype.val := by
    rw [Measure.map_map measurable_subtype_coe measurable_gapOf, ← h]
    apply Measure.map_congr
    rw [Filter.EventuallyEq, ae_iff]
    apply measure_mono_null _ h0
    intro p hp
    have hp' : ¬ ((Subtype.val ∘ gapOf) p = |(p : ℝ) - 1/2|) := hp
    by_contra hne
    exact hp' (gapOf_coe p hne)
  rw [← he.comap_map (G.map gapOf), h2, he.comap_map]

/-- Every law `G` of `P` with `|P - 1/2| ~ μ` is some `G_{μ,q}`. -/
theorem exists_latentLaw_of_magnitude (μ : Measure Gap) [IsProbabilityMeasure μ]
    (G : Measure unitInterval)
    (h : G.map (fun p : unitInterval => |(p : ℝ) - 1/2|) = μ.map Subtype.val) :
    ∃ q : SignLaw, latentLaw μ q = G := by
  obtain ⟨hprob, h0, hmap⟩ := of_magnitude μ G h
  obtain ⟨q, hq⟩ := exists_latentLaw_eq G h0
  exact ⟨q, hmap ▸ hq⟩

end ThresholdHC.LatentDisintegration
