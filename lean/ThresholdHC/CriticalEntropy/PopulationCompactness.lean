import ThresholdHC.CriticalEntropy.PopulationGeometryModel

noncomputable section
open MeasureTheory Set
open scoped ENNReal RealInnerProductSpace Topology
namespace ThresholdHC.CriticalEntropy

theorem populationDualSet_compact {D : Type} [MeasurableSpace D]
    (μ : Measure D) [IsProbabilityMeasure μ] (ρ : ℝ) :
    IsCompact (populationDualSet μ ρ) := by
  have hclosed : IsClosed {f : PopulationDual μ | ∀ (S : Set D) (hS : MeasurableSet S),
      f (indicatorConstLp 2 hS (measure_ne_top μ S) (1 : ℝ)) ∈ Icc 0 (μ.real S/2)} := by
    simp only [ofPred_forall]
    apply isClosed_iInter
    intro S
    apply isClosed_iInter
    intro hS
    exact isClosed_Icc.preimage (WeakDual.eval_continuous _)
  exact ((WeakDual.isCompact_closedBall (0 : StrongDual ℝ (Lp ℝ 2 μ)) 1).inter_right
    hclosed).inter_right (isClosed_le (WeakDual.eval_continuous _) continuous_const)

theorem populationDualSet_nonempty {D : Type} [MeasurableSpace D]
    (μ : Measure D) [IsProbabilityMeasure μ] (ρ : ℝ) (hρ : 0 ≤ ρ) :
    (populationDualSet μ ρ).Nonempty := by
  refine ⟨0,⟨⟨?_,?_⟩,?_⟩⟩
  · simp
  · intro S hS
    change 0 ∈ Icc 0 (μ.real S/2)
    exact ⟨le_rfl, by positivity⟩
  · exact hρ

theorem populationDualSet_convex {D : Type} [MeasurableSpace D]
    (μ : Measure D) [IsProbabilityMeasure μ] (ρ : ℝ) :
    Convex ℝ (populationDualSet μ ρ) := by
  let ev (g : Lp ℝ 2 μ) : PopulationDual μ →ₗ[ℝ] ℝ :=
    (ContinuousLinearMap.apply ℝ ℝ g).toLinearMap.comp WeakDual.toStrongDual.toLinearMap
  have hc : Convex ℝ {f : PopulationDual μ | ∀ (S : Set D) (hS : MeasurableSet S),
      f (indicatorConstLp 2 hS (measure_ne_top μ S) (1 : ℝ)) ∈ Icc 0 (μ.real S/2)} := by
    simp only [ofPred_forall]
    apply convex_iInter
    intro S
    apply convex_iInter
    intro hS
    exact (convex_Icc (0 : ℝ) (μ.real S/2)).linear_preimage
      (ev (indicatorConstLp 2 hS (measure_ne_top μ S) (1 : ℝ)))
  exact (((convex_closedBall (0 : StrongDual ℝ (Lp ℝ 2 μ)) 1).linear_preimage
    WeakDual.toStrongDual.toLinearMap).inter hc).inter
      ((convex_Iic ρ).linear_preimage (ev (Lp.const 2 μ (1 : ℝ))))

theorem populationDualDensity_test {D : Type} [MeasurableSpace D]
    (μ : Measure D) (f : PopulationDual μ) (g : Lp ℝ 2 μ) :
    ⟪populationDualDensity μ f,g⟫ = f g :=
  InnerProductSpace.toDual_symm_apply

theorem populationDualDensity_setIntegral {D : Type} [MeasurableSpace D]
    (μ : Measure D) [IsProbabilityMeasure μ] (f : PopulationDual μ)
    (S : Set D) (hS : MeasurableSet S) :
    (∫ d in S, populationDualDensity μ f d ∂μ) =
      f (indicatorConstLp 2 hS (measure_ne_top μ S) (1 : ℝ)) := by
  rw [← L2.inner_indicatorConstLp_one hS (measure_ne_top μ S),real_inner_comm]
  exact populationDualDensity_test μ f _

theorem populationDualDensity_bounds {D : Type} [MeasurableSpace D]
    (μ : Measure D) [IsProbabilityMeasure μ] (ρ : ℝ)
    (f : PopulationDual μ) (hf : f ∈ populationDualSet μ ρ) :
    ∀ᵐ d ∂μ, 0 ≤ populationDualDensity μ f d ∧ populationDualDensity μ f d ≤ 1/2 := by
  have hi : Integrable (populationDualDensity μ f) μ :=
    (Lp.memLp _).integrable (by norm_num)
  have hlo : 0 ≤ᵐ[μ] populationDualDensity μ f := by
    apply ae_nonneg_of_forall_setIntegral_nonneg hi
    intro S hS hfin
    rw [populationDualDensity_setIntegral μ f S hS]
    exact (hf.1.2 S hS).1
  have hhi : populationDualDensity μ f ≤ᵐ[μ] (fun _ => (1/2 : ℝ)) := by
    apply ae_le_of_forall_setIntegral_le hi (integrable_const _)
    intro S hS hfin
    rw [populationDualDensity_setIntegral μ f S hS, integral_const]
    simpa only [measureReal_restrict_apply_univ,smul_eq_mul,div_eq_mul_inv,one_mul]
      using (hf.1.2 S hS).2
  filter_upwards [hlo,hhi] with d hd hd'
  exact ⟨hd,hd'⟩

theorem populationDualPrior_measurable {D : Type} [MeasurableSpace D]
    (μ : Measure D) (f : PopulationDual μ) : Measurable (populationDualPrior μ f) := by
  exact (measurable_const.max ((Lp.stronglyMeasurable _).measurable.min measurable_const)).subtype_mk

theorem populationDualPrior_le_half {D : Type} [MeasurableSpace D]
    (μ : Measure D) (f : PopulationDual μ) (d : D) :
    (populationDualPrior μ f d : ℝ) ≤ 1/2 :=
  max_le (by norm_num) (min_le_right _ _)

theorem populationDualPrior_ae {D : Type} [MeasurableSpace D]
    (μ : Measure D) [IsProbabilityMeasure μ] (ρ : ℝ)
    (f : PopulationDual μ) (hf : f ∈ populationDualSet μ ρ) :
    (fun d => (populationDualPrior μ f d : ℝ)) =ᵐ[μ] populationDualDensity μ f := by
  filter_upwards [populationDualDensity_bounds μ ρ f hf] with d hd
  change max 0 (min (populationDualDensity μ f d) (1/2)) = populationDualDensity μ f d
  rw [min_eq_left hd.2,max_eq_right hd.1]

theorem populationDualPrior_mass {D : Type} [MeasurableSpace D]
    (μ : Measure D) [IsProbabilityMeasure μ] (ρ : ℝ)
    (f : PopulationDual μ) (hf : f ∈ populationDualSet μ ρ) :
    (∫ d, (populationDualPrior μ f d : ℝ) ∂μ) = f (Lp.const 2 μ (1 : ℝ)) := by
  rw [integral_congr_ae (populationDualPrior_ae μ ρ f hf)]
  simpa using populationDualDensity_setIntegral μ f univ MeasurableSet.univ

theorem populationDualPrior_admissible {D : Type} [MeasurableSpace D]
    (μ : Measure D) [IsProbabilityMeasure μ] (ρ : ℝ)
    (f : PopulationDual μ) (hf : f ∈ populationDualSet μ ρ) :
    Measurable (populationDualPrior μ f) ∧
      (∀ d, (populationDualPrior μ f d : ℝ) ≤ 1/2) ∧
      (∫ d, (populationDualPrior μ f d : ℝ) ∂μ) ≤ ρ := by
  refine ⟨populationDualPrior_measurable μ f,populationDualPrior_le_half μ f,?_⟩
  rw [populationDualPrior_mass μ ρ f hf]
  exact hf.2

theorem populationDualSet_covers_priors {D : Type} [MeasurableSpace D]
    (μ : Measure D) [IsProbabilityMeasure μ] (ρ : ℝ)
    (q : D → unitInterval) (hq : Measurable q) (hh : ∀ d, (q d : ℝ) ≤ 1/2)
    (hm : (∫ d, (q d : ℝ) ∂μ) ≤ ρ) :
    ∃ f ∈ populationDualSet μ ρ,
      (fun d => (populationDualPrior μ f d : ℝ)) =ᵐ[μ] (fun d => (q d : ℝ)) := by
  have hqm : Measurable (fun d => (q d : ℝ)) := measurable_subtype_coe.comp hq
  have hqb : ∀ᵐ d ∂μ, ‖(q d : ℝ)‖ ≤ 1 := by
    exact ae_of_all _ (fun d => by rw [Real.norm_eq_abs,abs_of_nonneg (q d).property.1]; exact (q d).property.2)
  have hqL : MemLp (fun d => (q d : ℝ)) 2 μ := MemLp.of_bound hqm.aestronglyMeasurable 1 hqb
  let u : Lp ℝ 2 μ := hqL.toLp (fun d => (q d : ℝ))
  let f : PopulationDual μ := (InnerProductSpace.toDual ℝ (Lp ℝ 2 μ) u).toWeakDual
  have hu : u =ᵐ[μ] (fun d => (q d : ℝ)) := hqL.coeFn_toLp
  have hd : populationDualDensity μ f = u := by simp [populationDualDensity,f]
  have hi : Integrable (fun d => (q d : ℝ)) μ := hqL.integrable (by norm_num)
  have ht (S : Set D) (hS : MeasurableSet S) :
      f (indicatorConstLp 2 hS (measure_ne_top μ S) (1 : ℝ)) = ∫ d in S, (q d : ℝ) ∂μ := by
    rw [← populationDualDensity_setIntegral μ f S hS,hd]
    exact integral_congr_ae (ae_restrict_of_ae hu)
  have hf : f ∈ populationDualSet μ ρ := by
    refine ⟨⟨?_,?_⟩,?_⟩
    · simp only [mem_preimage,Metric.mem_closedBall,dist_zero_right,
        f,StrongDual.toStrongDual_toWeakDual,LinearIsometryEquiv.norm_map]
      have hb : ∀ᵐ d ∂μ, ‖u d‖ ≤ 1 := by
        filter_upwards [hu,hqb] with d he hb
        rwa [he]
      simpa [measureUnivNNReal] using Lp.norm_le_of_ae_bound (by norm_num : (0 : ℝ) ≤ 1) hb
    · intro S hS
      rw [ht S hS]
      refine ⟨setIntegral_nonneg_of_ae (ae_of_all μ (fun d => (q d).property.1)),?_⟩
      have hle := setIntegral_mono_ae (s := S) hi.integrableOn (integrable_const (1/2 : ℝ)).integrableOn
        (ae_of_all μ hh)
      simpa [setIntegral_const,smul_eq_mul,div_eq_mul_inv] using hle
    · have htu := ht univ MeasurableSet.univ
      simp only [indicatorConstLp_univ,setIntegral_univ] at htu
      change f (Lp.const 2 μ (1 : ℝ)) ≤ ρ
      rwa [htu]
  refine ⟨f,hf,?_⟩
  exact (populationDualPrior_ae μ ρ f hf).trans (hd ▸ hu)

theorem populationDualPrior_test {D : Type} [MeasurableSpace D]
    (μ : Measure D) [IsProbabilityMeasure μ] (ρ : ℝ)
    (f : PopulationDual μ) (hf : f ∈ populationDualSet μ ρ) (g : Lp ℝ 2 μ) :
    (∫ d, (populationDualPrior μ f d : ℝ)*g d ∂μ) = f g := by
  rw [← populationDualDensity_test μ f g,L2.inner_def]
  apply integral_congr_ae
  filter_upwards [populationDualPrior_ae μ ρ f hf] with d hd
  simp [hd,mul_comm]

theorem populationMomentMap_apply {D I : Type} [MeasurableSpace D]
    (μ : Measure D) (g : I → Lp ℝ 2 μ) (b : I → ℝ) (f : PopulationDual μ) (i : I) :
    populationMomentMap μ g b f i = f (g i)+b i := rfl

theorem populationMomentMap_continuous {D I : Type} [MeasurableSpace D]
    (μ : Measure D) (g : I → Lp ℝ 2 μ) (b : I → ℝ) :
    Continuous (populationMomentMap μ g b) := by
  apply continuous_pi
  intro i
  exact (WeakDual.eval_continuous (g i)).add continuous_const

theorem populationMomentImage_compact_convex {D I : Type} [MeasurableSpace D]
    (μ : Measure D) [IsProbabilityMeasure μ] (ρ : ℝ)
    (g : I → Lp ℝ 2 μ) (b : I → ℝ) :
    IsCompact (populationMomentMap μ g b '' populationDualSet μ ρ) ∧
      Convex ℝ (populationMomentMap μ g b '' populationDualSet μ ρ) :=
  ⟨(populationDualSet_compact μ ρ).image (populationMomentMap_continuous μ g b),
    (populationDualSet_convex μ ρ).affine_image (populationMomentMap μ g b)⟩

theorem boundedPriorMomentSet_eq_image {D I : Type} [MeasurableSpace D]
    (μ : Measure D) [IsProbabilityMeasure μ] (ρ : ℝ)
    (g : I → Lp ℝ 2 μ) (b : I → ℝ) :
    boundedPriorMomentSet μ ρ g b = populationMomentMap μ g b '' populationDualSet μ ρ := by
  ext v
  constructor
  · rintro ⟨q,hq,hh,hm,hv⟩
    obtain ⟨f,hf,he⟩ := populationDualSet_covers_priors μ ρ q hq hh hm
    refine ⟨f,hf,?_⟩
    funext i
    rw [populationMomentMap_apply,hv i,← populationDualPrior_test μ ρ f hf (g i)]
    congr 1
    exact integral_congr_ae (he.mono fun d hd => congrArg (fun x : ℝ => x*g i d) hd)
  · rintro ⟨f,hf,rfl⟩
    obtain ⟨hq,hh,hm⟩ := populationDualPrior_admissible μ ρ f hf
    refine ⟨populationDualPrior μ f,hq,hh,hm,?_⟩
    intro i
    rw [populationMomentMap_apply,populationDualPrior_test μ ρ f hf (g i)]

theorem boundedPriorMomentSet_compact_convex {D I : Type} [MeasurableSpace D]
    (μ : Measure D) [IsProbabilityMeasure μ] (ρ : ℝ)
    (g : I → Lp ℝ 2 μ) (b : I → ℝ) :
    IsCompact (boundedPriorMomentSet μ ρ g b) ∧ Convex ℝ (boundedPriorMomentSet μ ρ g b) := by
  rw [boundedPriorMomentSet_eq_image]
  exact populationMomentImage_compact_convex μ ρ g b

theorem populationPairSet_compact_convex {D : Type} [MeasurableSpace D]
    (μ : Measure D) [IsProbabilityMeasure μ] (ρ δ : ℝ) :
    IsCompact (populationPairSet μ ρ δ) ∧ Convex ℝ (populationPairSet μ ρ δ) := by
  have ht : Continuous (populationTarget μ) := WeakDual.eval_continuous _
  refine ⟨((populationDualSet_compact μ ρ).prod (populationDualSet_compact μ ρ)).inter_right
    (isClosed_le continuous_const ((ht.comp continuous_snd).sub (ht.comp continuous_fst))),?_⟩
  exact ((populationDualSet_convex μ ρ).prod (populationDualSet_convex μ ρ)).inter
    ((convex_Ici δ).linear_preimage
      ((populationTarget μ).comp (LinearMap.snd ℝ (PopulationDual μ) (PopulationDual μ)) -
        (populationTarget μ).comp (LinearMap.fst ℝ (PopulationDual μ) (PopulationDual μ))))

theorem populationPairSet_nonempty {D : Type} [MeasurableSpace D]
    (μ : Measure D) [IsProbabilityMeasure μ] (ρ δ : ℝ)
    (hδ : 0 ≤ δ) (hδhalf : δ ≤ 1/2) (hδρ : δ ≤ ρ) :
    (populationPairSet μ ρ δ).Nonempty := by
  let qδ : D → unitInterval := fun _ => ⟨δ,hδ,le_trans hδhalf (by norm_num)⟩
  obtain ⟨f₀,hf₀,he₀⟩ := populationDualSet_covers_priors μ ρ (fun _ => 0)
    measurable_const (by intro d; norm_num) (by simpa using hδ.trans hδρ)
  obtain ⟨f₁,hf₁,he₁⟩ := populationDualSet_covers_priors μ ρ qδ
    measurable_const (fun _ => hδhalf) (by simpa [qδ] using hδρ)
  have ht₀ : populationTarget μ f₀ = 0 := by
    change f₀ (Lp.const 2 μ (1 : ℝ)) = 0
    rw [← populationDualPrior_mass μ ρ f₀ hf₀]
    simpa using integral_congr_ae he₀
  have ht₁ : populationTarget μ f₁ = δ := by
    change f₁ (Lp.const 2 μ (1 : ℝ)) = δ
    rw [← populationDualPrior_mass μ ρ f₁ hf₁]
    simpa [qδ] using integral_congr_ae he₁
  refine ⟨(f₀,f₁),⟨⟨hf₀,hf₁⟩,?_⟩⟩
  change δ ≤ populationTarget μ f₁-populationTarget μ f₀
  rw [ht₀,ht₁,sub_zero]

end ThresholdHC.CriticalEntropy
