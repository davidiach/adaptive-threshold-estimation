import ThresholdHC.CriticalEntropy.FiniteAffinity

noncomputable section

namespace ThresholdHC.CriticalEntropy
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal Topology

theorem map_singleton_real_tendsto {Ω I : Type} [MeasurableSpace Ω]
    [Fintype I] [MeasurableSpace I] [MeasurableSingletonClass I]
    (P : Measure Ω) [IsFiniteMeasure P] (F : ℕ → Ω → I) (f : Ω → I)
    (hF : ∀ n, Measurable (F n)) (hf : Measurable f)
    (he : ∀ᵐ x ∂P, ∀ᶠ n in atTop, F n x = f x) (i : I) :
    Tendsto (fun n => (P.map (F n)).real {i}) atTop (𝓝 ((P.map f).real {i})) := by
  classical
  let g : I → ℝ := ({i} : Set I).indicator (fun _ => 1)
  have hgm : Measurable g := measurable_of_countable g
  have heq (u : Ω → I) (hu : Measurable u) :
      (P.map u).real {i} = ∫ x, g (u x) ∂P := by
    rw [← integral_indicator_one (measurableSet_singleton i)]
    change (∫ x, g x ∂P.map u) = _
    exact integral_map hu.aemeasurable hgm.aestronglyMeasurable
  have h := tendsto_integral_of_dominated_convergence (μ := P) (fun _ => (1 : ℝ))
    (F := fun n x => g (F n x)) (f := fun x => g (f x))
    (fun n => (hgm.comp (hF n)).aestronglyMeasurable) (integrable_const 1)
    (fun n => ae_of_all _ (fun x => by by_cases hx : F n x = i <;> simp [g,hx]))
    (by
      filter_upwards [he] with x hx
      exact (tendsto_congr' (hx.mono (fun n hn => congrArg g hn))).2 tendsto_const_nhds)
  simpa only [← heq _ hf,← heq _ (hF _)] using h

theorem hellingerAffinity_finite_real {I : Type} [Fintype I]
    [MeasurableSpace I] [MeasurableSingletonClass I]
    (P Q : Measure I) [IsFiniteMeasure P] [IsFiniteMeasure Q] :
    (hellingerAffinity P Q).toReal = realFiniteAffinity (fun i => P.real {i}) (fun i => Q.real {i}) := by
  rw [hellingerAffinity_finite,finiteAffinity_toReal _ _
    (fun i => measure_ne_top _ _) (fun i => measure_ne_top _ _)]
  rfl

/-- Eventual finite observations converge in affinity under both endpoint laws.
The hypotheses require eventual reconstruction separately at each endpoint. -/
theorem hellingerAffinity_tendsto_eventual_maps {Ω I : Type} [MeasurableSpace Ω]
    [Fintype I] [MeasurableSpace I] [MeasurableSingletonClass I]
    (P Q : Measure Ω) [IsFiniteMeasure P] [IsFiniteMeasure Q]
    (F : ℕ → Ω → I) (f : Ω → I) (hF : ∀ n, Measurable (F n)) (hf : Measurable f)
    (hP : ∀ᵐ x ∂P, ∀ᶠ n in atTop, F n x = f x)
    (hQ : ∀ᵐ x ∂Q, ∀ᶠ n in atTop, F n x = f x) :
    Tendsto (fun n => (hellingerAffinity (P.map (F n)) (Q.map (F n))).toReal) atTop
      (𝓝 (hellingerAffinity (P.map f) (Q.map f)).toReal) := by
  have hp := tendsto_pi_nhds.mpr (fun i => map_singleton_real_tendsto P F f hF hf hP i)
  have hq := tendsto_pi_nhds.mpr (fun i => map_singleton_real_tendsto Q F f hF hf hQ i)
  have h := realFiniteAffinity_continuous.continuousAt.tendsto.comp (hp.prodMk_nhds hq)
  simpa only [hellingerAffinity_finite_real,Function.comp_def] using h

theorem hellingerAffinity_lower_of_eventual_maps {Ω I : Type} [MeasurableSpace Ω]
    [Fintype I] [MeasurableSpace I] [MeasurableSingletonClass I]
    (P Q : Measure Ω) [IsFiniteMeasure P] [IsFiniteMeasure Q]
    (F : ℕ → Ω → I) (f : Ω → I) (hF : ∀ n, Measurable (F n)) (hf : Measurable f)
    (hP : ∀ᵐ x ∂P, ∀ᶠ n in atTop, F n x = f x)
    (hQ : ∀ᵐ x ∂Q, ∀ᶠ n in atTop, F n x = f x)
    (a : ℝ) (ha : ∀ n, a ≤ (hellingerAffinity (P.map (F n)) (Q.map (F n))).toReal) :
    a ≤ (hellingerAffinity (P.map f) (Q.map f)).toReal :=
  ge_of_tendsto (hellingerAffinity_tendsto_eventual_maps P Q F f hF hf hP hQ)
    (Eventually.of_forall ha)

end ThresholdHC.CriticalEntropy
