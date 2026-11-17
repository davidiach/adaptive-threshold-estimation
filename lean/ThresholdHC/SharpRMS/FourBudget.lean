import ThresholdHC.SharpRMS.BayesBudget
import ThresholdHC.SharpRMS.WeakPopulation
import ThresholdHC.SharpRMS.Attainment

/-! At most four expected flips: the lower bound for every ordinary gap law. -/
noncomputable section
namespace ThresholdHC.SharpRMS
open MeasureTheory Set Filter Tier3 Tier4 Tier5 Tier6
open scoped ENNReal Topology unitInterval

private def flatPrior (p : unitInterval) : SignLaw :=
  ⟨fun _ => p.val, measurable_const, fun _ => p.property⟩

/-- A finite-prefix Bayes lower bound that is uniform in the horizon passes
to the population minimax risk for all finite-expected-work estimators. -/
theorem minimax_from_prefix_bayes (μ : Measure Gap) [IsProbabilityMeasure μ] (B : ℝ)
    (priorBound : ∀ (R : Type) [MeasurableSpace R] (A : AdaptiveEstimator R), UniformBudget μ A B →
      ∀ n (X : PopulationSeed R → Prefix n → ℝ), (∀ w, Measurable (fun u => X u w)) →
      (∀ u w, X u w ∈ Icc 0 1) → (1/36:ℝ) ≤ ∫ p : unitInterval, ∫ u,
        priorExpect (populationPolicy A) populationGap (fun q v w => (X v w-q.val)^2) (p,u)
          ∂populationSeedLaw μ A) : ENNReal.ofReal (1/6:ℝ) ≤ minimaxRisk μ B := by
  apply le_sInf
  rintro _ ⟨R,mR,A,hb,rfl⟩
  by_contra! hsmall
  let c := (maximalRMSRisk μ A).toReal
  have hc : ENNReal.ofReal c = maximalRMSRisk μ A := ENNReal.ofReal_toReal
    (hsmall.trans ENNReal.ofReal_lt_top).ne
  have hc' : c < 1/6 := (ENNReal.ofReal_lt_ofReal_iff_of_nonneg ENNReal.toReal_nonneg).mp (hc.trans_lt hsmall)
  let Y := fun z : PopulationSeed R × ProcessTape => max 0 (min 1 (populationOutput A z))
  have hYm : Measurable Y := measurable_const.max (measurable_const.min (measurable_populationOutput A))
  have hY (z) : Y z ∈ Icc 0 1 := ⟨le_max_left ..,max_le (by norm_num) (min_le_left ..)⟩
  let P := fun p : unitInterval => experimentLaw μ A (flatPrior p)
  let f := fun (p : unitInterval) z => (Y z - p.val)^2
  have fm p : Measurable (f p) := (hYm.sub measurable_const).pow_const 2
  have bound (x : ℝ) (hx : x ∈ Icc 0 1) (p : unitInterval) : |(x-p.val)^2| ≤ 1 := by
    rw [abs_of_nonneg (sq_nonneg _)]
    nlinarith [mul_nonneg (show 0 ≤ 1-x+p.val by linarith [hx.2,p.property.1])
      (show 0 ≤ 1+x-p.val by linarith [hx.1,p.property.2])]
  have integr (p) : Integrable (f p) (P p) :=
    (integrable_const (1:ℝ)).mono' (fm p).aestronglyMeasurable (ae_of_all _ fun z => bound _ (hY z) p)
  let risk := fun p : unitInterval => ∫ z, f p z ∂P p
  have risk_le (p : unitInterval) : risk p ≤ c^2 := by
    have ht : signMean μ (flatPrior p).val = p.val := by simp [signMean,flatPrior]
    have root := le_iSup (fun q => rootMeanRisk (experimentLaw μ A q) (populationOutput A) (signMean μ q.val)) (flatPrior p)
    change _ ≤ maximalRMSRisk μ A at root
    rw [ht,← hc] at root
    have sq : squaredRisk (P p) (populationOutput A) p.val ≤ ENNReal.ofReal (c^2) := by
      by_contra! bad
      have hh := ENNReal.rpow_lt_rpow bad (by norm_num : (0:ℝ)<1/2)
      rw [ofReal_square_rpow_half c ENNReal.toReal_nonneg] at hh
      exact (not_lt_of_ge root) hh
    apply (ENNReal.ofReal_le_ofReal_iff (sq_nonneg c)).mp
    apply le_trans _ sq
    rw [show ENNReal.ofReal (risk p) = ∫⁻ z, ENNReal.ofReal (f p z) ∂P p from
      ofReal_integral_eq_lintegral_ofReal (integr p) (ae_of_all _ fun _ => sq_nonneg _)]
    apply lintegral_mono
    intro z
    apply ENNReal.ofReal_le_ofReal
    let y := populationOutput A z
    change (max 0 (min 1 y)-p.val)^2 ≤ (y-p.val)^2
    rcases le_total y 0 with hy | hy
    · rw [min_eq_right (by linarith),max_eq_left hy]
      nlinarith [mul_nonneg (neg_nonneg.mpr hy) (show 0 ≤ 2*p.val-y by linarith [p.property.1])]
    · rcases le_total y 1 with h' | h'
      · rw [min_eq_right h',max_eq_right hy]
      · rw [min_eq_left h',max_eq_right (by norm_num)]
        nlinarith [mul_nonneg (sub_nonneg.mpr h') (show 0 ≤ y+1-2*p.val by linarith [p.property.2])]
  let ν := populationSeedLaw μ A
  let F := fun (n : ℕ) (u : PopulationSeed R) (w : Prefix n) => Y (padJoint n (u,w))
  have Fm (n : ℕ) (w : Prefix n) : Measurable (fun u => F n u w) :=
    (hYm.comp (measurable_padJoint n)).comp (measurable_id.prodMk measurable_const)
  let L := fun n => priorExpect (populationPolicy A) populationGap
    (fun p u w => (F n u w-p.val)^2)
  let N := fun n (p : unitInterval) => ∫ u, L n (p,u) ∂ν
  have eqn (n) (p : unitInterval) : (∫ z, f p (observePrefix n z) ∂P p) = N n p :=
    (population_realization R μ A (flatPrior p)).2 n (fun u w => (F n u w-p.val)^2)
      (fun w => ((Fm n w).sub measurable_const).pow_const 2) ⟨1,fun u w => bound _ (hY _) p⟩
  have avg (n : ℕ) : 1/36 ≤ ∫ p : unitInterval, N n p := priorBound R A hb n (F n) (Fm n) (fun _ _ => hY _)
  have lim (p : unitInterval) : Tendsto (fun n => N n p) atTop (𝓝 (risk p)) :=
    (limit_prefix A μ (flatPrior p) B hb (f p) (fm p) 1 (fun z => bound _ (hY z) p)).congr (fun n => eqn n p)
  have hLm (n : ℕ) : Measurable (L n) := measurable_priorExpect (populationPolicy A)
    (measurable_populationPolicy A) populationGap measurable_populationGap _
    (fun w => (((Fm n w).comp measurable_snd).sub (measurable_subtype_coe.comp measurable_fst)).pow_const 2)
  have hNb (n : ℕ) (p : unitInterval) : ‖N n p‖ ≤ 1 := by
    have := norm_integral_le_of_norm_le_const (μ := ν) (f := fun u => L n (p,u))
      (ae_of_all _ fun u => priorExpect_bound (populationPolicy A) populationGap
        (fun u i => ⟨(u.2 i).property.1.le,(u.2 i).property.2⟩) _ 1 (fun p u w => bound _ (hY _) p) (p,u))
    simpa using this
  have Nm n : AEStronglyMeasurable (N n) volume := (hLm n).stronglyMeasurable.integral_prod_right'.aestronglyMeasurable
  have limAvg := tendsto_integral_of_dominated_convergence (μ := (volume : Measure unitInterval))
    (fun _ => (1:ℝ)) Nm (integrable_const 1) (fun n => ae_of_all _ (hNb n)) (ae_of_all _ lim)
  have low := ge_of_tendsto limAvg (Eventually.of_forall avg)
  have hi : Integrable risk volume := (integrable_const (1:ℝ)).mono'
    (aestronglyMeasurable_of_tendsto_ae atTop Nm (ae_of_all _ lim))
    (ae_of_all _ fun p => le_of_tendsto (lim p).norm (Eventually.of_forall fun n => hNb n p))
  have up := integral_mono hi (integrable_const (c^2)) risk_le
  simp only [integral_const,probReal_univ,one_smul] at up
  nlinarith only [low,up,mul_pos (show 0 < 1/6-c by linarith) (show 0 < 1/6+c by
    have := show 0 ≤ c from ENNReal.toReal_nonneg; linarith)]

theorem population_prefix_work_budget {R : Type} [MeasurableSpace R]
    (μ : Measure Gap) [IsProbabilityMeasure μ] (A : AdaptiveEstimator R) (B : ℝ) (hB : 0 ≤ B)
    (hb : UniformBudget μ A B) (n : ℕ) (p : unitInterval) :
    (∫ u, priorExpect (populationPolicy A) populationGap (fun _ _ => @workOf n) (p,u)
      ∂populationSeedLaw μ A) ≤ B := by
  have he := (population_realization R μ A (flatPrior p)).2 n (fun _ => @workOf n)
    (fun _ => measurable_const) ⟨(n:ℝ), fun u w => by
      rw [abs_of_nonneg (workOf_nonneg _)]; exact workOf_le_length _⟩
  exact he.ge.trans (prefix_work_le A μ (flatPrior p) B hB hb n)

/-- At most four expected flips for arbitrary gap laws, including private
randomness and unbounded stopping. -/
theorem four_budget_minimax_lower (μ : Measure Gap) [IsProbabilityMeasure μ] (B : ℝ)
    (hB : 0 ≤ B) (hfour : B ≤ 4) : ENNReal.ofReal (1/6:ℝ) ≤ minimaxRisk μ B := by
  apply minimax_from_prefix_bayes
  intro R _ A hb n X hm hX
  exact four_budget_prefix_bayes (populationSeedLaw μ A) (populationPolicy A) (measurable_populationPolicy A)
    populationGap measurable_populationGap (fun u i => ⟨(u.2 i).property.1.le,(u.2 i).property.2⟩)
    X hm hX (fun p => (population_prefix_work_budget μ A B hB hb n p).trans hfour)

/-- Exact equality for the endpoint gap at budget four in the original
unrestricted population experiment. -/
theorem endpoint_minimax_eq : minimaxRisk (Measure.dirac endpointGap) 4 = ENNReal.ofReal (1/6:ℝ) :=
  le_antisymm endpoint_minimax_upper (four_budget_minimax_lower _ _ (by norm_num) le_rfl)

end ThresholdHC.SharpRMS
