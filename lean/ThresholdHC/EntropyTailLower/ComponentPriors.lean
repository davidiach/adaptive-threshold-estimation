import ThresholdHC.StoppingProgram.RobustRarity
import ThresholdHC.StoppingProgram.PositiveValue

/-! Disjoint component priors spend one global rarity budget. Their bias,
second-moment, and work contributions obey joint bounds from the original
feasible certificate, including arbitrary laws with atoms. -/

noncomputable section
open MeasureTheory Polynomial
open scoped BigOperators ENNReal
namespace ThresholdHC.EntropyTailLower
open ThresholdHC.Tier6 ThresholdHC.RareAboveTwo ThresholdHC.StoppingProgram
open ThresholdHC.CapIdentification

def finiteSumPrior {I : Type} [Fintype I] (q : I → SignLaw)
    (hq : ∀ d, ∑ i, (q i).val d ≤ 1) (S : Finset I) : SignLaw := by
  classical
  refine ⟨fun d => ∑ i ∈ S, (q i).val d, ?_, ?_⟩
  · exact Finset.measurable_sum _ (fun i _ => (q i).property.1)
  · intro d
    refine ⟨Finset.sum_nonneg (fun i _ => ((q i).property.2 d).1), ?_⟩
    exact (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S)
      (fun i _ _ => ((q i).property.2 d).1)).trans (hq d)

theorem finiteSumPrior_integral {I : Type} [Fintype I]
    (μ : Measure Gap) [IsProbabilityMeasure μ] (q : I → SignLaw)
    (hq : ∀ d, ∑ i, (q i).val d ≤ 1) (S : Finset I) :
    signMean μ (finiteSumPrior q hq S).val = ∑ i ∈ S, signMean μ (q i).val := by
  exact integral_finsetSum S (fun i _ => integrable_sign_prior μ (q i))

theorem finiteSumPrior_rare {I : Type} [Fintype I]
    (μ : Measure Gap) [IsProbabilityMeasure μ] (ρ : ℝ) (q : I → SignLaw)
    (hq : ∀ d, ∑ i, (q i).val d ≤ 1)
    (hρ : ∑ i, signMean μ (q i).val ≤ ρ) (S : Finset I) :
    RarePrior μ ρ (finiteSumPrior q hq S) := by
  rw [RarePrior, finiteSumPrior_integral]
  apply le_trans _ hρ
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S)
    (fun i _ _ => integral_nonneg (fun d => ((q i).property.2 d).1))

theorem finiteSumPrior_weighted_integral {I : Type} [Fintype I]
    (μ : Measure Gap) [IsProbabilityMeasure μ] (q : I → SignLaw)
    (hq : ∀ d, ∑ i, (q i).val d ≤ 1) (S : Finset I)
    (f : Gap → ℝ) (hf : Integrable f μ) :
    (∫ d, (finiteSumPrior q hq S).val d * f d ∂μ) =
      ∑ i ∈ S, ∫ d, (q i).val d * f d ∂μ := by
  change (∫ d, (∑ i ∈ S, (q i).val d) * f d ∂μ) = _
  simp_rw [Finset.sum_mul]
  exact integral_finsetSum S (fun i _ => integrable_prior_function μ (q i) hf)

theorem certificate_component_bias_budget {I : Type} [Fintype I] {N : ℕ}
    (μ : Measure Gap) [IsProbabilityMeasure μ] (ρ B : ℝ)
    (C : Certificate N) (hC : Feasible μ ρ B C) (q : I → SignLaw)
    (hq : ∀ d, ∑ i, (q i).val d ≤ 1)
    (hρ : ∑ i, signMean μ (q i).val ≤ ρ) :
    (∑ i, |∫ d, (q i).val d * (biasPolynomial C).eval (d:ℝ) ∂μ|) ≤ 2*C.bias := by
  classical
  let e : I → ℝ := fun i => ∫ d, (q i).val d * (biasPolynomial C).eval (d:ℝ) ∂μ
  let P := Finset.univ.filter (fun i => 0 ≤ e i)
  let M := Finset.univ.filter (fun i => ¬ 0 ≤ e i)
  have hf := (polynomial_gap_memLp μ (biasPolynomial C)).integrable (by norm_num : (1:ℝ≥0∞) ≤ 2)
  have hp := hC.bias_bound (finiteSumPrior q hq P) (finiteSumPrior_rare μ ρ q hq hρ P)
  have hm := hC.bias_bound (finiteSumPrior q hq M) (finiteSumPrior_rare μ ρ q hq hρ M)
  rw [certificate_bias_affine, finiteSumPrior_weighted_integral μ q hq P _ hf] at hp
  rw [certificate_bias_affine, finiteSumPrior_weighted_integral μ q hq M _ hf] at hm
  have he : (∑ i, |e i|) = (∑ i ∈ P, e i) - (∑ i ∈ M, e i) := by
    have hs := Finset.sum_filter_add_sum_filter_not Finset.univ (fun i => 0 ≤ e i) (fun i => |e i|)
    rw [← hs]
    change (∑ i ∈ P, |e i|) + (∑ i ∈ M, |e i|) = _
    have hp' : (∑ i ∈ P, |e i|) = ∑ i ∈ P, e i := by
      apply Finset.sum_congr rfl
      intro i hi
      exact abs_of_nonneg (Finset.mem_filter.mp hi).2
    have hm' : (∑ i ∈ M, |e i|) = -(∑ i ∈ M, e i) := by
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro i hi
      exact abs_of_neg (not_le.mp (Finset.mem_filter.mp hi).2)
    rw [hp',hm',sub_eq_add_neg]
  change (∑ i, |e i|) ≤ _
  rw [he]
  change |C.offset + countMean μ nullSignLaw C.flow.outputWeight + ∑ i ∈ P, e i| ≤ C.bias at hp
  change |C.offset + countMean μ nullSignLaw C.flow.outputWeight + ∑ i ∈ M, e i| ≤ C.bias at hm
  linarith [(abs_le.mp hp).2, (abs_le.mp hm).1]

def restrictedSignPrior (S : Set Gap) (hS : MeasurableSet S) (q : SignLaw) : SignLaw := by
  classical
  refine ⟨S.indicator q.val, q.property.1.indicator hS, ?_⟩
  intro d
  by_cases hd : d ∈ S
  · simpa [Set.indicator_of_mem hd] using q.property.2 d
  · simp [Set.indicator_of_notMem hd]

theorem restrictedSignPrior_mean (μ : Measure Gap) (S : Set Gap)
    (hS : MeasurableSet S) (q : SignLaw) :
    signMean μ (restrictedSignPrior S hS q).val = ∫ d in S, q.val d ∂μ :=
  integral_indicator hS

theorem restrictedSignPrior_weighted_integral (μ : Measure Gap) (S : Set Gap)
    (hS : MeasurableSet S) (q : SignLaw) (f : Gap → ℝ) :
    (∫ d, (restrictedSignPrior S hS q).val d*f d ∂μ) = ∫ d in S, q.val d*f d ∂μ := by
  have he : (fun d => (restrictedSignPrior S hS q).val d*f d) =
      S.indicator (fun d => q.val d*f d) := by
    funext d
    by_cases hd : d ∈ S <;> simp [restrictedSignPrior,hd]
  rw [he,integral_indicator hS]

theorem restrictedSignPriors_sum_le_one {I : Type} [Fintype I]
    (S : I → Set Gap) (hS : ∀ i, MeasurableSet (S i))
    (hd : Pairwise (fun i j => Disjoint (S i) (S j))) (q : I → SignLaw) :
    ∀ d, ∑ i, (restrictedSignPrior (S i) (hS i) (q i)).val d ≤ 1 := by
  classical
  intro d
  by_cases he : ∃ i, d ∈ S i
  · obtain ⟨i,hi⟩ := he
    rw [Finset.sum_eq_single i]
    · simpa [restrictedSignPrior,hi] using ((q i).property.2 d).2
    · intro j _ hji
      have hj : d ∉ S j := fun hj => Set.disjoint_left.mp (hd hji) hj hi
      simp [restrictedSignPrior,hj]
    · simp
  · push Not at he
    simp [restrictedSignPrior,he]

theorem certificate_disjoint_component_bias_budget {I : Type} [Fintype I] {N : ℕ}
    (μ : Measure Gap) [IsProbabilityMeasure μ] (ρ B : ℝ)
    (C : Certificate N) (hC : Feasible μ ρ B C)
    (S : I → Set Gap) (hS : ∀ i, MeasurableSet (S i))
    (hd : Pairwise (fun i j => Disjoint (S i) (S j))) (q : I → SignLaw)
    (hρ : ∑ i, (∫ d in S i, (q i).val d ∂μ) ≤ ρ) :
    (∑ i, |∫ d in S i, (q i).val d * (biasPolynomial C).eval (d:ℝ) ∂μ|) ≤ 2*C.bias := by
  have h := certificate_component_bias_budget μ ρ B C hC
    (fun i => restrictedSignPrior (S i) (hS i) (q i))
    (restrictedSignPriors_sum_le_one S hS hd q)
    (by simpa only [restrictedSignPrior_mean] using hρ)
  simpa only [restrictedSignPrior_weighted_integral] using h

def pastedSignPrior {I : Type} [Fintype I]
    (S : I → Set Gap) (hS : ∀ i, MeasurableSet (S i))
    (hd : Pairwise (fun i j => Disjoint (S i) (S j))) (q : I → SignLaw) : SignLaw :=
  finiteSumPrior (fun i => restrictedSignPrior (S i) (hS i) (q i))
    (restrictedSignPriors_sum_le_one S hS hd q) Finset.univ

theorem pastedSignPrior_apply {I : Type} [Fintype I]
    (S : I → Set Gap) (hS : ∀ i, MeasurableSet (S i))
    (hd : Pairwise (fun i j => Disjoint (S i) (S j))) (q : I → SignLaw)
    (i : I) (d : Gap) (hi : d ∈ S i) :
    (pastedSignPrior S hS hd q).val d = (q i).val d := by
  classical
  change (∑ j, (restrictedSignPrior (S j) (hS j) (q j)).val d) = _
  rw [Finset.sum_eq_single i]
  · simp [restrictedSignPrior,hi]
  · intro j _ hji
    have hj : d ∉ S j := fun hj => Set.disjoint_left.mp (hd hji) hj hi
    simp [restrictedSignPrior,hj]
  · simp

theorem pastedSignPrior_rare {I : Type} [Fintype I]
    (μ : Measure Gap) [IsProbabilityMeasure μ] (ρ : ℝ)
    (S : I → Set Gap) (hS : ∀ i, MeasurableSet (S i))
    (hd : Pairwise (fun i j => Disjoint (S i) (S j))) (q : I → SignLaw)
    (hρ : ∑ i, (∫ d in S i, (q i).val d ∂μ) ≤ ρ) :
    RarePrior μ ρ (pastedSignPrior S hS hd q) :=
  finiteSumPrior_rare μ ρ _ _ (by simpa only [restrictedSignPrior_mean] using hρ) _

theorem countMean_restrict_congr {N : ℕ} (μ : Measure Gap)
    (S : Set Gap) (hS : MeasurableSet S) (q r : SignLaw)
    (he : ∀ d ∈ S, q.val d = r.val d) (u : CountState N → ℝ) :
    countMean (μ.restrict S) q u = countMean (μ.restrict S) r u := by
  unfold countMean
  apply Finset.sum_congr rfl
  intro s _
  congr 1
  unfold countCoefficient
  congr 1
  apply setIntegral_congr_fun hS
  intro d hd
  dsimp only
  rw [he d hd]

theorem countMean_disjoint_restrictions_le {I : Type} [Fintype I] {N : ℕ}
    (μ : Measure Gap) [IsFiniteMeasure μ]
    (S : I → Set Gap) (hS : ∀ i, MeasurableSet (S i))
    (hd : Pairwise (fun i j => Disjoint (S i) (S j)))
    (q : SignLaw) (u : CountState N → ℝ) (hu : ∀ s, 0 ≤ u s) :
    (∑ i, countMean (μ.restrict (S i)) q u) ≤ countMean μ q u := by
  classical
  unfold countMean
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro s _
  have hi := integrable_count_mixture μ q s.1.val s.2.val
  have hnonneg : ∀ d : Gap, 0 ≤ q.val d*prefixLikelihood true s.1.val s.2.val d+
      (1-q.val d)*prefixLikelihood false s.1.val s.2.val d := by
    intro d
    exact add_nonneg (mul_nonneg (q.property.2 d).1 (prefixLikelihood_nonneg _ _ _ _))
      (mul_nonneg (sub_nonneg.mpr (q.property.2 d).2) (prefixLikelihood_nonneg _ _ _ _))
  have hle := setIntegral_le_integral (s := ⋃ i, S i) hi (Filter.Eventually.of_forall hnonneg)
  rw [integral_iUnion_fintype hS hd (fun _ => hi.integrableOn)] at hle
  unfold countCoefficient
  rw [← Finset.sum_mul, ← Finset.mul_sum]
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hle (Nat.cast_nonneg _)) (hu s)

theorem countMean_pasted_components_le {I : Type} [Fintype I] {N : ℕ}
    (μ : Measure Gap) [IsFiniteMeasure μ]
    (S : I → Set Gap) (hS : ∀ i, MeasurableSet (S i))
    (hd : Pairwise (fun i j => Disjoint (S i) (S j)))
    (q : I → SignLaw) (u : CountState N → ℝ) (hu : ∀ s, 0 ≤ u s) :
    (∑ i, countMean (μ.restrict (S i)) (q i) u) ≤ countMean μ (pastedSignPrior S hS hd q) u := by
  have he (i) : countMean (μ.restrict (S i)) (q i) u =
      countMean (μ.restrict (S i)) (pastedSignPrior S hS hd q) u :=
    countMean_restrict_congr μ (S i) (hS i) _ _
      (fun d hi => (pastedSignPrior_apply S hS hd q i d hi).symm) u
  simp_rw [he]
  exact countMean_disjoint_restrictions_le μ S hS hd _ u hu

theorem certificate_disjoint_component_moment_budget {I : Type} [Fintype I] {N : ℕ}
    (μ : Measure Gap) [IsProbabilityMeasure μ] (ρ B : ℝ)
    (C : Certificate N) (hC : Feasible μ ρ B C)
    (S : I → Set Gap) (hS : ∀ i, MeasurableSet (S i))
    (hd : Pairwise (fun i j => Disjoint (S i) (S j))) (q : I → SignLaw)
    (hρ : ∑ i, (∫ d in S i, (q i).val d ∂μ) ≤ ρ) :
    (∑ i, countMean (μ.restrict (S i)) (q i) C.flow.momentWeight) ≤ C.variance :=
  (countMean_pasted_components_le μ S hS hd q _ hC.cone.moment_nonneg).trans
    (hC.variance_bound _ (pastedSignPrior_rare μ ρ S hS hd q hρ))

theorem certificate_disjoint_component_work_budget {I : Type} [Fintype I] {N : ℕ}
    (μ : Measure Gap) [IsProbabilityMeasure μ] (ρ B : ℝ)
    (C : Certificate N) (hC : Feasible μ ρ B C)
    (S : I → Set Gap) (hS : ∀ i, MeasurableSet (S i))
    (hd : Pairwise (fun i j => Disjoint (S i) (S j))) (q : I → SignLaw)
    (hρ : ∑ i, (∫ d in S i, (q i).val d ∂μ) ≤ ρ) :
    (∑ i, countMean (μ.restrict (S i)) (q i) C.flow.continueWeight) ≤ B :=
  (countMean_pasted_components_le μ S hS hd q _ hC.cone.continue_nonneg).trans
    (hC.work_bound _ (pastedSignPrior_rare μ ρ S hS hd q hρ))

end ThresholdHC.EntropyTailLower
