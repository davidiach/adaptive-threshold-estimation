import ThresholdHC.AdditiveConfidence.Decomposition

noncomputable section
open MeasureTheory
open scoped ENNReal NNReal
namespace ThresholdHC.AdditiveConfidence
open ThresholdHC.Tier6

def positiveMeasure (μ : Measure Gap) (q : SignLaw) : Measure Gap :=
  μ.withDensity (fun d => ENNReal.ofReal (q.val d))

theorem positiveMeasure_le (μ : Measure Gap) (q : SignLaw) : positiveMeasure μ q ≤ μ := by
  calc
    _ ≤ μ.withDensity (fun _ => 1) := withDensity_mono (ae_of_all _ (fun d => by
      simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal (q.property.2 d).2))
    _ = μ := by rw [withDensity_const,one_smul]

instance positiveMeasure_finite (μ : Measure Gap) [IsFiniteMeasure μ] (q : SignLaw) :
    IsFiniteMeasure (positiveMeasure μ q) := isFiniteMeasure_of_le μ (positiveMeasure_le μ q)

theorem positiveMeasure_twice_le (μ : Measure Gap) (q : SignLaw) (hq : ∀ d, q.val d ≤ 1/2) :
    (2 : ℝ≥0) • positiveMeasure μ q ≤ μ := by
  apply Measure.le_iff.mpr
  intro S hS
  rw [Measure.smul_apply,positiveMeasure,withDensity_apply _ hS,ENNReal.smul_def,smul_eq_mul]
  change (2 : ℝ≥0∞)*(∫⁻ d in S, ENNReal.ofReal (q.val d) ∂μ) ≤ μ S
  rw [← lintegral_const_mul' _ _ (by norm_num : (2 : ℝ≥0∞) ≠ ∞)]
  calc
    _ ≤ ∫⁻ _ in S, (1 : ℝ≥0∞) ∂μ := by
      apply lintegral_mono
      intro d
      calc
        (2 : ℝ≥0∞)*ENNReal.ofReal (q.val d) = ENNReal.ofReal (2*q.val d) := by
          rw [ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2)]
          norm_num
        _ ≤ ENNReal.ofReal 1 := ENNReal.ofReal_le_ofReal (by linarith [hq d])
        _ = 1 := by simp
    _ = μ S := by simp

theorem positiveMeasure_integral (μ : Measure Gap) [IsProbabilityMeasure μ]
    (q : SignLaw) (F : Gap → ℝ) :
    (∫ d, q.val d*F d ∂μ) = ∫ d, F d ∂positiveMeasure μ q := by
  have hm : Measurable (fun d => ENNReal.ofReal (q.val d)) :=
    ENNReal.measurable_ofReal.comp q.property.1
  have he := integral_withDensity_eq_integral_toReal_smul (μ := μ) hm
    (ae_of_all _ (fun _ => ENNReal.ofReal_lt_top)) F
  simp_rw [ENNReal.toReal_ofReal (q.property.2 _).1,smul_eq_mul] at he
  exact he.symm

theorem positiveMeasure_mass (μ : Measure Gap) [IsProbabilityMeasure μ] (q : SignLaw) :
    (positiveMeasure μ q).real Set.univ = signMean μ q.val := by
  have he := positiveMeasure_integral μ q (fun _ => 1)
  simpa [signMean] using he.symm

def GapMixture.positiveMass {I : Type} [Fintype I] {μ : Measure Gap}
    (M : GapMixture I μ) (q : I → SignLaw) : Measure Gap :=
  ∑ i, M.weight i • positiveMeasure (M.law i) (q i)

instance GapMixture.positiveMass_finite {I : Type} [Fintype I] {μ : Measure Gap}
    (M : GapMixture I μ) (q : I → SignLaw) : IsFiniteMeasure (M.positiveMass q) := by
  unfold GapMixture.positiveMass
  infer_instance

theorem GapMixture.positiveMass_twice_le {I : Type} [Fintype I] {μ : Measure Gap}
    (M : GapMixture I μ) (q : I → SignLaw) (hq : ∀ i d, (q i).val d ≤ 1/2) :
    (2 : ℝ≥0) • M.positiveMass q ≤ μ := by
  calc
    _ = ∑ i, M.weight i • ((2 : ℝ≥0) • positiveMeasure (M.law i) (q i)) := by
      simp only [GapMixture.positiveMass,Finset.smul_sum,smul_comm (2 : ℝ≥0)]
    _ ≤ ∑ i, M.weight i • M.law i := by
      apply Finset.sum_le_sum
      intro i _
      apply Measure.le_iff'.mpr
      intro S
      simp only [Measure.smul_apply,ENNReal.smul_def,smul_eq_mul]
      exact mul_le_mul' le_rfl (positiveMeasure_twice_le (M.law i) (q i) (hq i) S)
    _ ≤ M.residual+∑ i, M.weight i • M.law i := Measure.le_add_left le_rfl
    _ = μ := M.eq_measure.symm

def GapMixture.mixedSign {I : Type} [Fintype I] {μ : Measure Gap}
    (M : GapMixture I μ) (q : I → SignLaw) : SignLaw := halfSign μ (M.positiveMass q)

theorem GapMixture.mixedSign_density {I : Type} [Fintype I] {μ : Measure Gap}
    [IsProbabilityMeasure μ] (M : GapMixture I μ) (q : I → SignLaw)
    (hq : ∀ i d, (q i).val d ≤ 1/2) :
    positiveMeasure μ (M.mixedSign q) = M.positiveMass q :=
  halfSign_density μ _ (M.positiveMass_twice_le q hq)

theorem GapMixture.mixedSign_mean {I : Type} [Fintype I] {μ : Measure Gap}
    [IsProbabilityMeasure μ] (M : GapMixture I μ) (q : I → SignLaw)
    (hq : ∀ i d, (q i).val d ≤ 1/2) :
    signMean μ (M.mixedSign q).val = ∑ i, (M.weight i : ℝ)*signMean (M.law i) (q i).val := by
  rw [show signMean μ (M.mixedSign q).val = (M.positiveMass q).real Set.univ from
    halfSign_mean μ _ (M.positiveMass_twice_le q hq)]
  simp only [GapMixture.positiveMass,Measure.real,Measure.finsetSum_apply,Measure.smul_apply,
    ENNReal.smul_def,smul_eq_mul]
  rw [ENNReal.toReal_sum (fun i _ => ENNReal.mul_ne_top ENNReal.coe_ne_top (measure_ne_top _ _))]
  simp only [ENNReal.toReal_mul,ENNReal.coe_toReal]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Measure.real,positiveMeasure_mass]

end ThresholdHC.AdditiveConfidence
