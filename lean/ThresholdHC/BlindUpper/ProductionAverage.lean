import ThresholdHC.CriticalEntropy.SymmetricReduction

noncomputable section
namespace ThresholdHC.BlindUpper
open MeasureTheory ProbabilityTheory ThresholdHC.CriticalEntropy
open scoped ENNReal

theorem mse_eq_variance_add_bias {X : Type} [MeasurableSpace X]
    (ν : Measure X) [IsProbabilityMeasure ν] (Z : X → ℝ) (hZ : MemLp Z 2 ν) (a : ℝ) :
    (∫ x, (Z x-a)^2 ∂ν) = variance Z ν + ((∫ x, Z x ∂ν)-a)^2 := by
  have hsub : MemLp (fun x => Z x-a) 2 ν := hZ.sub (memLp_const a)
  have h := variance_eq_sub hsub
  rw [variance_sub_const hZ.aestronglyMeasurable] at h
  have hm : (∫ x, Z x-a ∂ν) = (∫ x, Z x ∂ν)-a := by
    rw [integral_sub (hZ.integrable (by norm_num)) (integrable_const a)]
    simp
  rw [hm] at h
  change variance Z ν = (∫ x, (Z x-a)^2 ∂ν)-((∫ x, Z x ∂ν)-a)^2 at h
  linarith

def finiteAverage {X : Type} (Z : X → ℝ) (n : ℕ) (x : Fin (n+1) → X) : ℝ :=
  ((n : ℝ)+1)⁻¹ * ∑ i, Z (x i)

theorem measurable_finiteAverage {X : Type} [MeasurableSpace X]
    (Z : X → ℝ) (hZ : Measurable Z) (n : ℕ) : Measurable (finiteAverage Z n) := by
  apply Measurable.mul measurable_const
  apply Finset.measurable_sum
  intro i hi
  exact hZ.comp (measurable_pi_apply i)

theorem finiteAverage_memLp {X : Type} [MeasurableSpace X]
    (ν : Measure X) [IsProbabilityMeasure ν] (Z : X → ℝ) (hZ : MemLp Z 2 ν) (n : ℕ) :
    MemLp (finiteAverage Z n) 2 (Measure.pi (fun _ : Fin (n+1) => ν)) :=
  (iid_score_memLp ν Z hZ (n+1)).const_mul _

theorem finiteAverage_mean {X : Type} [MeasurableSpace X]
    (ν : Measure X) [IsProbabilityMeasure ν] (Z : X → ℝ) (hZ : MemLp Z 2 ν) (n : ℕ) :
    (∫ x, finiteAverage Z n x ∂Measure.pi (fun _ : Fin (n+1) => ν)) = ∫ x, Z x ∂ν := by
  unfold finiteAverage
  rw [integral_const_mul,iid_score_integral ν Z hZ (n+1)]
  push_cast
  field_simp

theorem finiteAverage_variance {X : Type} [MeasurableSpace X]
    (ν : Measure X) [IsProbabilityMeasure ν] (Z : X → ℝ) (hZ : MemLp Z 2 ν) (n : ℕ) :
    variance (finiteAverage Z n) (Measure.pi (fun _ : Fin (n+1) => ν)) = variance Z ν/((n : ℝ)+1) := by
  unfold finiteAverage
  rw [variance_const_mul,iid_score_variance ν Z hZ (n+1)]
  push_cast
  field_simp

theorem finiteAverage_mse {X : Type} [MeasurableSpace X]
    (ν : Measure X) [IsProbabilityMeasure ν] (Z : X → ℝ) (hZ : MemLp Z 2 ν) (n : ℕ) (a : ℝ) :
    (∫ x, (finiteAverage Z n x-a)^2 ∂Measure.pi (fun _ : Fin (n+1) => ν)) =
      variance Z ν/((n : ℝ)+1) + ((∫ x, Z x ∂ν)-a)^2 := by
  rw [mse_eq_variance_add_bias _ _ (finiteAverage_memLp ν Z hZ n) a,
    finiteAverage_mean ν Z hZ n,finiteAverage_variance ν Z hZ n]

def productionPrefix {X : Type} (n : ℕ) (x : ℕ → X) : Fin (n+1) → X := fun i => x i.val

theorem productionPrefix_preserving {X : Type} [MeasurableSpace X]
    (ν : Measure X) [IsProbabilityMeasure ν] (n : ℕ) :
    MeasurePreserving (productionPrefix (X := X) n) (Measure.infinitePi (fun _ : ℕ => ν))
      (Measure.pi (fun _ : Fin (n+1) => ν)) := by
  refine ⟨Measurable.of_eval (fun i => measurable_pi_apply i.val),?_⟩
  unfold productionPrefix
  rw [Measure.map_infinitePi_infinitePi_of_inj Fin.val_injective,Measure.infinitePi_eq_pi]

def productionAverage {X : Type} (Z : X → ℝ) (n : ℕ) (x : ℕ → X) : ℝ :=
  finiteAverage Z n (productionPrefix n x)

theorem measurable_productionAverage {X : Type} [MeasurableSpace X]
    (Z : X → ℝ) (hZ : Measurable Z) (n : ℕ) : Measurable (productionAverage Z n) :=
  (measurable_finiteAverage Z hZ n).comp (Measurable.of_eval (fun i => measurable_pi_apply i.val))

theorem measurable_productionAverage_joint {X : Type} [MeasurableSpace X]
    (Z : X → ℝ) (hZ : Measurable Z) : Measurable (fun z : ℕ × (ℕ → X) => productionAverage Z z.1 z.2) :=
  measurable_from_prod_countable_right (fun n => measurable_productionAverage Z hZ n)

theorem productionAverage_memLp {X : Type} [MeasurableSpace X]
    (ν : Measure X) [IsProbabilityMeasure ν] (Z : X → ℝ) (hZ : MemLp Z 2 ν) (n : ℕ) :
    MemLp (productionAverage Z n) 2 (Measure.infinitePi (fun _ : ℕ => ν)) :=
  (finiteAverage_memLp ν Z hZ n).comp_measurePreserving (productionPrefix_preserving ν n)

theorem productionAverage_mse {X : Type} [MeasurableSpace X]
    (ν : Measure X) [IsProbabilityMeasure ν] (Z : X → ℝ) (hZm : Measurable Z)
    (hZ : MemLp Z 2 ν) (n : ℕ) (a : ℝ) :
    (∫⁻ x, ENNReal.ofReal ((productionAverage Z n x-a)^2) ∂Measure.infinitePi (fun _ : ℕ => ν)) =
      ENNReal.ofReal (variance Z ν/((n : ℝ)+1) + ((∫ x, Z x ∂ν)-a)^2) := by
  have hm : Measurable (fun x => ENNReal.ofReal ((finiteAverage Z n x-a)^2)) :=
    ENNReal.measurable_ofReal.comp (((measurable_finiteAverage Z hZm n).sub measurable_const).pow_const 2)
  have he := (productionPrefix_preserving ν n).lintegral_comp hm
  have hi : Integrable (fun x => (finiteAverage Z n x-a)^2)
      (Measure.pi (fun _ : Fin (n+1) => ν)) :=
    ((finiteAverage_memLp ν Z hZ n).sub (memLp_const a)).integrable_sq
  change (∫⁻ x, ENNReal.ofReal ((finiteAverage Z n (productionPrefix n x)-a)^2) ∂_) = _
  rw [he,← ofReal_integral_eq_lintegral_ofReal hi
    (ae_of_all _ (fun x => sq_nonneg _)),finiteAverage_mse ν Z hZ n a]

end ThresholdHC.BlindUpper
