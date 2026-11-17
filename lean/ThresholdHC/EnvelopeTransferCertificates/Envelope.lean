import ThresholdHC.FiniteLawCertificates.Oracles
import ThresholdHC.ArbitraryLawAdaptation.ZeroQuantile
import ThresholdHC.ArbitraryLawAdaptation.CDFEnvelope

noncomputable section
open MeasureTheory
open scoped ENNReal BigOperators Classical
namespace ThresholdHC.EnvelopeTransferCertificates
open ThresholdHC.Tier6 ThresholdHC.FiniteLawCertificates
open ThresholdHC.ArbitraryLawAdaptation

def extendedAtomic {n : ℕ} (z : ℚ) (d : Fin n → Gap) (w : Fin n → ℚ) : Measure ℝ :=
  ENNReal.ofReal (z:ℝ) • Measure.dirac 0 + (atomicMeasure d w).map Subtype.val

theorem map_atomic {n : ℕ} {α : Type*} [MeasurableSpace α] (d : Fin n → Gap)
    (w : Fin n → ℚ) (f : Gap → α) (hf : Measurable f) :
    (atomicMeasure d w).map f = ∑ i, ENNReal.ofReal (w i:ℝ) • Measure.dirac (f (d i)) := by
  unfold atomicMeasure
  rw [Measure.map_finset_sum' hf.aemeasurable]
  simp only [Measure.map_smul _ hf.aemeasurable, Measure.map_dirac' hf]

theorem extendedAtomic_finite {n : ℕ} (z : ℚ) (d : Fin n → Gap) (w : Fin n → ℚ) :
    IsFiniteMeasure (extendedAtomic z d w) := by
  let := atomicMeasure_finite d w
  unfold extendedAtomic
  have : IsFiniteMeasure (ENNReal.ofReal (z:ℝ) • Measure.dirac (0:ℝ)) :=
    (Measure.dirac (0:ℝ)).smul_finite ENNReal.ofReal_ne_top
  infer_instance

theorem extendedAtomic_probability {n : ℕ} (z : ℚ) (d : Fin n → Gap) (w : Fin n → ℚ)
    (hz : 0 ≤ z) (hw : ∀ i, 0 ≤ w i) (hs : z+∑ i,w i=1) :
    IsProbabilityMeasure (extendedAtomic z d w) := by
  constructor
  rw [extendedAtomic, Measure.add_apply, Measure.map_apply measurable_subtype_coe MeasurableSet.univ]
  simp only [Measure.smul_apply, Measure.dirac_apply_of_mem (Set.mem_univ _), smul_eq_mul,
    mul_one, Set.preimage_univ, atomicMeasure_univ d w hw]
  rw [← ENNReal.ofReal_add (by exact_mod_cast hz) (by exact_mod_cast Finset.sum_nonneg (fun i _ => hw i)),
    ← Rat.cast_add, hs]
  norm_num

theorem extendedAtomic_zero {n : ℕ} (z : ℚ) (d : Fin n → Gap) (w : Fin n → ℚ) :
    extendedAtomic z d w {0} = ENNReal.ofReal (z:ℝ) := by
  simp [extendedAtomic, mappedGap_zero_atom]

theorem fallback_selection {n : ℕ} (z : ℚ) (d : Fin n → Gap) (w : Fin n → ℚ)
    {ρ B : ℝ} (hρ : 0 < ρ) (hB : 0 < B) (hz : ρ ≤ (z:ℝ)) :
    zeroSelection (extendedAtomic z d w) ρ B = ENNReal.ofReal ρ := by
  let := extendedAtomic_finite z d w
  apply le_antisymm (min_le_left _ _)
  have h := min_zeroMass_le_zeroSelection (extendedAtomic z d w) hρ hB
  rw [extendedAtomic_zero, min_eq_left (ENNReal.ofReal_le_ofReal hz)] at h
  exact h

theorem extended_integral {n : ℕ} (z : ℚ) (d : Fin n → Gap) (w : Fin n → ℚ)
    (hz : 0 ≤ z) (hw : ∀ i, 0 ≤ w i) (f : ℝ → ℝ) :
    (∫ x, f x ∂extendedAtomic z d w) = (z:ℝ)*f 0 + ∑ i, (w i:ℝ)*f (d i) := by
  rw [extendedAtomic, map_atomic d w Subtype.val measurable_subtype_coe]
  have hf (i : Fin n) : Integrable f (ENNReal.ofReal (w i:ℝ) • Measure.dirac (d i:ℝ)) :=
    (integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top
  rw [integral_add_measure ((integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top)
    (integrable_finsetSum_measure.mpr (fun i _ => hf i)),
    integral_finsetSum_measure (fun i _ => hf i)]
  simp [ENNReal.toReal_ofReal (show (0:ℝ) ≤ z by exact_mod_cast hz),
    fun i => ENNReal.toReal_ofReal (show (0:ℝ) ≤ w i from by exact_mod_cast hw i)]

theorem normalized_identity {n : ℕ} (z : ℚ) (d : Fin n → Gap) (w : Fin n → ℚ)
    (hz : z < 1) :
    extendedAtomic z d w = zeroAtomLaw (z:ℝ) (atomicMeasure d (fun i => w i/(1-z))) := by
  have he : atomicMeasure d w = ENNReal.ofReal ((1-z:ℚ):ℝ) • atomicMeasure d (fun i => w i/(1-z)) := by
    rw [← atomicMeasure_smul d _ (1-z) (by linarith)]
    congr 1
    funext i
    field_simp
  rw [extendedAtomic, he, map_val_smul, zeroAtomLaw]
  push_cast
  rfl

theorem scaled_core {n : ℕ} (z : ℚ) (d : Fin n → Gap) (w s : Fin n → ℚ)
    (hz : z < 1) {ρ : ℝ}
    (hcore : ThresholdHC.EntropyTailQuantile.quantileCore
      (atomicMeasure d (fun i => w i/(1-z))) ρ =
        atomicMeasure d (fun i => (w i/(1-z))*s i)) :
    ENNReal.ofReal (1-(z:ℝ)) • ThresholdHC.EntropyTailQuantile.quantileCore
      (atomicMeasure d (fun i => w i/(1-z))) ρ = atomicMeasure d (fun i => w i*s i) := by
  rw [hcore, show (1-(z:ℝ))=((1-z:ℚ):ℝ) by push_cast; rfl,
    ← atomicMeasure_smul d _ (1-z) (by linarith)]
  congr 1
  funext i
  field_simp

def extendCDF {n : ℕ} (c : Fin (n+1) → ℚ) (j : ℕ) : ℝ := (c ⟨min j n, by omega⟩:ℝ)

theorem extendCDF_nonneg {n : ℕ} (c : Fin (n+1) → ℚ) (hc : ∀ i, 0 ≤ c i) :
    ∀ j, 0 ≤ extendCDF c j := by intro j; unfold extendCDF; exact_mod_cast hc _

theorem extendCDF_antitone {n : ℕ} (c : Fin (n+1) → ℚ) (hc : Antitone c) :
    Antitone (extendCDF c) := by
  intro i j hij
  apply Rat.cast_le.mpr
  exact hc (min_le_min_right n hij)

end ThresholdHC.EnvelopeTransferCertificates
