import ThresholdHC.QuantileOptimality.Support

noncomputable section
open MeasureTheory Real Set
open scoped ENNReal BigOperators
namespace ThresholdHC.QuantileOptimality
open ThresholdHC.Tier6 (Gap)
open ThresholdHC.EntropyTailQuantile
open ThresholdHC.BandwiseSuffix (packet)

theorem packet_add {e f : ℝ} (he : 0 ≤ e) (hf : 0 ≤ f) (d : Gap) :
    packet (e+f) d=packet e d+packet f d := by
  unfold packet
  rw [add_mul,ENNReal.ofReal_add (mul_nonneg he (sq_nonneg _)) (mul_nonneg hf (sq_nonneg _)),add_smul]

theorem packet_tailModulus {e : ℝ} (he : 0 ≤ e) (d : Gap) (h : ℝ) :
    tailModulus (packet e d) h=(e*(d : ℝ)^2)*min 1 (h/(d : ℝ)) := by
  simp only [tailModulus,packet,integral_smul_measure,integral_dirac,
    ENNReal.toReal_ofReal (mul_nonneg he (sq_nonneg _)),smul_eq_mul]

theorem packet_tailModulus_of_small {e : ℝ} (he : 0 ≤ e) (d : Gap) {h : ℝ} (hhd : h ≤ (d : ℝ)) :
    tailModulus (packet e d) h=e*h*(d : ℝ) := by
  rw [packet_tailModulus he, min_eq_right ((div_le_one d.property.1).mpr hhd)]
  field_simp

theorem tailModulus_finset_sum {ι : Type*} (s : Finset ι) (μ : ι → Measure Gap)
    [∀ i, IsFiniteMeasure (μ i)] {h : ℝ} (hh : 0 ≤ h) :
    tailModulus (∑ i ∈ s, μ i) h=∑ i ∈ s, tailModulus (μ i) h := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [tailModulus]
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi,tailModulus_add _ _ hh,ih,Finset.sum_insert hi]

theorem packet_sum_mass {ι : Type*} (s : Finset ι) (e : ι → ℝ) (d : ι → Gap)
    (he : ∀ i, 0 ≤ e i) :
    (∑ i ∈ s, packet (e i) (d i)).real univ=∑ i ∈ s, e i*(d i : ℝ)^2 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi,measureReal_add_apply,packet_real_mass (he i),ih,Finset.sum_insert hi]

end ThresholdHC.QuantileOptimality
