import ThresholdHC.Confidence.Testing
import ThresholdHC.ObservedState.Experiment

noncomputable section
open MeasureTheory InformationTheory
open scoped ENNReal
namespace ThresholdHC.ObservedState
open ThresholdHC ThresholdHC.Tier6

/-- Exact binary testing cost, including a common zero-density event. -/
theorem event_information_lower {Ω : Type} [MeasurableSpace Ω]
    (P Q : Measure Ω) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (E : Set Ω) (hE : MeasurableSet E) {e : ℝ} (he : 0 < e) (he1 : e < 1 / 2)
    (hP : 1 - e ≤ P.real E) (hQ : Q.real E ≤ e) :
    ENNReal.ofReal (klB (1 - e) e) ≤ klDiv P Q := by
  classical
  by_cases htop : klDiv P Q = ∞
  · simp [htop]
  have hac := (klDiv_ne_top_iff.mp htop).1
  have hQpos : 0 < Q E := by
    by_contra hn
    have hzero : Q E = 0 := le_antisymm (not_lt.mp hn) bot_le
    have hpzero : P.real E = 0 := (measureReal_eq_zero_iff).mpr (hac hzero)
    linarith
  have hQcpos : 0 < Q Eᶜ := by
    have hc : 0 < Q.real Eᶜ := by rw [probReal_compl_eq_one_sub hE]; linarith
    exact (ENNReal.toReal_pos_iff.mp hc).1
  let test : Ω → Bool := fun x => decide (x ∈ E)
  have htrue : test ⁻¹' {true} = E := by ext x; simp [test]
  have hfalse : test ⁻¹' {false} = Eᶜ := by ext x; simp [test]
  have hm : Measurable test := by
    apply measurable_to_bool
    rw [htrue]
    exact hE
  have hmapQ (b : Bool) : 0 < (Q.map test) {b} := by
    rw [Measure.map_apply hm (measurableSet_singleton b)]
    cases b
    · simpa [hfalse] using hQcpos
    · simpa [htrue] using hQpos
  have hmap (M : Measure Ω) (b : Bool) :
      (M.map test).real {b} = if b then M.real E else M.real Eᶜ := by
    rw [map_measureReal_apply hm (measurableSet_singleton b)]
    cases b <;> simp [htrue,hfalse]
  have hkl : klDiv (P.map test) (Q.map test) = ENNReal.ofReal (klB (P.real E) (Q.real E)) := by
    rw [klDiv_finite_of_positive (P.map test) (Q.map test) hmapQ]
    simp only [Fintype.sum_bool,hmap,Bool.false_eq_true,ite_false,ite_true]
    rw [probReal_compl_eq_one_sub hE,probReal_compl_eq_one_sub hE]
    congr 1
  have hsep := Proofs.Tier2Information.kl_test_separation e (P.real E) (Q.real E)
    he he1 measureReal_nonneg measureReal_le_one
    (ENNReal.toReal_pos hQpos.ne' (measure_ne_top Q _)) hQ hP
  exact (ENNReal.ofReal_le_ofReal hsep).trans (hkl.symm ▸ klDiv_map_le P Q hm)

/-- Uniform validity for deterministic sign arrays passes to a product prior.
A prior exceptional event contributes its own probability. -/
theorem bayes_event_bound {m : ℕ} {R : Type} [MeasurableSpace R]
    (A : Estimator m R) (d : Fin m → Gap) (q : Fin m → unitInterval)
    (E : Set (R × ThresholdHC.Tier3.ProcessTape)) (bad : Set (Fin m → Bool))
    {δ : ℝ}
    (hgood : ∀ s, s ∉ bad → modelLaw A d s E ≤ ENNReal.ofReal δ) :
    bayesLaw A d q E ≤ ENNReal.ofReal δ + signLaw q bad := by
  classical
  have hpoint (s : Fin m → Bool) :
      modelLaw A d s E ≤ ENNReal.ofReal δ + (if s ∈ bad then 1 else 0) := by
    by_cases hs : s ∈ bad
    · simp only [ite_eq_left hs]
      exact (prob_le_one : modelLaw A d s E ≤ 1).trans (le_add_left le_rfl)
    · simpa only [ite_eq_right hs,add_zero] using hgood s hs
  have hbad : (∑ s : Fin m → Bool, (signLaw q) {s} * (if s ∈ bad then 1 else 0)) = signLaw q bad := by
    simp_rw [mul_comm ((signLaw q) {_})]
    rw [← lintegral_fintype]
    change (∫⁻ s, bad.indicator (fun _ => 1) s ∂signLaw q) = _
    exact lintegral_indicator_fun_one (Set.toFinite bad).measurableSet
  rw [bayesLaw,Measure.finsetSum_apply]
  simp only [Measure.smul_apply,smul_eq_mul]
  calc
    _ ≤ ∑ s, (signLaw q) {s} * (ENNReal.ofReal δ + (if s ∈ bad then 1 else 0)) :=
      Finset.sum_le_sum (fun s _ => mul_le_mul' le_rfl (hpoint s))
    _ = _ := by
      simp only [mul_add,Finset.sum_add_distrib]
      rw [← Finset.sum_mul,signLaw_total,one_mul,hbad]

end ThresholdHC.ObservedState
