import ThresholdHC.BlindUpper.MarkedCall
import ThresholdHC.BlindUpper.FirstSuccess

noncomputable section
namespace ThresholdHC.BlindUpper
open MeasureTheory ProbabilityTheory ThresholdHC.CriticalEntropy
open scoped ENNReal

theorem prefix_product_current_expectation {X : Type} [MeasurableSpace X]
    (ν : Measure X) [IsProbabilityMeasure ν] (f g : X → ℝ≥0∞)
    (hf : Measurable f) (hg : Measurable g) (i : ℕ) :
    (∫⁻ z : ℕ → X, (∏ j ∈ Finset.range i, f (z j))*g (z i)
      ∂Measure.infinitePi (fun _ : ℕ => ν)) = (∫⁻ x, f x ∂ν)^i*(∫⁻ x, g x ∂ν) := by
  let F (j : ℕ) : X → ℝ≥0∞ := if j=i then g else f
  have hF (j : ℕ) : Measurable (F j) := by dsimp [F]; split_ifs <;> assumption
  have hind := iIndepFun_infinitePi (P := fun _ : ℕ => ν) (X := F) hF
  have he (z : ℕ → X) : (∏ j ∈ Finset.range (i+1), F j (z j)) =
      (∏ j ∈ Finset.range i, f (z j))*g (z i) := by
    rw [Finset.prod_range_succ]
    congr 1
    · apply Finset.prod_congr rfl
      intro j hj
      simp [F,ne_of_lt (Finset.mem_range.mp hj)]
    · simp [F]
  have hE (j : ℕ) : (∫⁻ z : ℕ → X, F j (z j) ∂Measure.infinitePi (fun _ : ℕ => ν)) =
      ∫⁻ x, F j x ∂ν :=
    (measurePreserving_eval_infinitePi (fun _ : ℕ => ν) j).lintegral_comp (hF j)
  calc
    _ = ∫⁻ z : ℕ → X, ∏ j ∈ Finset.range (i+1), F j (z j) ∂Measure.infinitePi (fun _ : ℕ => ν) :=
      lintegral_congr (fun z => (he z).symm)
    _ = ∏ j ∈ Finset.range (i+1), ∫⁻ z : ℕ → X, F j (z j) ∂Measure.infinitePi (fun _ : ℕ => ν) :=
      lintegral_prod_eq_prod_lintegral_of_indepFun _ _ hind
        (fun j => (hF j).comp (measurable_pi_apply j))
    _ = _ := by
      simp_rw [hE]
      rw [Finset.prod_range_succ]
      have hprod : (∏ j ∈ Finset.range i, ∫⁻ x, F j x ∂ν) =
          (∫⁻ x, f x ∂ν)^i := by
        calc
          _ = ∏ _ ∈ Finset.range i, ∫⁻ x, f x ∂ν := by
            apply Finset.prod_congr rfl
            intro j hj
            simp [F,ne_of_lt (Finset.mem_range.mp hj)]
          _ = _ := by simp
      rw [hprod]
      simp [F]


def failureWeight {X : Type} (P : X → unitInterval) (z : X × ℝ) : ℝ≥0∞ :=
  if callMark P z then 0 else 1

theorem measurable_failureWeight {X : Type} [MeasurableSpace X]
    (P : X → unitInterval) (hP : Measurable P) : Measurable (failureWeight P) :=
  (measurable_of_countable (fun b : Bool => if b then (0 : ℝ≥0∞) else 1)).comp
    (measurable_callMark P hP)

theorem failureWeight_mean {X : Type} [MeasurableSpace X]
    (ν : Measure X) [IsProbabilityMeasure ν] (P : X → unitInterval) (hP : Measurable P) :
    (∫⁻ z, failureWeight P z ∂ν.prod uniformUnitMeasure) =
      ENNReal.ofReal (1-(meanParameter ν P hP : ℝ)) := by
  have he : failureWeight P = {z | callMark P z = false}.indicator (fun _ => (1 : ℝ≥0∞)) := by
    funext z
    cases h : callMark P z <;> simp [failureWeight,h,Set.indicator_apply]
  rw [he,lintegral_indicator_fun_one
    (measurableSet_eq_fun (measurable_callMark P hP) measurable_const)]
  have hs : {z | callMark P z = false} = {z | callMark P z = true}ᶜ := by
    ext z; cases h : callMark P z <;> simp [h]
  rw [hs,prob_compl_eq_one_sub
    (measurableSet_eq_fun (measurable_callMark P hP) measurable_const),callMark_true ν P hP,
    ENNReal.ofReal_sub 1 (meanParameter ν P hP).property.1]
  simp

/-- Total actual call costs through the first mark, retaining infinite work. -/
def firstPilotWork {X : Type} (P : X → unitInterval) (C : X → ℝ≥0∞)
    (z : ℕ → X × ℝ) : ℝ≥0∞ :=
  ∑' i, (∏ j ∈ Finset.range i, failureWeight P (z j))*C (z i).1

theorem measurable_firstPilotTerm {X : Type} [MeasurableSpace X]
    (P : X → unitInterval) (hP : Measurable P) (C : X → ℝ≥0∞) (hC : Measurable C) (i : ℕ) :
    Measurable (fun z : ℕ → X × ℝ => (∏ j ∈ Finset.range i, failureWeight P (z j))*C (z i).1) := by
  apply Measurable.mul
  · apply Finset.measurable_prod
    intro j hj
    exact (measurable_failureWeight P hP).comp (measurable_pi_apply j)
  · exact hC.comp ((measurable_pi_apply i).fst)

theorem measurable_firstPilotWork {X : Type} [MeasurableSpace X]
    (P : X → unitInterval) (hP : Measurable P) (C : X → ℝ≥0∞) (hC : Measurable C) :
    Measurable (firstPilotWork P C) :=
  Measurable.tsum (fun i => measurable_firstPilotTerm P hP C hC i)

theorem firstPilotWork_of_stop {X : Type} (P : X → unitInterval) (C : X → ℝ≥0∞)
    (z : ℕ → X × ℝ) (n : ℕ) (hn : firstSuccess (fun i => callMark P (z i)) = n) :
    firstPilotWork P C z = ∑ i ∈ Finset.range (n+1), C (z i).1 := by
  classical
  obtain ⟨hn,hi⟩ := (firstSuccess_eq _ n).mp hn
  have hprefix (i : ℕ) (hin : i ≤ n) : (∏ j ∈ Finset.range i, failureWeight P (z j)) = 1 := by
    apply Finset.prod_eq_one
    intro j hj
    simp [failureWeight,hi j (lt_of_lt_of_le (Finset.mem_range.mp hj) hin)]
  have hzero (i : ℕ) (hin : n < i) : (∏ j ∈ Finset.range i, failureWeight P (z j)) = 0 := by
    apply Finset.prod_eq_zero (Finset.mem_range.mpr hin)
    simp [failureWeight,hn]
  unfold firstPilotWork
  rw [tsum_eq_sum (s := Finset.range (n+1)) (fun i hi => by
    have hin : n < i := by simp only [Finset.mem_range] at hi; omega
    rw [hzero i hin,zero_mul])]
  apply Finset.sum_congr rfl
  intro i hi
  rw [hprefix i (by simpa only [Finset.mem_range,Nat.lt_succ_iff] using hi),one_mul]

theorem firstPilotWork_expectation {X : Type} [MeasurableSpace X]
    (ν : Measure X) [IsProbabilityMeasure ν] (P : X → unitInterval) (hP : Measurable P)
    (C : X → ℝ≥0∞) (hC : Measurable C) :
    (∫⁻ z, firstPilotWork P C z ∂Measure.infinitePi (fun _ : ℕ => ν.prod uniformUnitMeasure)) =
      (ENNReal.ofReal (meanParameter ν P hP : ℝ))⁻¹ * ∫⁻ x, C x ∂ν := by
  unfold firstPilotWork
  rw [lintegral_tsum (fun i => (measurable_firstPilotTerm P hP C hC i).aemeasurable)]
  simp_rw [prefix_product_current_expectation (ν.prod uniformUnitMeasure) (failureWeight P)
    (fun z => C z.1) (measurable_failureWeight P hP) (hC.comp measurable_fst),failureWeight_mean ν P hP]
  rw [ENNReal.tsum_mul_right,ENNReal.tsum_geometric]
  have he : 1-ENNReal.ofReal (1-(meanParameter ν P hP : ℝ)) =
      ENNReal.ofReal (meanParameter ν P hP : ℝ) := by
    rw [← ENNReal.ofReal_one,← ENNReal.ofReal_sub 1
      (sub_nonneg.mpr (meanParameter ν P hP).property.2)]
    congr 1
    ring
  rw [he]
  congr 1
  have hm : Measurable (fun z : X × ℝ => C z.1) := hC.comp measurable_fst
  rw [lintegral_prod _ hm.aemeasurable]
  simp


end ThresholdHC.BlindUpper
