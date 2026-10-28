import ThresholdHC.CriticalUpper.CappedCost

/-! Work integration under a global rarity constraint; no pointwise rarity assumption. -/

noncomputable section
namespace ThresholdHC.CriticalUpper
open MeasureTheory Set ThresholdHC.CriticalEntropy ThresholdHC.Uniform713
open scoped ENNReal

def criticalCappedCost (N K d : ℝ) : ℝ := min N (K/(16*d^2))

theorem criticalCappedCost_nonneg (N K d : ℝ) (hN : 0 ≤ N) (hK : 0 ≤ K) :
    0 ≤ criticalCappedCost N K d := le_min hN (div_nonneg hK (by positivity))

theorem criticalCappedCost_integrable (N K : ℝ) (hN : 0 ≤ N) (hK : 0 ≤ K) :
    Integrable (criticalCappedCost N K) criticalGapLaw := by
  apply Integrable.of_bound (show Measurable (criticalCappedCost N K) by
    unfold criticalCappedCost; fun_prop).aestronglyMeasurable N
  exact ae_of_all _ (fun d => by
    rw [Real.norm_of_nonneg (criticalCappedCost_nonneg N K d hN hK)]
    exact min_le_left _ _)

theorem criticalCappedCost_truncated_integral (N K ρ : ℝ) (hρ : ρ ≤ 1) :
    (∫ d, (Ioc (0 : ℝ) ρ).indicator (fun u => min N (K/u)) (16*d^2) ∂criticalGapLaw) =
      ∫ u in Ioc (0 : ℝ) ρ, min N (K/u) := by
  calc
    _ = ∫ u, (Ioc (0 : ℝ) ρ).indicator (fun u => min N (K/u)) u ∂uniformUnitMeasure := by
      have hm : Measurable (fun u : ℝ => min N (K/u)) := by fun_prop
      rw [← criticalGap_square_map,integral_map (by fun_prop)
        (hm.indicator measurableSet_Ioc).aestronglyMeasurable]
    _ = _ := by
      rw [integral_indicator measurableSet_Ioc,uniformUnitMeasure,
        Measure.restrict_restrict measurableSet_Ioc]
      have he : Ioc (0 : ℝ) ρ ∩ Icc 0 1 = Ioc 0 ρ := by
        apply inter_eq_left.mpr
        intro u hu
        exact ⟨hu.1.le,hu.2.trans hρ⟩
      rw [he]

/-- The global rarity constraint controls the costly positive-coin contribution.
No pointwise upper bound on the sign prior by the rarity is used. -/
theorem criticalCappedCost_weighted_le (N K ρ : ℝ) (hN : 0 < N) (hK : 0 < K)
    (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (q : ℝ → unitInterval) (hq : Measurable q)
    (hmass : (∫ d, (q d : ℝ) ∂criticalGapLaw) ≤ ρ) :
    (∫ d, (q d : ℝ)*criticalCappedCost N K d ∂criticalGapLaw) ≤
      K*(2+max 0 (Real.log (N*ρ/K))) := by
  let f := criticalCappedCost N K
  let g : ℝ → ℝ := fun d =>
    (Ioc (0 : ℝ) ρ).indicator (fun u => min N (K/u)) (16*d^2)
  have hqint : Integrable (fun d => (q d : ℝ)) criticalGapLaw := by
    apply Integrable.of_bound (by fun_prop) 1
    exact ae_of_all _ (fun d => by rw [Real.norm_of_nonneg (q d).property.1]; exact (q d).property.2)
  have hf0 (d : ℝ) : 0 ≤ f d := criticalCappedCost_nonneg N K d hN.le hK.le
  have hfint : Integrable (fun d => (q d : ℝ)*f d) criticalGapLaw := by
    apply Integrable.of_bound (by dsimp [f,criticalCappedCost]; fun_prop) N
    exact ae_of_all _ (fun d => by
      rw [Real.norm_of_nonneg (mul_nonneg (q d).property.1 (hf0 d))]
      exact (mul_le_mul_of_nonneg_right (q d).property.2 (hf0 d)).trans
        (by simpa [f,criticalCappedCost] using (min_le_left N (K/(16*d^2)))))
  have hgint : Integrable g criticalGapLaw := by
    have hm : Measurable (fun u : ℝ => min N (K/u)) := by fun_prop
    have hgm : Measurable g := (hm.indicator measurableSet_Ioc).comp (by fun_prop)
    apply Integrable.of_bound hgm.aestronglyMeasurable N
    exact ae_of_all _ (fun d => by
      by_cases hu : 16*d^2 ∈ Ioc (0 : ℝ) ρ
      · simp only [g,Set.indicator_of_mem hu]
        change ‖criticalCappedCost N K d‖ ≤ N
        rw [Real.norm_of_nonneg (criticalCappedCost_nonneg N K d hN.le hK.le)]
        exact min_le_left _ _
      · simp only [g,Set.indicator_of_notMem hu,norm_zero]
        exact hN.le)
  have hpoint : (fun d => (q d : ℝ)*f d) ≤ᵐ[criticalGapLaw]
      fun d => (K/ρ)*(q d : ℝ)+g d := by
    filter_upwards [criticalGap_ae_support] with d hd
    have hd0 : 0 < 16*d^2 := mul_pos (by norm_num) (sq_pos_of_pos hd.1)
    by_cases hu : 16*d^2 ≤ ρ
    · have hm : 16*d^2 ∈ Ioc (0 : ℝ) ρ := ⟨hd0,hu⟩
      have hg : g d = f d := by simp [g,f,criticalCappedCost,Set.indicator_of_mem hm]
      rw [hg]
      have hqf := mul_le_mul_of_nonneg_right (q d).property.2 (hf0 d)
      have hq0 := (q d).property.1
      have hKρ : 0 ≤ K/ρ := (div_pos hK hρ).le
      nlinarith
    · have hm : 16*d^2 ∉ Ioc (0 : ℝ) ρ := fun h => hu h.2
      have hg : g d = 0 := by simp [g,Set.indicator_of_notMem hm]
      have hf : f d ≤ K/ρ :=
        (min_le_right _ _).trans (div_le_div_of_nonneg_left hK.le hρ (le_of_not_ge hu))
      rw [hg,add_zero]
      exact (mul_le_mul_of_nonneg_left hf (q d).property.1).trans_eq (mul_comm _ _)
  have hle := integral_mono_ae hfint ((hqint.const_mul (K/ρ)).add hgint) hpoint
  simp only [Pi.add_apply] at hle
  rw [integral_add (hqint.const_mul (K/ρ)) hgint,integral_const_mul] at hle
  have hmass' : (K/ρ)*(∫ d, (q d : ℝ) ∂criticalGapLaw) ≤ K := by
    calc
      _ ≤ (K/ρ)*ρ := mul_le_mul_of_nonneg_left hmass (div_pos hK hρ).le
      _ = K := by field_simp
  have hg : (∫ d, g d ∂criticalGapLaw) ≤ K*(1+max 0 (Real.log (N*ρ/K))) := by
    rw [show g = _ from rfl,criticalCappedCost_truncated_integral N K ρ hρ1]
    exact cappedReciprocal_integral_le N K ρ hN hK hρ.le
  dsimp only [f] at hle
  linarith

end ThresholdHC.CriticalUpper
