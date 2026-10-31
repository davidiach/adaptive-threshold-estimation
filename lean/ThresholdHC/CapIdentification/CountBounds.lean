import ThresholdHC.CapIdentification.CountMatching

/-! Uniform finite envelopes for count coefficients. These coarse envelopes
suffice for a fixed-cap certificate whose variance vanishes with the budget. -/

noncomputable section
open MeasureTheory
open scoped BigOperators

namespace ThresholdHC.CapIdentification
open ThresholdHC.Tier6 (Gap SignLaw)
open ThresholdHC.StoppingProgram

theorem prefixLikelihood_le_one (s : Bool) (n k : ℕ) (d : Gap) : prefixLikelihood s n k d ≤ 1 := by
  have hm : 0 ≤ 1/2-(d:ℝ) := by linarith [d.property.2]
  have hp : 0 ≤ 1/2+(d:ℝ) := by linarith [d.property.1]
  have hm1 : 1/2-(d:ℝ) ≤ 1 := by linarith [d.property.1]
  have hp1 : 1/2+(d:ℝ) ≤ 1 := by linarith [d.property.2]
  cases s <;> simp only [prefixLikelihood,Bool.false_eq_true,ite_false,ite_true]
  · exact (mul_le_mul_of_nonneg_right (pow_le_one₀ hm hm1) (pow_nonneg hp _)).trans
      (by simpa only [one_mul] using pow_le_one₀ hp hp1)
  · exact (mul_le_mul_of_nonneg_right (pow_le_one₀ hp hp1) (pow_nonneg hm _)).trans
      (by simpa only [one_mul] using pow_le_one₀ hm hm1)

theorem countCoefficient_le_choose {N : ℕ} (μ : Measure Gap) [IsProbabilityMeasure μ]
    (q : SignLaw) (s : CountState N) : countCoefficient μ q s ≤ (s.1.val.choose s.2.val:ℝ) := by
  have hle (d : Gap) : q.val d*prefixLikelihood true s.1.val s.2.val d+
      (1-q.val d)*prefixLikelihood false s.1.val s.2.val d ≤ 1 := by
    have h1 := mul_le_mul_of_nonneg_left (prefixLikelihood_le_one true s.1.val s.2.val d) (q.property.2 d).1
    have h0 := mul_le_mul_of_nonneg_left (prefixLikelihood_le_one false s.1.val s.2.val d)
      (sub_nonneg.mpr (q.property.2 d).2)
    nlinarith
  have hi : Integrable (fun d => q.val d*prefixLikelihood true s.1.val s.2.val d+
      (1-q.val d)*prefixLikelihood false s.1.val s.2.val d) μ := by
    convert (integrable_weighted_prefix μ q true s.1.val s.2.val).add
      ((integrable_prefixLikelihood μ false s.1.val s.2.val).sub
        (integrable_weighted_prefix μ q false s.1.val s.2.val)) using 1
    ext d
    simp only [Pi.add_apply,Pi.sub_apply]
    ring
  have hh := integral_mono hi (integrable_const (1:ℝ)) hle
  simp only [integral_const,probReal_univ,smul_eq_mul,one_mul] at hh
  exact (mul_le_mul_of_nonneg_left hh (Nat.cast_nonneg _)).trans_eq (mul_one _)

def countEnvelope (N : ℕ) : ℝ := 1+∑ s : CountState N, (s.1.val.choose s.2.val:ℝ)

theorem countEnvelope_pos (N : ℕ) : 0 < countEnvelope N := by
  have h : 0 ≤ ∑ s : CountState N, (s.1.val.choose s.2.val:ℝ) :=
    Finset.sum_nonneg (fun _ _ => Nat.cast_nonneg _)
  unfold countEnvelope
  linarith

theorem countMean_le_envelope {N : ℕ} (μ : Measure Gap) [IsProbabilityMeasure μ]
    (q : SignLaw) (u : CountState N → ℝ) {M : ℝ} (hM : 0 ≤ M)
    (hu : ∀ s, 0 ≤ u s) (hb : ∀ s, u s ≤ M) : countMean μ q u ≤ M*countEnvelope N := by
  calc
    countMean μ q u ≤ ∑ s : CountState N, (s.1.val.choose s.2.val:ℝ)*M := by
      apply Finset.sum_le_sum
      intro s _
      exact mul_le_mul (countCoefficient_le_choose μ q s) (hb s) (hu s) (Nat.cast_nonneg _)
    _ = M*(∑ s : CountState N, (s.1.val.choose s.2.val:ℝ)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro s _
      ring
    _ ≤ M*countEnvelope N := mul_le_mul_of_nonneg_left (by unfold countEnvelope; linarith) hM

end ThresholdHC.CapIdentification
