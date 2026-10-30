import ThresholdHC.CriticalEntropy.BernoulliPrefix

/-! Negative-reference likelihoods under any positive-sign Bernoulli law.
A normalized tilted law dominates the nonnegative likelihood process, giving
a prefix proof of the crossing bound without conditioning on stopping. -/

noncomputable section
open MeasureTheory Set Real
open scoped ENNReal BigOperators

namespace ThresholdHC.EntropyTailUpper
open ThresholdHC ThresholdHC.Tier2 ThresholdHC.CriticalEntropy

def tiltNormalizer (p r : ℝ) : ℝ := p*(1-2*r)+(1-p)*(1+2*r)

theorem tiltNormalizer_bounds (p : unitInterval) {r : ℝ}
    (hp : 1/2 ≤ (p:ℝ)) (hr0 : 0 ≤ r) (hr1 : r ≤ 1/4) :
    0 < tiltNormalizer p r ∧ tiltNormalizer p r ≤ 1 := by
  have h₁ := mul_nonneg hr0 (sub_nonneg.mpr p.property.2)
  have h₂ := mul_nonneg hr0 (show 0 ≤ 2*(p:ℝ)-1 by linarith)
  unfold tiltNormalizer
  constructor <;> nlinarith

def tiltedParameter (p : unitInterval) {r : ℝ}
    (hp : 1/2 ≤ (p:ℝ)) (hr0 : 0 ≤ r) (hr1 : r ≤ 1/4) : unitInterval :=
  ⟨(p:ℝ)*(1-2*r)/tiltNormalizer p r, by
    have hz := (tiltNormalizer_bounds p hp hr0 hr1).1
    refine ⟨div_nonneg (mul_nonneg p.property.1 (by linarith)) hz.le, (div_le_one hz).2 ?_⟩
    have hb := mul_nonneg (sub_nonneg.mpr p.property.2) (show 0 ≤ 1+2*r by linarith)
    unfold tiltNormalizer
    linarith⟩

theorem tilted_bit_bound (p : unitInterval) {r : ℝ}
    (hp : 1/2 ≤ (p:ℝ)) (hr0 : 0 ≤ r) (hr1 : r ≤ 1/4) (b : Bool) :
    (if b then (p:ℝ) else 1-(p:ℝ)) * (if b then 1/2-r else 1/2+r) ≤
      (1/2) * (if b then (tiltedParameter p hp hr0 hr1 : ℝ)
        else 1-(tiltedParameter p hp hr0 hr1 : ℝ)) := by
  have hz := tiltNormalizer_bounds p hp hr0 hr1
  have he : (if b then (p:ℝ) else 1-(p:ℝ)) * (if b then 1/2-r else 1/2+r) =
      (tiltNormalizer p r/2) * (if b then (tiltedParameter p hp hr0 hr1 : ℝ)
        else 1-(tiltedParameter p hp hr0 hr1 : ℝ)) := by
    cases b <;> simp only [Bool.false_eq_true, ite_false, ite_true, tiltedParameter]
    · field_simp [hz.1.ne']
      unfold tiltNormalizer
      ring
    · field_simp [hz.1.ne']
  rw [he]
  apply mul_le_mul_of_nonneg_right (by linarith [hz.2])
  cases b
  · exact sub_nonneg.mpr (tiltedParameter p hp hr0 hr1).property.2
  · exact (tiltedParameter p hp hr0 hr1).property.1

theorem streamProb_nonneg_of_unit (p : unitInterval) {n : ℕ} (w : Fin n → Bool) :
    0 ≤ streamProb p w := by
  apply Finset.prod_nonneg
  intro i _
  split
  · exact p.property.1
  · exact sub_nonneg.mpr p.property.2

theorem tilted_prefix_bound (p : unitInterval) {r : ℝ}
    (hp : 1/2 ≤ (p:ℝ)) (hr0 : 0 ≤ r) (hr1 : r ≤ 1/4)
    {n : ℕ} (w : Fin n → Bool) :
    streamProb p w * streamProb (1/2-r) w ≤
      streamProb (1/2) w * streamProb (tiltedParameter p hp hr0 hr1) w := by
  unfold streamProb
  rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  apply Finset.prod_le_prod₀
  · intro i _
    apply mul_nonneg
    · split
      · exact p.property.1
      · exact sub_nonneg.mpr p.property.2
    · split <;> linarith
  · intro i _
    simpa only [show (1:ℝ)-(1/2-r) = 1/2+r by ring,
      show (1:ℝ)-1/2=1/2 by norm_num, ite_self] using tilted_bit_bound p hp hr0 hr1 (w i)

theorem negative_reference_crossing_dominates (p : unitInterval) {r c : ℝ}
    (hp : 1/2 ≤ (p:ℝ)) (hr0 : 0 ≤ r) (hr1 : r ≤ 1/4) (hc : 0 ≤ c)
    {n : ℕ} (w : Fin n → Bool) (hcross : streamProb (1/2) w ≤ c * streamProb (1/2-r) w) :
    streamProb p w ≤ c * streamProb (tiltedParameter p hp hr0 hr1) w := by
  have hfair : 0 < streamProb (1/2) w := streamProb_pos _ (by norm_num) (by norm_num) w
  apply (mul_le_mul_iff_left₀ hfair).mp
  calc
    _ ≤ streamProb p w * (c * streamProb (1/2-r) w) := by
      exact mul_le_mul_of_nonneg_left hcross (streamProb_nonneg_of_unit p w)
    _ = c * (streamProb p w * streamProb (1/2-r) w) := by ring
    _ ≤ c * (streamProb (1/2) w * streamProb (tiltedParameter p hp hr0 hr1) w) :=
      mul_le_mul_of_nonneg_left (tilted_prefix_bound p hp hr0 hr1 w) hc
    _ = _ := by ring

end ThresholdHC.EntropyTailUpper
