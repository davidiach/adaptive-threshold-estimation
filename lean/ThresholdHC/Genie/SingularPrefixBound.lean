import ThresholdHC.Genie.UniformPrefixes

/-! Prefix information in the explicit singular example grows at most
linearly in depth against the auxiliary uniform Bernoulli mixture. -/

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace ThresholdHC.Genie
open ThresholdHC.Tier6 ThresholdHC.StoppingProgram

theorem singular_prefix_information (n k : ℕ) (hk : k ≤ n) :
    prefixInformation uniformGapLaw singularExamplePriors n k ≤
      ENNReal.ofReal (3/8*(n:ℝ)*prefixCoefficient uniformGapLaw uniformSignPrior n k) := by
  by_cases hn : n = 0
  · subst n
    have hk0 : k = 0 := by omega
    subst k
    simp [prefixInformation_root]
  have hn1 : (1:ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  let u := uniformMoment k (n-k)
  let v := prefixCoefficient uniformGapLaw singularVariancePrior n k
  let δ := prefixCoefficient uniformGapLaw singularExamplePriors.high n k-
    prefixCoefficient uniformGapLaw singularExamplePriors.low n k
  have hu : 0 < u := uniformMoment_pos _ _
  have hv : 0 < v := by
    dsimp [v]
    rw [singular_variance_prefix_moment]
    exact mul_pos (by norm_num) (uniformMoment_pos _ _)
  have hg : |δ| ≤ u/2 := singular_prefix_gap n k
  have hr : ((n:ℝ)+2)*v = 2*((n-k:ℕ)+1)*u := by
    have h := uniformMoment_recurrence k (n-k)
    have he : (k:ℝ)+(n-k:ℕ) = n := by exact_mod_cast (Nat.add_sub_of_le hk)
    dsimp [u,v]
    rw [singular_variance_prefix_moment]
    rw [he] at h
    nlinarith
  have hb : 0 ≤ (n-k:ℕ) := Nat.zero_le _
  have hbr : (0:ℝ) ≤ (n-k:ℕ) := Nat.cast_nonneg _
  have hlin : 2*u ≤ 3*(n:ℝ)*v := by
    nlinarith [mul_nonneg hbr hu.le,mul_nonneg (sub_nonneg.mpr hn1) hv.le]
  have hsq : δ^2 ≤ u^2/4 := by
    obtain ⟨hlo,hhi⟩ := abs_le.mp hg
    nlinarith [mul_nonneg (show 0 ≤ u/2-δ by linarith) (show 0 ≤ u/2+δ by linarith)]
  change perspective δ v ≤ _
  rw [perspective_pos hv,uniform_prefix_moment]
  apply ENNReal.ofReal_le_ofReal
  apply (div_le_iff₀ hv).mpr
  change δ^2 ≤ (3/8*(n:ℝ)*u)*v
  have hmul := mul_le_mul_of_nonneg_right hlin (show 0 ≤ u/8 by positivity)
  nlinarith

end ThresholdHC.Genie
