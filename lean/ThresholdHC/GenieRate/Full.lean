import ThresholdHC.GenieRate.Flow
import ThresholdHC.Genie.OptimizedBrackets

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace ThresholdHC.GenieRate
open ThresholdHC.Tier6 ThresholdHC.StoppingProgram ThresholdHC.Genie ThresholdHC.RareAboveTwo

set_option maxHeartbeats 800000 in
/-- Explicit relative convergence of the optimized finite programs, uniformly
over the gap law. The optimization may change both reference priors. -/
theorem optimized_cap_factor (μ : Measure Gap) [IsProbabilityMeasure μ]
    {ρ B k : ℝ} (hρ : 0 < ρ) (hρ' : ρ ≤ 1/2) (hB : 0 < B) (hk : 1 < k)
    (N : ℕ) (hcap : B ≤ N*(1-1/k)^2*(k^2-1)) :
    programValue μ ρ B N ≤ ENNReal.ofReal k*genieValue μ ρ B N := by
  obtain ⟨_,Q,hQ,hval,_,hfinite⟩ := strong_four_prior_duality N μ hρ hρ' hB
  let K := (informationRatio μ N Q).toReal
  have hK : 0 ≤ K := ENNReal.toReal_nonneg
  have hKeq : informationRatio μ N Q = ENNReal.ofReal K := (ENNReal.ofReal_toReal hfinite.ne).symm
  have hk0 : 0 < k := by linarith
  have hk2 : 1 < k^2 := by nlinarith [sq_nonneg (k-1)]
  let e := 1-1/k
  have he : 0 < e := sub_pos.mpr ((div_lt_one hk0).2 hk)
  have he1 : e < 1 := by dsimp [e]; linarith [one_div_pos.mpr hk0]
  let D := k^2*K+4*(k^2-1)/B
  have hD : 0 ≤ D := add_nonneg (mul_nonneg (sq_nonneg _) hK) (by positivity)
  have hDn : 4/e ≤ D*e*N := by
    have h : 4/e ≤ (4*(k^2-1)/B)*e*N := by
      apply (div_le_iff₀ he).2
      rw [div_mul_eq_mul_div,div_mul_eq_mul_div,div_mul_eq_mul_div]
      apply (le_div_iff₀ hB).2
      change B ≤ (N:ℝ)*e^2*(k^2-1) at hcap
      nlinarith only [hcap]
    exact h.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (le_add_of_nonneg_left (mul_nonneg (sq_nonneg _) hK)) he.le) (Nat.cast_nonneg _))
  have hK' : K ≤ D*(1-e)^2 := by
    calc K = k^2*K*(1-e)^2 := by dsimp [e]; field_simp; ring
         _ ≤ _ := mul_le_mul_of_nonneg_right (le_add_of_nonneg_right (by positivity : 0 ≤ 4*(k^2-1)/B))
           (sq_nonneg _)
  let F := mixedReferences Q e ⟨he.le,he1.le⟩
  have hF := mixedReferences_admissible μ Q hQ e ⟨he.le,he1.le⟩
  have hgenie := mixed_genie_price μ Q e ⟨he.le,he1.le⟩ he he1 D hD hDn
    (hKeq.le.trans (ENNReal.ofReal_le_ofReal hK'))
  let A := (ENNReal.ofReal (signMean μ Q.high.val - signMean μ Q.low.val))^2
  have hden : 4+ENNReal.ofReal B*ENNReal.ofReal D =
      ENNReal.ofReal (k^2)*(4+ENNReal.ofReal B*informationRatio μ N Q) := by
    rw [hKeq,← ENNReal.ofReal_mul hB.le,← ENNReal.ofReal_mul hB.le,
      ← ENNReal.ofReal_ofNat 4,← ENNReal.ofReal_add (by norm_num) (mul_nonneg hB.le hD),
      ← ENNReal.ofReal_add (by norm_num) (mul_nonneg hB.le hK),← ENNReal.ofReal_mul (sq_nonneg _)]
    congr 1
    dsimp [D]; field_simp; ring
  change genieInformationRatio μ N F ≤ ENNReal.ofReal D at hgenie
  have hden' : 4+ENNReal.ofReal B*genieInformationRatio μ N F ≤ 4+ENNReal.ofReal B*ENNReal.ofReal D :=
    add_le_add le_rfl (mul_le_mul_right hgenie (ENNReal.ofReal B))
  have hquot : A/(4+ENNReal.ofReal B*ENNReal.ofReal D) ≤ genieDualRatio μ B N F := by
    change A/(4+ENNReal.ofReal B*ENNReal.ofReal D) ≤ A/(4+ENNReal.ofReal B*genieInformationRatio μ N F)
    exact ENNReal.div_le_div_left hden' A
  have hsup : genieDualRatio μ B N F ≤ genieSquared μ ρ B N :=
    le_iSup_of_le F (le_iSup_of_le hF le_rfl)
  have hsq : programSquared μ ρ B N ≤ ENNReal.ofReal (k^2)*genieSquared μ ρ B N := by
    rw [← hval]
    calc dualRatio μ B N Q = ENNReal.ofReal (k^2)*(A/(4+ENNReal.ofReal B*ENNReal.ofReal D)) := by
           rw [hden,← mul_div_assoc,ENNReal.mul_div_mul_left _ _
             (ENNReal.ofReal_ne_zero_iff.mpr (sq_pos_of_pos hk0)) ENNReal.ofReal_ne_top]
           rfl
         _ ≤ _ := mul_le_mul_right (hquot.trans hsup) _
  have h := ENNReal.rpow_le_rpow hsq (by norm_num : (0:ℝ) ≤ 1/2)
  rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num),ENNReal.ofReal_pow hk0.le,
    ← ENNReal.rpow_natCast_mul] at h
  norm_num at h
  exact h

/-- The factor-two stopping test, and hence the factor-sixteen risk certificate,
already holds when the local cap is at least 4B/3. -/
theorem linear_cap_risk_certificate (μ : Measure Gap) [IsProbabilityMeasure μ]
    {ρ B : ℝ} (hρ : 0 < ρ) (hρ' : ρ ≤ 1/2) (hB : 0 < B)
    (N : ℕ) (hcap : 4*B/3 ≤ N) :
    programValue μ ρ B N ≤ 2*genieValue μ ρ B N ∧
    rareMinimaxRisk μ ρ B ≤ programValue μ ρ B N ∧ programValue μ ρ B N ≤ 16*rareMinimaxRisk μ ρ B := by
  have hN : 0 < N := by exact_mod_cast (show 0 < (N:ℝ) by linarith)
  have h := optimized_cap_factor μ hρ hρ' hB (by norm_num : (1:ℝ) < 2) N (by norm_num; linarith)
  norm_num at h
  exact ⟨h,genie_stopping_certificate μ ρ B hρ hρ' hB N hN h⟩

/-- Relative error is at most 2t once the cap satisfies B ≤ Nt³, for t ≤ 1. -/
theorem cubic_cap_factor (μ : Measure Gap) [IsProbabilityMeasure μ]
    {ρ B t : ℝ} (hρ : 0 < ρ) (hρ' : ρ ≤ 1/2) (hB : 0 < B)
    (ht : 0 < t) (ht' : t ≤ 1) (N : ℕ) (hcap : B ≤ N*t^3) :
    programValue μ ρ B N ≤ ENNReal.ofReal (1+2*t)*genieValue μ ρ B N := by
  apply optimized_cap_factor μ hρ hρ' hB (by linarith)
  apply hcap.trans
  rw [mul_assoc]
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
  have hden : 0 < (1+2*t)^2 := by positivity
  have he : (1-1/(1+2*t))^2*((1+2*t)^2-1) = t^3*(16*(1+t))/(1+2*t)^2 := by
    field_simp
    ring
  rw [he]
  apply (le_div_iff₀ hden).2
  apply mul_le_mul_of_nonneg_left _ (pow_nonneg ht.le _)
  nlinarith [mul_nonneg ht.le (sub_nonneg.mpr ht')]

end ThresholdHC.GenieRate
