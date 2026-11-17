import ThresholdHC.GenieRate.Flow
import ThresholdHC.SquareRootCap.Specification

noncomputable section
open MeasureTheory
open scoped ENNReal

namespace ThresholdHC.SquareRootCap
open ThresholdHC.Tier6 ThresholdHC.StoppingProgram ThresholdHC.Genie
  ThresholdHC.GenieRate ThresholdHC.RareAboveTwo

/-- Choose the midpoint mixing weight from the ordinary information price.
The strict upper bound on the weight also covers a zero ordinary price. -/
private theorem mixing_weight {B K n k : ℝ} (hB : 0 < B) (hK : 0 ≤ K)
    (hk : 1 < k) (hcap : B ≤ n * (k - 1/k)^2) :
    let D := k^2*K + 4*(k^2-1)/B
    ∃ e : ℝ, 0 < e ∧ e < 1 ∧ 4/e ≤ D*e*n ∧ K ≤ D*(1-e)^2 := by
  let p := 2 / Real.sqrt B
  let u := Real.sqrt K
  let v := p * (k - 1/k)
  let D := k^2*K + 4*(k^2-1)/B
  have hk0 : 0 < k := by linarith
  have hk2 : 0 < k^2-1 := by nlinarith [sq_nonneg (k-1)]
  have hbk := Real.sq_sqrt hB.le
  have hp : 0 < p := by dsimp [p]; positivity
  have hp2 : p^2 = 4/B := by
    dsimp [p]; rw [div_pow, hbk]; norm_num
  have hpg : 0 < k - 1/k := sub_pos.mpr ((div_lt_iff₀ hk0).2 (by nlinarith))
  have hv : 0 < v := mul_pos hp hpg
  have hu : 0 ≤ u := Real.sqrt_nonneg _
  have hu2 : u^2 = K := Real.sq_sqrt hK
  have hDeq : D = k^2*u^2 + p^2*(k^2-1) := by
    rw [hu2, hp2]; dsimp [D]; ring
  have hgap : D-(u+v)^2 = (k^2-1)*(u-p/k)^2 := by
    rw [hDeq]; dsimp [v]; field_simp; ring
  have hsum : (u+v)^2 ≤ D := by nlinarith only [hgap, mul_nonneg hk2.le (sq_nonneg (u-p/k))]
  have hstrict : v^2 < D := by
    have hi : D-v^2 = k^2*u^2 + (p/k)^2*(k^2-1) := by
      rw [hDeq]; dsimp [v]; field_simp; ring
    have hi' : 0 < (p/k)^2*(k^2-1) := mul_pos (sq_pos_of_pos (div_pos hp hk0)) hk2
    linarith [mul_nonneg (sq_nonneg k) (sq_nonneg u)]
  have hD : 0 < D := (sq_nonneg v).trans_lt hstrict
  let r := Real.sqrt D
  have hr : 0 < r := Real.sqrt_pos.2 hD
  have hr2 : r^2 = D := Real.sq_sqrt hD.le
  have hvr : v < r := by nlinarith only [hstrict, hr2, hr, hv]
  have hur : u+v ≤ r := by nlinarith only [hsum, hr2, hr, hu, hv]
  have hvn : 4 ≤ v^2*n := by
    dsimp [v]; rw [mul_pow, hp2]
    have ht := mul_le_mul_of_nonneg_left hcap (show 0 ≤ 4/B by positivity)
    calc 4 = (4/B)*B := by field_simp
         _ ≤ (4/B)*(n*(k-1/k)^2) := ht
         _ = _ := by ring
  let e := v/r
  have he : 0 < e := div_pos hv hr
  have he1 : e < 1 := (div_lt_one hr).2 hvr
  have hre : r*e = v := by dsimp [e]; field_simp
  have hremaining : u ≤ r*(1-e) := by nlinarith only [hur, hre]
  refine ⟨e, he, he1, (div_le_iff₀ he).2 ?_, ?_⟩
  · change 4 ≤ D*e*n*e
    calc 4 ≤ v^2*n := hvn
         _ = D*e*n*e := by rw [← hr2, ← hre]; ring
  · change K ≤ D*(1-e)^2
    calc K = u^2 := hu2.symm
         _ ≤ (r*(1-e))^2 := pow_le_pow_left₀ hu hremaining 2
         _ = _ := by rw [mul_pow, hr2]

/-- Uniform optimized ordinary/genie comparison at the square-root cap scale. -/
theorem square_root_cap_factor (μ : Measure Gap) [IsProbabilityMeasure μ]
    {ρ B k : ℝ} (hρ : 0 < ρ) (hρ' : ρ ≤ 1/2) (hB : 0 < B) (hk : 1 < k)
    (N : ℕ) (hcap : B ≤ N*(k-1/k)^2) :
    programValue μ ρ B N ≤ ENNReal.ofReal k * genieValue μ ρ B N := by
  obtain ⟨_, Q, hQ, hval, _, hfinite⟩ := strong_four_prior_duality N μ hρ hρ' hB
  let K := (informationRatio μ N Q).toReal
  have hK : 0 ≤ K := ENNReal.toReal_nonneg
  have hKeq : informationRatio μ N Q = ENNReal.ofReal K := (ENNReal.ofReal_toReal hfinite.ne).symm
  have hk0 : 0 < k := by linarith
  have hk2 : 0 < k^2-1 := by nlinarith [sq_nonneg (k-1)]
  let D := k^2*K+4*(k^2-1)/B
  have hD : 0 ≤ D := by dsimp [D]; positivity
  obtain ⟨e, he, he1, hwork, hprice⟩ := mixing_weight hB hK hk hcap
  let F := mixedReferences Q e ⟨he.le, he1.le⟩
  have hF := mixedReferences_admissible μ Q hQ e ⟨he.le, he1.le⟩
  have hgenie : genieInformationRatio μ N F ≤ ENNReal.ofReal D :=
    mixed_genie_price μ Q e ⟨he.le, he1.le⟩ he he1 D hD hwork
      (hKeq.le.trans (ENNReal.ofReal_le_ofReal hprice))
  let A := (ENNReal.ofReal (signMean μ Q.high.val - signMean μ Q.low.val))^2
  have hden : 4+ENNReal.ofReal B*ENNReal.ofReal D =
      ENNReal.ofReal (k^2)*(4+ENNReal.ofReal B*informationRatio μ N Q) := by
    rw [hKeq, ← ENNReal.ofReal_mul hB.le, ← ENNReal.ofReal_mul hB.le,
      ← ENNReal.ofReal_ofNat 4, ← ENNReal.ofReal_add (by norm_num) (mul_nonneg hB.le hD),
      ← ENNReal.ofReal_add (by norm_num) (mul_nonneg hB.le hK), ← ENNReal.ofReal_mul (sq_nonneg _)]
    congr 1
    dsimp [D]; field_simp; ring
  have hquot : A/(4+ENNReal.ofReal B*ENNReal.ofReal D) ≤ genieDualRatio μ B N F :=
    ENNReal.div_le_div_left (add_le_add le_rfl (mul_le_mul_right hgenie (ENNReal.ofReal B))) A
  have hsup : genieDualRatio μ B N F ≤ genieSquared μ ρ B N :=
    le_iSup_of_le F (le_iSup_of_le hF le_rfl)
  have hsq : programSquared μ ρ B N ≤ ENNReal.ofReal (k^2)*genieSquared μ ρ B N := by
    rw [← hval]
    calc dualRatio μ B N Q = ENNReal.ofReal (k^2)*(A/(4+ENNReal.ofReal B*ENNReal.ofReal D)) := by
           rw [hden, ← mul_div_assoc, ENNReal.mul_div_mul_left _ _
             (ENNReal.ofReal_ne_zero_iff.mpr (sq_pos_of_pos hk0)) ENNReal.ofReal_ne_top]
           rfl
         _ ≤ _ := mul_le_mul_right (hquot.trans hsup) _
  have h := ENNReal.rpow_le_rpow hsq (by norm_num : (0:ℝ) ≤ 1/2)
  rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), ENNReal.ofReal_pow hk0.le,
    ← ENNReal.rpow_natCast_mul] at h
  norm_num at h
  exact h

/-- A cap of 4B/9 passes the factor-two stopping test and yields the existing
factor-sixteen minimax certificate. -/
theorem four_ninths_cap (μ : Measure Gap) [IsProbabilityMeasure μ]
    {ρ B : ℝ} (hρ : 0 < ρ) (hρ' : ρ ≤ 1/2) (hB : 0 < B)
    (N : ℕ) (hcap : 4*B/9 ≤ N) :
    programValue μ ρ B N ≤ 2*genieValue μ ρ B N ∧
    rareMinimaxRisk μ ρ B ≤ programValue μ ρ B N ∧
    programValue μ ρ B N ≤ 16*rareMinimaxRisk μ ρ B := by
  have hN : 0 < N := by exact_mod_cast (show 0 < (N:ℝ) by linarith)
  have h := square_root_cap_factor μ hρ hρ' hB (by norm_num : (1:ℝ) < 2) N (by norm_num; linarith)
  norm_num at h
  exact ⟨h, genie_stopping_certificate μ ρ B hρ hρ' hB N hN h⟩

theorem square_root_cap : SquareRootCapStatement := @square_root_cap_factor

theorem four_ninths : FourNinthsCapStatement := @four_ninths_cap

end ThresholdHC.SquareRootCap
