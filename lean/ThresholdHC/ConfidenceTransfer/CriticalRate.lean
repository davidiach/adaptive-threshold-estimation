import ThresholdHC.ConfidenceTransfer.CriticalModel

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace ThresholdHC.ConfidenceTransfer
open ThresholdHC.Tier6 ThresholdHC.CriticalEntropy ThresholdHC.ObservableSimulation
open ThresholdHC.RareAboveTwo

/-- The critical obstruction supplies the common pair before the local
policy is chosen, with b = ρ/32 and J proportional to ρ L(1+log L). -/
theorem critical_common_pair_bound :
    ∃ a : ℝ, 0 < a ∧ ∀ ρ : ℝ, 0 < ρ → ρ ≤ 1/4 →
      CommonPairBound criticalPositiveLaw ρ (ρ/32) (a*(ρ*criticalLogFactor ρ)) := by
  obtain ⟨C,hC,hpair⟩ := critical_common_capped_pair
  refine ⟨42/C,by positivity,?_⟩
  intro ρ hρ hup s hs hsb
  let ρ' : unitInterval := ⟨ρ,hρ.le,by linarith⟩
  obtain ⟨q,r,hq,hr,hsep,hlocal⟩ := hpair ρ' hρ hup s hs.le (by change s ≤ ρ/96; linarith)
  have hL := criticalLogFactor_pos ρ hρ ρ'.property.2
  refine ⟨criticalSign q hq.1,criticalSign r hr.1,?_,?_,fun d => hq.2.1 d,
    fun d => hr.2.1 d,?_,?_⟩
  · exact (critical_sign_mean q hq.1).le.trans hq.2.2
  · exact (critical_sign_mean r hr.1).le.trans hr.2.2
  · rwa [critical_sign_mean r hr.1,critical_sign_mean q hq.1]
  apply critical_local_transfer q r hq.1 hr.1
  intro R E _ _ ν _ A n hn
  have h := hlocal R E ν A n hn
  have hκ : 42*s^2/(42/C*(ρ*criticalLogFactor ρ)) = C*s^2/(ρ*criticalLogFactor ρ) := by
    field_simp
  rw [hκ,div_mul_eq_mul_div]
  apply (le_div_iff₀ (mul_pos hρ hL)).2
  simpa only [ρ',mul_assoc] using h

/-- The critical high-confidence lower bound in the original observable model,
under a uniform expected flip budget and global integral rarity constraint. -/
theorem critical_confidence_lower : CriticalConfidenceLowerStatement := by
  obtain ⟨a,ha,hpair⟩ := critical_common_pair_bound
  let d := min (1/32 : ℝ) (Real.sqrt a)
  have hd : 0 < d := lt_min (by norm_num) (Real.sqrt_pos.mpr ha)
  refine ⟨d/128,by positivity,?_⟩
  intro ρ B δ hρ hρ' hB hδ hδ'
  let x := ρ*criticalLogFactor ρ*Real.log (1/δ)/B
  have hL := criticalLogFactor_pos ρ hρ (by linarith)
  have hr := minimax_confidence_rate_of_common_pair criticalPositiveLaw
    (by positivity : 0 < ρ/32) (mul_pos ha (mul_pos hρ hL)) hB hδ hδ' (hpair ρ hρ hρ')
  have he : a*(ρ*criticalLogFactor ρ)*Real.log (1/δ)/B = a*x := by dsimp [x]; ring
  rw [he,Real.sqrt_mul ha.le] at hr
  refine (ENNReal.ofReal_le_ofReal ?_).trans hr
  change d/128*min ρ (Real.sqrt x) ≤ min (ρ/32) (Real.sqrt a*Real.sqrt x)/128
  rw [div_mul_eq_mul_div]
  apply div_le_div_of_nonneg_right _ (by norm_num)
  apply le_min
  · calc d*min ρ (Real.sqrt x) ≤ (1/32)*ρ :=
           mul_le_mul (min_le_left _ _) (min_le_left _ _) (le_min hρ.le (Real.sqrt_nonneg _)) (by norm_num)
         _ = _ := by ring
  · exact mul_le_mul (min_le_right _ _) (min_le_right _ _) (le_min hρ.le (Real.sqrt_nonneg _))
      (Real.sqrt_nonneg _)

end ThresholdHC.ConfidenceTransfer
