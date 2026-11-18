import ThresholdHC.LargeBudgetRMS.LargeBudgetPrice
import ThresholdHC.LargeBudgetRMS.LargeBudgetPopulation
import ThresholdHC.SharpRMS.Reduction
import ThresholdHC.SharpRMS.OracleReduction

/-! Uniform coefficients for the ordinary and both magnitude-oracle experiments. -/
noncomputable section
namespace ThresholdHC.SharpRMS.LargeBudget
open MeasureTheory Tier6 OracleLower
open scoped ENNReal

/-- The three original minimax risks, normalized by the same gap-law modulus. -/
def lowerForAll (μ : Measure Gap) [IsProbabilityMeasure μ] (B r : ℝ) : Prop :=
  let L := ENNReal.ofReal (modulus μ (1/Real.sqrt B)*r)
  L ≤ minimaxRisk μ B ∧ L ≤ revealedMinimaxRisk μ B ∧ L ≤ selectedMinimaxRisk μ B

/-- An explicit, budget-dependent three-bias lower certificate. -/
theorem logarithmic_lower (μ : Measure Gap) [IsProbabilityMeasure μ] (B r : ℝ) (hb : 25≤B)
    (hr : 0<r)
    (test : 4*(tilt+2*weight)*r^2 - Real.log (1-4*bias^2/B)*B ≤ floorLog+2*(1-intercept)) :
    lowerForAll μ B r := by
  have hB : 0<B := by linarith
  have root : (5:ℝ) ≤ Real.sqrt B := (Real.le_sqrt (by norm_num) hB.le).2 (by linarith)
  have hp : 0<Real.sqrt B := by linarith
  let g : Gap := ⟨1/Real.sqrt B,one_div_pos.mpr hp,(div_le_iff₀ hp).2 (by linarith)⟩
  have crit : (2*g.val)^2*B=4 := by
    change (2*(1/Real.sqrt B))^2*B=4
    field_simp [hp.ne']
    nlinarith only [Real.sq_sqrt hB.le]
  have hg : 2*g.val<1 := by
    change 2*(1/Real.sqrt B)<1
    rw [mul_one_div,div_lt_iff₀ hp]; linarith
  have eq : bias^2*(2*g.val)^2 = 4*bias^2/B := (eq_div_iff hB.ne').2 (by
    rw [mul_assoc,crit]; ring)
  have low := critical_of_price g B r hr hg crit (by unfold charge; rw [eq]; linarith only [test])
  let L := ENNReal.ofReal (modulus μ g.val)*ENNReal.ofReal r
  have oracle (R : Type) [MeasurableSpace R] (A : OracleEstimator R) (ha : OracleBudget A B) :
      L ≤ oracleRisk μ A := (mul_le_mul_right low _).trans (oracle_gap_reduction μ g A B ha)
  unfold lowerForAll
  change ENNReal.ofReal (modulus μ g.val*r) ≤ _ ∧ ENNReal.ofReal (modulus μ g.val*r) ≤ _ ∧
    ENNReal.ofReal (modulus μ g.val*r) ≤ _
  rw [ENNReal.ofReal_mul (modulus_pos μ g.property.1).le]
  refine ⟨(mul_le_mul_right low _).trans (critical_gap_reduction μ g B),?_,?_⟩
  · apply le_sInf
    rintro _ ⟨R,mR,A,ha,rfl⟩
    exact oracle _ (revealedOracle μ A) ha
  · apply le_sInf
    rintro _ ⟨R,mR,A,ha,rfl⟩
    exact oracle R (selectedOracle A) ha

private theorem cutoff_lower (μ : Measure Gap) [IsProbabilityMeasure μ] (B N r : ℝ)
    (hN : 25≤N) (hb : N≤B) (hr : 0<r)
    (certificate : -((floorLog+2*(1-intercept)-4*(tilt+2*weight)*r^2)/N) ≤ Real.log (1-4*bias^2/N)) :
    lowerForAll μ B r := by
  have np : 0<N := by linarith
  have hn : 4*bias^2<N := lt_of_lt_of_le (by norm_num) hN
  have h := log_price_mono (4*bias^2) (by norm_num) hn (hn.trans_le hb) hb
  have atN := mul_le_mul_of_nonneg_right certificate np.le
  rw [neg_mul,div_mul_cancel₀ _ np.ne'] at atN
  apply logarithmic_lower μ B r (hN.trans hb) hr
  linear_combination h + atN

theorem lower_25 (μ : Measure Gap) [IsProbabilityMeasure μ] (B : ℝ) (hb : 25≤B) :
    lowerForAll μ B (17356166/100000000) := by
  apply cutoff_lower μ B 25 _ (by norm_num) hb (by norm_num)
  apply rational_log_price _ _ (by norm_num) (by norm_num) 8
  norm_num [Finset.sum_range_succ,Nat.factorial]

theorem lower_100 (μ : Measure Gap) [IsProbabilityMeasure μ] (B : ℝ) (hb : 100≤B) :
    lowerForAll μ B (17623782/100000000) := by
  apply cutoff_lower μ B 100 _ (by norm_num) hb (by norm_num)
  apply rational_log_price _ _ (by norm_num) (by norm_num) 8
  norm_num [Finset.sum_range_succ,Nat.factorial]

end ThresholdHC.SharpRMS.LargeBudget
