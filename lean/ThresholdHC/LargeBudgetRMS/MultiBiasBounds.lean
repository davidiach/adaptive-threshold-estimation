import ThresholdHC.LargeBudgetRMS.MultiBiasCertificate
import ThresholdHC.LargeBudgetRMS.MultiBiasPopulation
import ThresholdHC.LargeBudgetRMS.MultiBiasPrice
import ThresholdHC.LargeBudgetRMS.LargeBudgetBounds

/-! A uniform testing lower bound at every real expected budget B ≥ 25. -/
noncomputable section
namespace ThresholdHC.SharpRMS.MultiBias
open MeasureTheory Real Tier3 Tier5 Tier6 LargeBudget OracleLower
open scoped ENNReal unitInterval

private def clipped {R : Type} [MeasurableSpace R] (A : AdaptiveEstimator R) (z : PopulationSeed R × ProcessTape) :=
  2*HardBudget.clipEstimate 1 (populationOutput A z)-1

private theorem clipped_measurable {R : Type} [MeasurableSpace R] (A : AdaptiveEstimator R) : Measurable (clipped A) :=
  (measurable_const.mul ((HardBudget.measurable_clip 1).comp (measurable_populationOutput A))).sub measurable_const

private theorem clipped_range {R : Type} [MeasurableSpace R] (A : AdaptiveEstimator R) (z) : |clipped A z|≤1 := by
  let v := populationOutput A z
  have hl : 0≤HardBudget.clipEstimate 1 v := le_max_left ..
  have hu : HardBudget.clipEstimate 1 v≤1 := max_le (by norm_num) (min_le_left ..)
  change |2*HardBudget.clipEstimate 1 v-1|≤1
  exact abs_le.mpr ⟨by linarith,by linarith⟩

private theorem small_loss {R : Type} [MeasurableSpace R] (A : AdaptiveEstimator R) (g : Gap)
    (r : ℝ) (hr : 0<r) (small : maximalRMSRisk (Measure.dirac g) A < ENNReal.ofReal r) (t : ℝ) (ht : |t|≤1) :
    expectation A g (fraction t ht) (clipped A) (fun x => (x-t)^2)<4*r^2 := by
  let p := fraction t ht
  let q := flat p
  let P := experimentLaw (Measure.dirac g) A q
  have mean : signMean (Measure.dirac g) q.val=p.val := by simp [signMean,q,flat]
  have rms := (le_iSup (fun q' => rootMeanRisk (experimentLaw (Measure.dirac g) A q')
    (populationOutput A) (signMean (Measure.dirac g) q'.val)) q).trans_lt small
  rw [mean] at rms
  have sq : squaredRisk P (populationOutput A) p.val < ENNReal.ofReal (r^2) := by
    by_contra! bad
    have h := ENNReal.rpow_le_rpow bad (by norm_num : (0:ℝ)≤1/2)
    rw [ofReal_square_rpow_half r hr.le] at h
    exact (not_le_of_gt rms) h
  let E := expectation A g p (clipped A) (fun x => (x-t)^2)
  have le : ENNReal.ofReal E ≤ ENNReal.ofReal 4*squaredRisk P (populationOutput A) p.val := by
    change ENNReal.ofReal (∫ z, (clipped A z-t)^2 ∂P) ≤ _
    rw [ofReal_integral_eq_lintegral_ofReal (output_integrable P _ (clipped_measurable A) (clipped_range A)
      (fun x => (x-t)^2) (by fun_prop)) (ae_of_all _ fun z => sq_nonneg _),squaredRisk,
      ←lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    apply lintegral_mono
    intro z
    have id : (clipped A z-t)^2 = 4*(HardBudget.clipEstimate 1 (populationOutput A z)-p.val)^2 := by
      simp only [clipped,p,fraction]; ring
    change ENNReal.ofReal ((clipped A z-t)^2) ≤ _
    rw [id,ENNReal.ofReal_mul (by norm_num)]
    exact mul_le_mul_right (HardBudget.clip_loss_le 1 p.val _ p.property) _
  have result := le.trans_lt (ENNReal.mul_lt_mul_right (by norm_num : ENNReal.ofReal (4:ℝ)≠0) ENNReal.ofReal_ne_top sq)
  rw [←ENNReal.ofReal_mul (by norm_num)] at result
  by_contra! bad
  exact result.not_ge (ENNReal.ofReal_le_ofReal bad)

theorem critical_lower (g : Gap) (B r : ℝ) (hr : 0<r) (hb : 25≤B) (hg : 2*g.val<1) (hcrit : (2*g.val)^2*B=4)
    (budget : weightSum*(4*r^2-target)+price B≤price 25) :
    ENNReal.ofReal r ≤ minimaxRisk (Measure.dirac g) B := by
  apply le_sInf
  rintro _ ⟨R,mR,A,ha,rfl⟩
  by_contra! small
  let X := clipped A
  let p0 := fraction 0 (by norm_num)
  let P := experimentLaw (Measure.dirac g) A (flat p0)
  let E := expectation A g p0 X
  have pair_le (i : Fin 5) : E (pair i) ≤ charge (2*g.val) (bias i)*B+slope i*(2*(4*r^2-target)) := by
    have h := pair_population A g B ha (by linarith) hg X (clipped_measurable A) (clipped_range A) i
    have p := small_loss A g r hr small (bias i) (bias_lt i).le
    have n := small_loss A g r hr small (-bias i) (by simpa using (bias_lt i).le)
    have add : expectation A g (fraction (bias i) (bias_lt i).le) X (fun x => (x-bias i)^2) +
        expectation A g (fraction (-bias i) (by simpa using (bias_lt i).le)) X (fun x => (x-(-bias i))^2)-2*target ≤ 2*(4*r^2-target) := by
      dsimp only [X]; linarith only [p,n]
    exact h.trans (add_le_add_right (mul_le_mul_of_nonneg_left add (params i).2.2.1.le) _)
  have sum := Finset.sum_le_sum (s:=Finset.univ) (fun i _ => pair_le i)
  simp only [Finset.sum_add_distrib,←Finset.sum_mul] at sum
  rw [charge_sum _ _ (by linarith) hcrit] at sum
  have pi (i : Fin 5) : Integrable (fun z => pair i (X z)) P :=
    output_integrable P X (clipped_measurable A) (clipped_range A) _ (pair_cont i)
  have qi : Integrable (fun z => (X z)^2) P :=
    output_integrable P X (clipped_measurable A) (clipped_range A) (fun x => x^2) (by fun_prop)
  have integ := integral_mono (μ:=P) (integrable_const (tilt*target-25*∑ i, log (cut i)))
    ((qi.const_mul tilt).add (integrable_finsetSum _ fun i _ => pi i))
    (fun z => scalar_test (X z) (clipped_range A z))
  change (∫ _ : PopulationSeed R × ProcessTape, _ ∂P) ≤ ∫ z, tilt*(X z)^2+∑ i, pair i (X z) ∂P at integ
  rw [integral_const,probReal_univ,one_smul,integral_add (qi.const_mul _) (integrable_finsetSum _ fun i _ => pi i),
    integral_const_mul,integral_finsetSum _ (fun i _ => pi i)] at integ
  change tilt*target-25*∑ i, log (cut i) ≤ tilt*E (fun x => x^2)+∑ i, E (pair i) at integ
  have fair := small_loss A g r hr small 0 (by norm_num)
  simp only [sub_zero] at fair
  change E (fun x => x^2)<4*r^2 at fair
  rw [price_25] at budget
  unfold weightSum at budget
  have bad : (0:ℝ)<0 := by
    linear_combination integ + sum + budget + mul_lt_mul_of_pos_left fair (by norm_num : 0<tilt)
  exact (lt_irrefl _ bad)

/-- Ordinary and both magnitude-oracle risks obey the same lower bound. -/
theorem lower_of_price (μ : Measure Gap) [IsProbabilityMeasure μ] (B r : ℝ) (hb : 25≤B) (hr : 0<r)
    (budget : weightSum*(4*r^2-target)+price B≤price 25) :
    lowerForAll μ B r := by
  have hB : 0<B := by linarith
  have root : (5:ℝ) ≤ Real.sqrt B := (Real.le_sqrt (by norm_num) hB.le).2 (by linarith)
  have hp : 0<Real.sqrt B := by linarith
  let g : Gap := ⟨1/Real.sqrt B,one_div_pos.mpr hp,(div_le_iff₀ hp).2 (by linarith)⟩
  have crit : (2*g.val)^2*B=4 := by
    change (2*(1/Real.sqrt B))^2*B=4
    field_simp [hp.ne']; nlinarith only [Real.sq_sqrt hB.le]
  have hg : 2*g.val<1 := by
    change 2*(1/Real.sqrt B)<1
    rw [mul_one_div,div_lt_iff₀ hp]; linarith
  have low := critical_lower g B r hr hb hg crit budget
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

/-- Explicit RMS coefficient obtained by spending the difference between the
two divergence bounds on squared error. -/
theorem lower_curve (μ : Measure Gap) [IsProbabilityMeasure μ] (B : ℝ) (hb : 25≤B) :
    lowerForAll μ B (Real.sqrt (target+(price 25-price B)/weightSum)/2) := by
  have wt : 0<weightSum := add_pos_of_pos_of_nonneg (by norm_num : 0<tilt)
    (mul_nonneg (by norm_num) (Finset.sum_nonneg (fun i _ => (params i).2.2.1.le)))
  have gain := sub_nonneg.mpr (price_decreases 25 B (by norm_num) hb)
  have pos := add_pos_of_pos_of_nonneg (by norm_num : 0<target) (div_nonneg gain wt.le)
  apply lower_of_price μ B _ hb (div_pos (Real.sqrt_pos.mpr pos) (by norm_num))
  have sq := Real.sq_sqrt pos.le
  have eq : 4*(Real.sqrt (target+(price 25-price B)/weightSum)/2)^2-target =
      (price 25-price B)/weightSum := by linarith only [sq]
  rw [eq,mul_comm weightSum,div_mul_cancel₀ _ wt.ne',sub_add_cancel]

theorem lower_25 (μ : Measure Gap) [IsProbabilityMeasure μ] (B : ℝ) (hb : 25≤B) :
    lowerForAll μ B radius := by
  apply lower_of_price μ B radius hb (by norm_num)
  simpa only [target,sub_self,mul_zero,zero_add] using price_decreases 25 B (by norm_num) hb

theorem lower_100 (μ : Measure Gap) [IsProbabilityMeasure μ] (B : ℝ) (hb : 100≤B) :
    lowerForAll μ B radius100 := by
  apply lower_of_price μ B radius100 (by linarith) (by norm_num)
  exact (add_le_add_right (price_decreases 100 B (by norm_num) hb) _).trans gain_100

end ThresholdHC.SharpRMS.MultiBias
