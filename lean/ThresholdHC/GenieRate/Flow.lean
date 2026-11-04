import ThresholdHC.GenieRate.Terminal
import ThresholdHC.Genie.RevealResidual

noncomputable section
open MeasureTheory
open scoped ENNReal BigOperators
namespace ThresholdHC.GenieRate
open ThresholdHC.Tier6 ThresholdHC.StoppingProgram ThresholdHC.Genie

def mixedReferences (Q : FourPriors) (e : ℝ) (he : 0 ≤ e ∧ e ≤ 1) : FourPriors :=
  { regularizedPriors Q e he with work := mixPrior (midpointPrior Q.low Q.high) Q.work e he }

theorem mixedReferences_admissible (μ : Measure Gap) [IsProbabilityMeasure μ]
    {ρ : ℝ} (Q : FourPriors) (hQ : Admissible μ ρ Q) (e : ℝ) (he : 0 ≤ e ∧ e ≤ 1) :
    Admissible μ ρ (mixedReferences Q e he) :=
  ⟨hQ.1,hQ.2.1,(regularizedPriors_admissible μ Q hQ e he).2.2.1,
    mixPrior_rare μ _ _ (mixPrior_rare μ _ _ hQ.1 hQ.2.1 (1/2) (by norm_num)) hQ.2.2.2 e he⟩

private theorem mixed_work {N : ℕ} (μ : Measure Gap) [IsProbabilityMeasure μ]
    (Q : FourPriors) (e : ℝ) (he : 0 ≤ e ∧ e ≤ 1) (f : Flow N) :
    countMean μ (mixedReferences Q e he).work f.continueWeight =
      e*countMean μ (midpointPrior Q.low Q.high) f.continueWeight +
      (1-e)*countMean μ Q.work f.continueWeight := by
  simp only [mixedReferences,countMean,mixPrior_countCoefficient,Finset.mul_sum,←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro s _
  ring

private theorem terminal_excess {N : ℕ} (μ : Measure Gap) [IsProbabilityMeasure μ]
    (Q : FourPriors) (e : ℝ) (he : 0 ≤ e ∧ e ≤ 1) (hp : 0 < e) (f : Flow N) (hf : FlowCone f) :
    eRawLayer f.stopWeight (revealGap μ (mixedReferences Q e he)) N ≤
      ENNReal.ofReal ((4/e)*rawLayer f.stopWeight (prefixCoefficient μ (midpointPrior Q.low Q.high)) N) := by
  let m := midpointPrior Q.low Q.high
  have hnn (k : ℕ) := Genie.rawArray_nonneg _ hf.stop_nonneg N k
  have hpn (k : ℕ) := prefixCoefficient_nonneg μ m N k
  unfold eRawLayer rawLayer
  rw [Finset.mul_sum,ENNReal.ofReal_sum_of_nonneg (fun k _ =>
    mul_nonneg (by positivity : 0 ≤ 4/e) (mul_nonneg (hnn k) (hpn k)))]
  apply Finset.sum_le_sum
  intro k _
  have h : revealGap μ (mixedReferences Q e he) N k ≤
      ENNReal.ofReal (4/e)*ENNReal.ofReal (prefixCoefficient μ m N k) :=
    (tsub_le_self : revealGap μ (mixedReferences Q e he) N k ≤ revealReward μ _ N k).trans
      (regularized_reveal_word μ Q e he hp N k)
  refine (mul_le_mul_right h _).trans_eq ?_
  rw [ENNReal.ofReal_mul (by positivity : 0 ≤ 4/e),ENNReal.ofReal_mul (hnn k)]
  ac_rfl

/-- A finite ordinary price and the cost of reaching the cap bound one genie
price when both references are mixed. All work is computed on the same flow. -/
theorem mixed_genie_price {N : ℕ} (μ : Measure Gap) [IsProbabilityMeasure μ]
    (Q : FourPriors) (e : ℝ) (he : 0 ≤ e ∧ e ≤ 1) (hp : 0 < e) (he1 : e < 1)
    (D : ℝ) (hD : 0 ≤ D) (hcost : 4/e ≤ D*e*N)
    (hprice : informationRatio μ N Q ≤ ENNReal.ofReal (D*(1-e)^2)) :
    genieInformationRatio μ N (mixedReferences Q e he) ≤ ENNReal.ofReal D := by
  let m := midpointPrior Q.low Q.high
  apply iSup_le; intro f; apply iSup_le; intro hf; apply iSup_le; intro hi
  let W (q : SignLaw) := countMean μ q f.continueWeight
  have hw (q : SignLaw) : 0 < W q := by
    have h := flow_work_ge_intensity μ q f hf
    rw [hi] at h
    exact zero_lt_one.trans_le h
  have denom (q : SignLaw) := (ENNReal.ofReal_pos.mpr (hw q)).ne'
  apply (ENNReal.div_le_iff (denom _) ENNReal.ofReal_ne_top).2
  have hord : flowInformation μ Q f / ENNReal.ofReal (W Q.work) ≤ informationRatio μ N Q :=
    le_iSup_of_le f (le_iSup_of_le hf (le_iSup_of_le hi le_rfl))
  have hI := (ENNReal.div_le_iff (denom _) ENNReal.ofReal_ne_top).1 (hord.trans hprice)
  have hinter : flowInformation μ (mixedReferences Q e he) f ≤
      ENNReal.ofReal (D*(1-e)*W Q.work) := by
    refine (regularized_flowInformation μ Q e he he1 f).trans ((mul_le_mul_right hI _).trans_eq ?_)
    rw [← ENNReal.ofReal_mul (mul_nonneg hD (sq_nonneg _)),
      ← ENNReal.ofReal_mul (by positivity : 0 ≤ 1/(1-e))]
    congr 1
    field_simp [sub_ne_zero.mpr he1.ne']
  have hmass := terminal_mass_work μ m f hf
  let p := rawLayer f.stopWeight (prefixCoefficient μ m) N
  have hpn : 0 ≤ p := Finset.sum_nonneg (fun k _ =>
    mul_nonneg (Genie.rawArray_nonneg _ hf.stop_nonneg _ _) (prefixCoefficient_nonneg μ m _ _))
  have hterm : (4/e)*p ≤ D*e*W m := calc
    _ ≤ D*e*N*p := mul_le_mul_of_nonneg_right hcost hpn
    _ = D*e*((N:ℝ)*p) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hmass (mul_nonneg hD hp.le)
  rw [genieFlowInformation_gap]
  refine (add_le_add hinter ((terminal_excess μ Q e he hp f hf).trans
    (ENNReal.ofReal_le_ofReal hterm))).trans_eq ?_
  rw [← ENNReal.ofReal_add (mul_nonneg (mul_nonneg hD (sub_nonneg.mpr he.2)) (hw _).le)
    (mul_nonneg (mul_nonneg hD hp.le) (hw _).le),← ENNReal.ofReal_mul hD]
  congr 1
  dsimp only [W,m]
  rw [mixed_work]
  ring

end ThresholdHC.GenieRate
