import ThresholdHC.StoppingProgram.WeakDuality
import ThresholdHC.StoppingProgram.MomentImage

/-! A strictly interior constant sign reference dominates every count law.
It gives a finite-ratio positive dual witness at every finite cap. -/

noncomputable section
open MeasureTheory
open scoped BigOperators ENNReal

namespace ThresholdHC.StoppingProgram
open ThresholdHC.Tier6 (Gap SignLaw signMean)
open ThresholdHC.RareAboveTwo ThresholdHC.CapIdentification

def constantPrior (r : ℝ) (hr : 0 ≤ r ∧ r ≤ 1) : SignLaw :=
  ⟨fun _ => r,measurable_const,fun _ => hr⟩

theorem constantPrior_mean (μ : Measure Gap) [IsProbabilityMeasure μ]
    (r : ℝ) (hr : 0 ≤ r ∧ r ≤ 1) : signMean μ (constantPrior r hr).val = r := by
  simp [signMean,constantPrior]

theorem integrable_count_mixture (μ : Measure Gap) [IsFiniteMeasure μ]
    (q : SignLaw) (n k : ℕ) : Integrable (fun d =>
      q.val d*prefixLikelihood true n k d+(1-q.val d)*prefixLikelihood false n k d) μ := by
  convert (integrable_weighted_prefix μ q true n k).add
    ((integrable_prefixLikelihood μ false n k).sub (integrable_weighted_prefix μ q false n k)) using 1
  ext d
  simp only [Pi.add_apply,Pi.sub_apply]
  ring

theorem countCoefficient_dominated {N : ℕ} (μ : Measure Gap) [IsFiniteMeasure μ]
    (q : SignLaw) (s : CountState N) {r : ℝ} (hr : 0 ≤ r ∧ r ≤ 1) (hrhalf : r ≤ 1/2) :
    r*countCoefficient μ q s ≤ countCoefficient μ (constantPrior r hr) s := by
  have hp : ∀ d : Gap,
      r*(q.val d*prefixLikelihood true s.1.val s.2.val d+
        (1-q.val d)*prefixLikelihood false s.1.val s.2.val d) ≤
      r*prefixLikelihood true s.1.val s.2.val d+(1-r)*prefixLikelihood false s.1.val s.2.val d := by
    intro d
    have hq := q.property.2 d
    have h1 := prefixLikelihood_nonneg true s.1.val s.2.val d
    have h0 := prefixLikelihood_nonneg false s.1.val s.2.val d
    have hA : r*q.val d ≤ r := by nlinarith
    have hB : r*(1-q.val d) ≤ 1-r := by nlinarith
    have ht := add_le_add (mul_le_mul_of_nonneg_right hA h1) (mul_le_mul_of_nonneg_right hB h0)
    nlinarith
  have hi := integral_mono ((integrable_count_mixture μ q s.1.val s.2.val).const_mul r)
    (integrable_count_mixture μ (constantPrior r hr) s.1.val s.2.val) hp
  rw [integral_const_mul] at hi
  have hh := mul_le_mul_of_nonneg_left hi (Nat.cast_nonneg (s.1.val.choose s.2.val))
  change r*(_*_) ≤ _*_
  convert hh using 1
  ring

theorem constantPrior_null_state {N : ℕ} (μ : Measure Gap) [IsFiniteMeasure μ]
    (q : SignLaw) (s : CountState N) {r : ℝ} (hr : 0 < r) (hrhalf : r ≤ 1/2)
    (hzero : countCoefficient μ (constantPrior r ⟨hr.le,by linarith⟩) s = 0) :
    countCoefficient μ q s = 0 := by
  have hh := countCoefficient_dominated μ q s ⟨hr.le,by linarith⟩ hrhalf
  rw [hzero] at hh
  nlinarith [countCoefficient_nonneg μ q s]

theorem informationRatio_finite_of_statewise {N : ℕ} (μ : Measure Gap) [IsProbabilityMeasure μ]
    (Q : FourPriors) (hstate : ∀ s : CountState N,
      perspective (countCoefficient μ Q.high s-countCoefficient μ Q.low s) (countCoefficient μ Q.variance s) ≠ ⊤) :
    informationRatio μ N Q < ⊤ := by
  let S : ℝ≥0∞ := ∑ s : CountState N,
    perspective (countCoefficient μ Q.high s-countCoefficient μ Q.low s) (countCoefficient μ Q.variance s)
  have hS : S ≠ ⊤ := ENNReal.sum_ne_top.mpr (fun s _ => hstate s)
  apply lt_of_le_of_lt (b := S) _ (lt_top_iff_ne_top.mpr hS)
  apply iSup_le
  intro f
  apply iSup_le
  intro hf
  apply iSup_le
  intro hi
  have hI : flowInformation μ Q f ≤ S := by
    apply Finset.sum_le_sum
    intro s _
    have ha : ENNReal.ofReal (f.stopWeight s) ≤ 1 := by
      have hh := ENNReal.ofReal_le_ofReal ((flow_stop_le_intensity f hf s).trans_eq hi)
      simpa using hh
    calc
      _ ≤ 1*perspective (countCoefficient μ Q.high s-countCoefficient μ Q.low s)
          (countCoefficient μ Q.variance s) := by gcongr
      _ = _ := one_mul _
  have hw : 1 ≤ ENNReal.ofReal (countMean μ Q.work f.continueWeight) := by
    have hh := ENNReal.ofReal_le_ofReal (flow_work_ge_intensity μ Q.work f hf)
    simpa [hi] using hh
  apply ENNReal.div_le_of_le_mul
  exact hI.trans (by simpa only [one_mul,mul_comm] using mul_le_mul_left hw S)

theorem positive_dual_witness (N : ℕ) (μ : Measure Gap) [IsProbabilityMeasure μ]
    {ρ B : ℝ} (hρ : 0 < ρ) (hρhalf : ρ ≤ 1/2) :
    ∃ Q : FourPriors, Admissible μ ρ Q ∧ informationRatio μ N Q < ⊤ ∧ 0 < dualRatio μ B N Q := by
  let q := constantPrior ρ ⟨hρ.le,by linarith⟩
  let Q : FourPriors := ⟨nullSignLaw,q,q,nullSignLaw⟩
  have hq : RarePrior μ ρ q := le_of_eq (constantPrior_mean μ _ _)
  have hnull : RarePrior μ ρ nullSignLaw := by simpa [RarePrior,signMean,nullSignLaw] using hρ.le
  have hK : informationRatio μ N Q < ⊤ := by
    apply informationRatio_finite_of_statewise μ Q
    intro s
    apply ne_of_lt
    apply (perspective_finite_iff (countCoefficient_nonneg μ Q.variance s)).mpr
    by_cases hv : countCoefficient μ q s = 0
    · right
      have hl := constantPrior_null_state μ nullSignLaw s hρ hρhalf hv
      change countCoefficient μ q s-countCoefficient μ nullSignLaw s = 0
      rw [hv,hl,sub_self]
    · left
      exact lt_of_le_of_ne (countCoefficient_nonneg μ q s) (Ne.symm hv)
  refine ⟨Q,⟨hnull,hq,hq,hnull⟩,hK,?_⟩
  rw [dualRatio]
  apply ENNReal.div_pos_iff.mpr
  constructor
  · change (ENNReal.ofReal (signMean μ q.val-signMean μ nullSignLaw.val))^2 ≠ 0
    have he : signMean μ q.val-signMean μ nullSignLaw.val = ρ := by
      rw [show signMean μ q.val = ρ from constantPrior_mean μ _ _]
      simp [signMean,nullSignLaw]
    rw [he]
    exact pow_ne_zero _ (ENNReal.ofReal_ne_zero_iff.mpr hρ)
  · exact ENNReal.add_ne_top.mpr ⟨by norm_num,ENNReal.mul_ne_top ENNReal.ofReal_ne_top hK.ne⟩

theorem programSquared_pos (N : ℕ) (μ : Measure Gap) [IsProbabilityMeasure μ]
    {ρ B : ℝ} (hρ : 0 < ρ) (hρhalf : ρ ≤ 1/2) (hB : 0 < B) :
    0 < programSquared μ ρ B N := by
  obtain ⟨Q,hQ,hK,hpos⟩ := positive_dual_witness (B := B) N μ hρ hρhalf
  have hh : dualRatio μ B N Q ≤ dualValue μ ρ B N :=
    le_iSup_of_le Q (le_iSup_of_le hQ le_rfl)
  exact hpos.trans_le (hh.trans (weak_duality μ hB N))

end ThresholdHC.StoppingProgram
