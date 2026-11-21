import ThresholdHC.LocalizationCounter.CounterLaw
import ThresholdHC.LocalizationCounter.Information
import ThresholdHC.UnbiasedConverse.Tilt
import ThresholdHC.RareAboveTwo.Nonvacuity

/-! The two-point lower bound of Theorem `loc:thm:counter`.

The sign laws put prior `1/2 ± 1/20` on the atom `ρ²` and the common prior `ρ/4`
everywhere else, so every prior is strictly inside `(0,1)` and the two-sided
prior ratio is at most `5/3`. Only flips of the atom carry information; there
the local tilt bound with `d = h = ρ²` and `η = e = 1/20` charges
`tiltCoefficient ρ² (1/20) = 32ρ⁴/400/(1-4/400)²` per flip. Both laws are rare,
since their sign means are at most `0.8ρ`, so the budget `ρ^{-4}` bounds the
plus-law work and the divergence is at most `12800/156816 ≤ 1/8`. The sign means
differ by `ρ/10`, and the existing KL two-point test gives `ρ/40 ≤ R`, which
implies the stated `ρ/100`. The constant estimator `ρ/2` gives `R ≤ ρ/2`. -/
noncomputable section
open MeasureTheory InformationTheory
open scoped ENNReal
namespace ThresholdHC.LocalizationCounter
open ThresholdHC ThresholdHC.Proofs.Transcript
open ThresholdHC.Tier6 ThresholdHC.RareAboveTwo ThresholdHC.UnbiasedConverse

/-- Prior `c` on the atom `ρ²` and `ρ/4` elsewhere. -/
def counterSign (ρ c : ℝ) (x : Gap) : ℝ := if (x : ℝ) = ρ^2 then c else ρ/4

theorem measurable_counterSign (ρ c : ℝ) : Measurable (counterSign ρ c) :=
  Measurable.ite (measurableSet_eq_fun measurable_subtype_coe measurable_const)
    measurable_const measurable_const

theorem counterSign_range (ρ c : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1/4) (hc : 0 < c) (hc1 : c < 1)
    (x : Gap) : 0 < counterSign ρ c x ∧ counterSign ρ c x < 1 := by
  unfold counterSign
  split_ifs
  · exact ⟨hc, hc1⟩
  · constructor <;> linarith

/-- The sign law `counterSign ρ c` as a `SignLaw`. -/
def counterSignLaw (ρ c : ℝ) (h : ∀ x, 0 ≤ counterSign ρ c x ∧ counterSign ρ c x ≤ 1) :
    SignLaw := ⟨counterSign ρ c, measurable_counterSign ρ c, h⟩

theorem counterSign_mean (ρ c : ℝ) (d : Gap) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1/4)
    (hd : (d : ℝ) = ρ^2) (μ : Measure Gap) (hμ : μ = counterLaw ρ d) :
    signMean μ (counterSign ρ c) = ρ*c + (1-ρ)*(ρ/4) := by
  unfold signMean
  rw [hμ, integral_counterLaw ρ d hρ.le (by linarith)]
  have hq : ((quarterGap : Gap) : ℝ) ≠ ρ^2 := by
    rw [quarterGap_val]; nlinarith
  simp [counterSign, hd, hq]

theorem counter_tilt_value (ρ : ℝ) (hρ : 0 < ρ) :
    tiltCoefficient (ρ^2) (1/20) * (1/ρ^4) ≤ 1/8 := by
  have h : tiltCoefficient (ρ^2) (1/20) * (1/ρ^4) = 12800/156816 := by
    unfold tiltCoefficient
    field_simp
    ring
  rw [h]
  norm_num

/-- The explicit two-point lower bound `ρ/40` for every budgeted algorithm. -/
theorem counter_rareRisk_lower {R : Type} [MeasurableSpace R]
    (ρ : ℝ) (d : Gap) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1/4) (hd : (d : ℝ) = ρ^2)
    (μ : Measure Gap) [IsProbabilityMeasure μ] (hμ : μ = counterLaw ρ d)
    (A : AdaptiveEstimator R) (hA : RareBudget μ A ρ (1/ρ^4)) :
    ENNReal.ofReal (ρ/40) ≤ rareRisk μ A ρ := by
  have hpr := counterSign_range ρ (1/2+1/20) hρ hρ1 (by norm_num) (by norm_num)
  have hmr := counterSign_range ρ (1/2-1/20) hρ hρ1 (by norm_num) (by norm_num)
  let qp := counterSignLaw ρ (1/2+1/20) (fun x => ⟨(hpr x).1.le, (hpr x).2.le⟩)
  let qm := counterSignLaw ρ (1/2-1/20) (fun x => ⟨(hmr x).1.le, (hmr x).2.le⟩)
  have hpm : signMean μ qp.val = ρ*(1/2+1/20) + (1-ρ)*(ρ/4) :=
    counterSign_mean ρ _ d hρ hρ1 hd μ hμ
  have hmm : signMean μ qm.val = ρ*(1/2-1/20) + (1-ρ)*(ρ/4) :=
    counterSign_mean ρ _ d hρ hρ1 hd μ hμ
  have hqp : RarePrior μ ρ qp := by
    change signMean μ qp.val ≤ ρ
    rw [hpm]; nlinarith
  have hqm : RarePrior μ ρ qm := by
    change signMean μ qm.val ≤ ρ
    rw [hmm]; nlinarith
  have hc : 0 ≤ tiltCoefficient (ρ^2) (1/20) := by unfold tiltCoefficient; positivity
  have hρ2 : 0 < ρ^2 := by positivity
  have hstep : ∀ (x : Gap) (a b : ℝ), 0 ≤ a → 0 ≤ b → 0 < a+b →
      klB (mixPredict (x:ℝ) (qp.val x) a b) (mixPredict (x:ℝ) (qm.val x) a b) ≤
        tiltCoefficient (ρ^2) (1/20) := by
    intro x a b ha hb hab
    change klB (mixPredict (x:ℝ) (counterSign ρ (1/2+1/20) x) a b)
      (mixPredict (x:ℝ) (counterSign ρ (1/2-1/20) x) a b) ≤ _
    by_cases hx : (x : ℝ) = ρ^2
    · simp only [counterSign, hx, ite_true]
      rw [← hx]
      exact (local_tilt_information x.property.1 x.property.2 (by norm_num) le_rfl
        (hx ▸ hρ2) (by norm_num) (by norm_num) (by rw [hx]) ha hb hab).1
    · simp only [counterSign, hx, ite_false, klB_self]
      exact hc
  have hkl := ratio_experiment_information μ A qp qm (tiltCoefficient (ρ^2) (1/20)) (5/3)
    (1/ρ^4) hc (by norm_num) hpr hmr
    (fun x => by
      change counterSign ρ _ x ≤ 5/3 * counterSign ρ _ x
      unfold counterSign; split_ifs <;> nlinarith)
    (fun x => by
      change 1 - counterSign ρ _ x ≤ 5/3 * (1 - counterSign ρ _ x)
      unfold counterSign; split_ifs <;> nlinarith)
    (fun x => by
      change counterSign ρ _ x ≤ 5/3 * counterSign ρ _ x
      unfold counterSign; split_ifs <;> nlinarith)
    (fun x => by
      change 1 - counterSign ρ _ x ≤ 5/3 * (1 - counterSign ρ _ x)
      unfold counterSign; split_ifs <;> nlinarith)
    hstep (hA qp hqp)
  have hkl8 : klDiv (experimentLaw μ A qp) (experimentLaw μ A qm) ≤ ENNReal.ofReal (1/8:ℝ) :=
    hkl.trans (ENNReal.ofReal_le_ofReal (counter_tilt_value ρ hρ))
  have hne : signMean μ qp.val ≠ signMean μ qm.val := by
    rw [hpm, hmm]; intro h; nlinarith
  have hsq := two_point_risk_lower_of_ne (experimentLaw μ A qp) (experimentLaw μ A qm)
    (populationOutput A) (signMean μ qp.val) (signMean μ qm.val)
    (measurable_populationOutput A) hne hkl8
  have hdiff : (signMean μ qm.val - signMean μ qp.val)^2 = (ρ/10)^2 := by
    rw [hpm, hmm]; ring
  rw [hdiff] at hsq
  have hrms := rms_of_squared_lower (experimentLaw μ A qp) (experimentLaw μ A qm)
    (populationOutput A) (signMean μ qp.val) (signMean μ qm.val) (ρ/10) (by positivity) hsq
  have h40 : ρ/10/4 = ρ/40 := by ring
  rw [h40] at hrms
  apply hrms.trans
  apply max_le
  · exact le_iSup_of_le qp (le_iSup_of_le hqp le_rfl)
  · exact le_iSup_of_le qm (le_iSup_of_le hqm le_rfl)

theorem counter_minimax_lower (ρ : ℝ) (d : Gap) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1/4)
    (hd : (d : ℝ) = ρ^2) (μ : Measure Gap) [IsProbabilityMeasure μ]
    (hμ : μ = counterLaw ρ d) :
    ENNReal.ofReal (ρ/40) ≤ rareMinimaxRisk μ ρ (1/ρ^4) := by
  apply le_sInf
  rintro t ⟨R, _, A, hA, rfl⟩
  exact counter_rareRisk_lower ρ d hρ hρ1 hd μ hμ A hA

/-- The constant estimator `ρ/2` (as in `EntropyTailExecution.minimax_half_rarity`). -/
theorem counter_minimax_upper (μ : Measure Gap) [IsProbabilityMeasure μ] (ρ B : ℝ)
    (hρ : 0 ≤ ρ) : rareMinimaxRisk μ ρ B ≤ ENNReal.ofReal (ρ/2) := by
  have h : rareMinimaxRisk μ ρ B ≤ rareRisk μ (constantEstimator (ρ/2)) ρ :=
    sInf_le ⟨Unit, inferInstance, constantEstimator (ρ/2),
      constant_rare_budget μ ρ B (ρ/2), rfl⟩
  exact h.trans (half_rarity_risk μ ρ hρ)

end ThresholdHC.LocalizationCounter
