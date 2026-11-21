import ThresholdHC.TwoFlipFeedback.Risk
import ThresholdHC.TwoFlipFeedback.UpperPoly
import ThresholdHC.HardBudget.Controller

/-! The feedback witness: flip coin `0`; after a tail flip the fresh coin `1`,
after a head revisit coin `0`; output the rational table. Its exact risk at
every sign law is the polynomial `riskPoly`, so its worst rare risk is at most
`upperValue = 15442587/10^9`. -/

noncomputable section
namespace ThresholdHC.TwoFlipFeedback
open MeasureTheory
open scoped ENNReal
open ThresholdHC.Tier3 ThresholdHC.Tier6 ThresholdHC.RareAboveTwo ThresholdHC.HardBudget

/-- The feedback witness of `full_class-body.tex`. -/
def feedbackEstimator : AdaptiveEstimator Unit where
  randomLaw := Measure.dirac ()
  probability := inferInstance
  policy := fun _ => stopAt 2 feedbackLabel
  policy_measurable := fun _ _ => measurableSet_eq_fun measurable_const measurable_const
  output := fun z => feedbackOutput (processPrefix 2 z.2)
  output_measurable := (measurable_of_countable feedbackOutput).comp
    (Measurable.of_eval fun i => (measurable_pi_apply i.val).comp measurable_snd)

theorem feedback_policy (r : Unit) : feedbackEstimator.policy r = stopAt 2 feedbackLabel := rfl

theorem feedback_output (x : ProcessTape) :
    feedbackEstimator.output ((), x) = feedbackOutput (processPrefix 2 x) := rfl

theorem feedback_cap : PathwiseCap feedbackEstimator 2 :=
  stopAt_pathwise_cap feedbackEstimator 2 (fun _ => feedbackLabel) (fun _ => rfl)

private theorem fb_root : stopAt 2 feedbackLabel [] = some 0 := rfl

private theorem fb_tail : stopAt 2 feedbackLabel [false] = some 1 := rfl

private theorem fb_head : stopAt 2 feedbackLabel [true] = some 0 := rfl

/-- The witness revisits after a head and moves to a fresh coin after a tail,
so it is not of the noninteractive normal form. -/
theorem feedback_not_noninteractive : ¬ NoninteractiveCapTwo feedbackEstimator := by
  intro h
  rcases h () 0 fb_root with ha | ⟨hb, _⟩
  · rcases ha false with h1 | h1
    · exact absurd (fb_tail.symm.trans h1) (by simp)
    · exact absurd (fb_tail.symm.trans h1) (by simp)
  · exact hb true fb_head

/-- The exact risk of the witness at every sign law. -/
theorem feedback_risk (q : SignLaw) :
    squaredRisk (experimentLaw twoGapLaw feedbackEstimator q) (populationOutput feedbackEstimator)
      (signMean twoGapLaw q.val) =
      ENNReal.ofReal (riskPoly (drift q.val) (signMean twoGapLaw q.val)) := by
  rw [prefix_output_risk twoGapLaw feedbackEstimator q _ feedbackOutput (fun _ => rfl)]
  rw [show feedbackEstimator.randomLaw = Measure.dirac () from rfl, integral_dirac]
  congr 1
  set θ := signMean twoGapLaw q.val
  set δ := drift q.val
  let pol := stopAt 2 feedbackLabel
  let W := seedWeight twoGapLaw feedbackEstimator q ()
  have hd : Measurable gapValue := measurable_subtype_coe
  have wFF : W ![some false, some false] = (11/16 - δ) * (11/16 - δ) := by
    rw [← oneBit_false]
    exact weight_fresh twoGapLaw pol gapValue q.val hd q.property.1 0 fb_root false 1 fb_tail
      (by norm_num) false _ rfl rfl
  have wFT : W ![some false, some true] = (11/16 - δ) * (5/16 + δ) := by
    rw [← oneBit_false, ← oneBit_true]
    exact weight_fresh twoGapLaw pol gapValue q.val hd q.property.1 0 fb_root false 1 fb_tail
      (by norm_num) true _ rfl rfl
  have wTF : W ![some true, some false] = 27/128 := by
    rw [← twoBit_tf q.val]
    exact weight_same twoGapLaw pol gapValue q.val hd q.property.1 0 fb_root true fb_head false
      _ rfl rfl
  have wTT : W ![some true, some true] = 13/128 + δ := by
    rw [← twoBit_tt]
    exact weight_same twoGapLaw pol gapValue q.val hd q.property.1 0 fb_root true fb_head true
      _ rfl rfl
  have tot := (seedWeight_total twoGapLaw feedbackEstimator q ()).2
  have nn := (seedWeight_total twoGapLaw feedbackEstimator q ()).1
  change ∑ w, W w = 1 at tot
  rw [sum_words, wFF, wFT, wTF, wTT] at tot
  have n1 := nn ![none, none]
  have n2 := nn ![none, some false]
  have n3 := nn ![none, some true]
  have n4 := nn ![some false, none]
  have n5 := nn ![some true, none]
  change 0 ≤ W _ at n1 n2 n3 n4 n5
  have z1 : W ![none, none] = 0 := by nlinarith
  have z2 : W ![none, some false] = 0 := by nlinarith
  have z3 : W ![none, some true] = 0 := by nlinarith
  have z4 : W ![some false, none] = 0 := by nlinarith
  have z5 : W ![some true, none] = 0 := by nlinarith
  change ∑ w, W w * (feedbackOutput w - θ)^2 = _
  rw [sum_words, wFF, wFT, wTF, wTT, z1, z2, z3, z4, z5]
  simp only [feedbackOutput, Matrix.cons_val_zero, Matrix.cons_val_one]
  unfold riskPoly yTT yTH yHT yHH
  ring

/-- Coordinates of a rare sign law in the feasible triangle. -/
theorem rare_triangle (q : SignLaw) (hq : RarePrior twoGapLaw (1/4) q) :
    0 ≤ drift q.val ∧ 2 * drift q.val ≤ signMean twoGapLaw q.val ∧
      signMean twoGapLaw q.val ≤ 4 * drift q.val ∧ signMean twoGapLaw q.val ≤ 1/4 := by
  have h1 := q.property.2 quarterGap
  have h2 := q.property.2 eighthGap
  have hr : signMean twoGapLaw q.val ≤ 1/4 := hq
  rw [signMean_twoGapLaw] at hr ⊢
  unfold drift
  refine ⟨by linarith, by linarith, by linarith, hr⟩

theorem feedback_upper : rareSquaredRisk feedbackEstimator ≤ ENNReal.ofReal upperValue := by
  unfold rareSquaredRisk
  refine iSup₂_le fun q hq => ?_
  rw [feedback_risk]
  obtain ⟨h0, h1, h2, h3⟩ := rare_triangle q hq
  exact ENNReal.ofReal_le_ofReal (riskPoly_le _ _ h0 h1 h2 h3)

end ThresholdHC.TwoFlipFeedback
