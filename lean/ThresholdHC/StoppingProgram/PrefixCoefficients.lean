import ThresholdHC.StoppingProgram.PascalFlow
import ThresholdHC.CapIdentification.TerminalMoments

/-! Ordered-prefix likelihood coefficients and their relation to the
binomially normalized count coefficients. -/

noncomputable section
open MeasureTheory
open scoped BigOperators

namespace ThresholdHC.StoppingProgram
open ThresholdHC.Tier6 (Gap SignLaw)
open ThresholdHC.CapIdentification

def prefixCoefficient (μ : Measure Gap) (q : SignLaw) (n k : ℕ) : ℝ :=
  ∫ d : Gap, q.val d*prefixLikelihood true n k d+(1-q.val d)*prefixLikelihood false n k d ∂μ

theorem prefixCoefficient_nonneg (μ : Measure Gap) (q : SignLaw) (n k : ℕ) :
    0 ≤ prefixCoefficient μ q n k := by
  apply integral_nonneg
  intro d
  exact add_nonneg (mul_nonneg (q.property.2 d).1 (prefixLikelihood_nonneg _ _ _ _))
    (mul_nonneg (sub_nonneg.mpr (q.property.2 d).2) (prefixLikelihood_nonneg _ _ _ _))

theorem prefixCoefficient_root (μ : Measure Gap) [IsProbabilityMeasure μ] (q : SignLaw) :
    prefixCoefficient μ q 0 0 = 1 := by
  simp [prefixCoefficient,prefixLikelihood]

theorem prefixLikelihood_add (s : Bool) (n k : ℕ) (hk : k ≤ n) (d : Gap) :
    prefixLikelihood s (n+1) k d+prefixLikelihood s (n+1) (k+1) d = prefixLikelihood s n k d := by
  have he : n+1-k = n-k+1 := by omega
  cases s <;> simp only [prefixLikelihood,Bool.false_eq_true,ite_false,ite_true,
    he,Nat.add_sub_add_right,pow_succ] <;> ring

theorem prefixCoefficient_add (μ : Measure Gap) [IsFiniteMeasure μ] (q : SignLaw)
    (n k : ℕ) (hk : k ≤ n) :
    prefixCoefficient μ q (n+1) k+prefixCoefficient μ q (n+1) (k+1) = prefixCoefficient μ q n k := by
  have hi (a b : ℕ) : Integrable (fun d : Gap =>
      q.val d*prefixLikelihood true a b d+(1-q.val d)*prefixLikelihood false a b d) μ := by
    have h0 := (integrable_prefixLikelihood μ false a b).sub (integrable_weighted_prefix μ q false a b)
    have h1 := (integrable_weighted_prefix μ q true a b).add h0
    convert h1 using 1
    funext d
    simp only [Pi.add_apply,Pi.sub_apply]
    ring
  unfold prefixCoefficient
  rw [← integral_add (hi _ _) (hi _ _)]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun d => by
    have h1 := prefixLikelihood_add true n k hk d
    have h0 := prefixLikelihood_add false n k hk d
    dsimp only
    nlinarith [congrArg (fun x : ℝ => q.val d*x) h1,
      congrArg (fun x : ℝ => (1-q.val d)*x) h0])

theorem countMean_raw {N : ℕ} (μ : Measure Gap) (q : SignLaw) (u : CountState N → ℝ) :
    countMean μ q u = ∑ s : CountState N, rawArray u s.1.val s.2.val*prefixCoefficient μ q s.1.val s.2.val := by
  unfold countMean
  apply Finset.sum_congr rfl
  intro s _
  rw [rawArray,arrayAt_state]
  unfold countCoefficient prefixCoefficient
  ring

end ThresholdHC.StoppingProgram
