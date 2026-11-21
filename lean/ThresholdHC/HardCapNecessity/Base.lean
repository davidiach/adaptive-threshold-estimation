import ThresholdHC.HardCapNecessity.Fresh
import ThresholdHC.UpperMixture.Mixture

/-! The base family of the counterexample. Every stage has the same seed law,
a delay coin showing `true` with probability `1/8`; whether stages share the
coin depends on the controller. Stages `0` and `1` return the midpoint `1/8`
at zero work. Stage `i+2` (allowance `b = 2^(i+2)`) returns the clipped mean
of `b/4 = 2^i` fresh flips; on the delay bit it buys `4b` further flips after
the `b/4` it reads, and discards them. Its expected work is `3b/4` and its
squared risk is at most `min(1/16, 1/b) ≤ K(b)^2`. -/

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace ThresholdHC.HardCapNecessity
open ThresholdHC.Tier3 ThresholdHC.Tier6 ThresholdHC.ObservableSimulation ThresholdHC.HardBudget
open ThresholdHC.PaperStatements ThresholdHC.UpperMixture ThresholdHC.RareAboveTwo

/-- The zero-work midpoint, behind the delay coin. -/
def midBase : AdaptiveEstimator (Bool × Unit) :=
  mixEstimator (1/8) (constantEstimator (1/8)) (constantEstimator (1/8))

/-- `2^i` fresh flips; on the delay bit `16 * 2^i` further discarded flips. -/
def delayBase (i : ℕ) : AdaptiveEstimator (Bool × Unit) :=
  mixEstimator (1/8) (freshClip (2^i-1)) (delayedClip (2^i-1) (17*2^i-1))

/-- The base family indexed by the stage. -/
def capBase : ℕ → AdaptiveEstimator (Bool × Unit)
  | 0 => midBase
  | 1 => midBase
  | i+2 => delayBase i

/-- The common seed law of every stage. -/
def delaySeedLaw : Measure (Bool × Unit) := (coinLaw (1/8)).prod (Measure.dirac ())

theorem capBase_seed (j : ℕ) : (capBase j).randomLaw = delaySeedLaw := by
  match j with
  | 0 => rfl
  | 1 => rfl
  | _+2 => rfl

theorem capBase_seed_zero (j : ℕ) : (capBase j).randomLaw = (capBase 0).randomLaw :=
  (capBase_seed j).trans (capBase_seed 0).symm

theorem clip_eighth : clip (1/8) = 1/8 := clip_eq (by norm_num) (by norm_num)

theorem two_pow_pred (i : ℕ) : (((2^i-1 : ℕ) : ℝ)+1) = 2^i := by
  rw [Nat.cast_sub Nat.one_le_two_pow]; push_cast; ring

theorem seventeen_pred (i : ℕ) : (((17*2^i-1 : ℕ) : ℝ)+1) = 17*2^i := by
  rw [Nat.cast_sub (by have := @Nat.one_le_two_pow i; omega)]; push_cast; ring

/-- A mixture of two runs with the same seed law has risk at most a common bound. -/
theorem mix_risk_le {R : Type} [MeasurableSpace R] (p : ℝ) (A₀ A₁ : AdaptiveEstimator R)
    (h : A₁.randomLaw = A₀.randomLaw) (μ : Measure Gap) [IsProbabilityMeasure μ] (q : SignLaw)
    (a : ℝ) (V : ℝ≥0∞)
    (h₀ : squaredRisk (experimentLaw μ A₀ q) (populationOutput A₀) a ≤ V)
    (h₁ : squaredRisk (experimentLaw μ A₁ q) (populationOutput A₁) a ≤ V) :
    squaredRisk (experimentLaw μ (mixEstimator p A₀ A₁) q) (populationOutput (mixEstimator p A₀ A₁)) a ≤ V := by
  rw [mix_squaredRisk p A₀ A₁ h]
  calc _ ≤ ENNReal.ofReal (clip p) * V + ENNReal.ofReal (1 - clip p) * V :=
        add_le_add (mul_le_mul_of_nonneg_left h₁ zero_le) (mul_le_mul_of_nonneg_left h₀ zero_le)
    _ = (ENNReal.ofReal (clip p) + ENNReal.ofReal (1 - clip p)) * V := (add_mul _ _ _).symm
    _ = V := by
        rw [← ENNReal.ofReal_add (clip_nonneg p) (by linarith [clip_le_one p])]
        simp

theorem constant_range (t : ℝ) (ht : 0 ≤ t ∧ t ≤ 1/4) (z : Unit × ProcessTape) :
    0 ≤ (constantEstimator t).output z ∧ (constantEstimator t).output z ≤ 1/4 := ht

theorem mid_work (q : SignLaw) : expectedWork (Measure.dirac halfGap) midBase q = 0 := by
  unfold midBase
  rw [mix_expectedWork _ _ _ rfl, constant_work]
  simp

theorem mid_risk (q : SignLaw) (hθ : 0 ≤ q.val halfGap ∧ q.val halfGap ≤ 1/4) :
    squaredRisk (experimentLaw (Measure.dirac halfGap) midBase q) (populationOutput midBase)
      (q.val halfGap) ≤ ENNReal.ofReal (1/16) := by
  have hc := risk_le_of_range (Measure.dirac halfGap) (constantEstimator (1/8)) q hθ
    (constant_range (1/8) ⟨by norm_num, by norm_num⟩)
  exact mix_risk_le _ _ _ rfl _ q _ _ hc hc

theorem delay_work (i : ℕ) (q : SignLaw) :
    expectedWork (Measure.dirac halfGap) (delayBase i) q ≤ ENNReal.ofReal (3 * 2^i) := by
  unfold delayBase
  rw [mix_expectedWork (1/8) (freshClip (2^i-1)) (delayedClip (2^i-1) (17*2^i-1)) rfl, clip_eighth]
  have h1 := delayed_work (Measure.dirac halfGap) (2^i-1) (17*2^i-1) q
  have h0 := clip_work (Measure.dirac halfGap) (2^i-1) q
  rw [seventeen_pred] at h1
  rw [two_pow_pred] at h0
  calc _ ≤ ENNReal.ofReal (1/8) * ENNReal.ofReal (17 * 2^i) + ENNReal.ofReal (1 - 1/8) *
        ENNReal.ofReal (2^i) := by gcongr
    _ = ENNReal.ofReal (3 * 2^i) := by
        rw [← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_mul (by norm_num),
          ← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1; ring

theorem delay_risk (i : ℕ) (q : SignLaw) (hθ : q.val halfGap ≤ 1/4) :
    squaredRisk (experimentLaw (Measure.dirac halfGap) (delayBase i) q) (populationOutput (delayBase i))
      (q.val halfGap) ≤ ENNReal.ofReal (min (1/16) ((1/4) / 2^i)) := by
  have hc := clip_risk_half (2^i-1) q hθ
  rw [two_pow_pred] at hc
  have hd : squaredRisk (experimentLaw (Measure.dirac halfGap) (delayedClip (2^i-1) (17*2^i-1)) q)
      (populationOutput (delayedClip (2^i-1) (17*2^i-1))) (q.val halfGap) ≤
        ENNReal.ofReal (min (1/16) ((1/4) / 2^i)) := by
    rw [delayed_risk _ (by have := @Nat.one_le_two_pow i; omega)]
    exact hc
  exact mix_risk_le (1/8) (freshClip (2^i-1)) (delayedClip (2^i-1) (17*2^i-1)) rfl _ q _ _ hc hd

/-- The base family meets the stage premise uniformly over the rare sign laws. -/
theorem capBase_premise : RarePremise capBase := by
  intro q hq j
  have hθ := signMean_half q
  unfold RarePrior at hq
  rw [hθ] at hq ⊢
  have h0 := (q.property.2 halfGap).1
  match j with
  | 0 =>
    refine ⟨by rw [show capBase 0 = midBase from rfl, mid_work]; exact bot_le, ?_⟩
    refine (mid_risk q ⟨h0, hq⟩).trans (ENNReal.ofReal_le_ofReal ?_)
    rw [rate_small (by norm_num [stageAllowance]) (by norm_num [stageAllowance])]
    norm_num
  | 1 =>
    refine ⟨by rw [show capBase 1 = midBase from rfl, mid_work]; exact bot_le, ?_⟩
    refine (mid_risk q ⟨h0, hq⟩).trans (ENNReal.ofReal_le_ofReal ?_)
    rw [rate_small (by norm_num [stageAllowance]) (by norm_num [stageAllowance])]
    norm_num
  | i+2 =>
    have hb : ((stageAllowance (i+2) : ℕ) : ℝ) = 4 * 2^i := by
      simp only [stageAllowance]; push_cast; ring
    refine ⟨?_, ?_⟩
    · refine (delay_work i q).trans ?_
      rw [← ENNReal.ofReal_natCast, hb]
      exact ENNReal.ofReal_le_ofReal (by nlinarith [pow_pos (two_pos : (0:ℝ) < 2) i])
    · refine (delay_risk i q hq).trans (ENNReal.ofReal_le_ofReal ?_)
      rw [hb, one_pow, one_mul]
      have h := min_le_rate_sq (b := 4 * 2^i) (by positivity)
      have he : (1/4 : ℝ) / 2^i = 1 / (4 * 2^i) := by field_simp
      rw [he]
      exact h

end ThresholdHC.HardCapNecessity
