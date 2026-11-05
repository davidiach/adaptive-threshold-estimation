
import ThresholdHC.AnytimeLower.TailLimits
import ThresholdHC.AnytimeLower.ObservedTesting
import ThresholdHC.AnytimeLower.TestingSchedule

noncomputable section
open MeasureTheory InformationTheory Real Filter
open scoped ENNReal Topology
namespace ThresholdHC.AnytimeLower
open ThresholdHC.Tier3 ThresholdHC.Tier6 ThresholdHC.RareAboveTwo ThresholdHC.StoppingProgram
open ThresholdHC.Genie

def centralShift (k : ℕ) : ℝ := geometricScale (1/8) k

theorem centralShift_bounds (k : ℕ) : 0 < centralShift k ∧ centralShift k ≤ 1/8 := by
  refine ⟨geometricScale_pos (by norm_num) k,?_⟩
  have h := geometricScale_antitone (by norm_num : (0:ℝ) ≤ 1/8) (Nat.zero_le k)
  simpa [geometricScale,centralShift] using h

theorem centralShift_separated (i k : ℕ) (hik : i < k) : 4*centralShift k ≤ centralShift i := by
  have h := geometricScale_antitone (by norm_num : (0:ℝ) ≤ 1/8) (show i+1 ≤ k by omega)
  have he : centralShift (i+1) = centralShift i/4 := by
    simp only [centralShift,geometricScale,pow_succ]
    ring
  change centralShift k ≤ centralShift (i+1) at h
  rw [he] at h
  linarith

def certificateAlternative (Q : FourPriors) (k : ℕ) : SignLaw :=
  centralPrior Q (1/2-centralShift k)
    ⟨by linarith [(centralShift_bounds k).2],by linarith [(centralShift_bounds k).1]⟩

def certificateScale (J : ℝ) (k : ℕ) : ℝ :=
  sqrt ((64/3)*J)*centralShift k

theorem certificateScale_pos {J : ℝ} (hJ : 0 < J) (k : ℕ) :
    0 < certificateScale J k :=
  mul_pos (sqrt_pos.mpr (by positivity)) (centralShift_bounds k).1

theorem certificateScale_antitone {J : ℝ} : Antitone (certificateScale J) := by
  intro i k hik
  exact mul_le_mul_of_nonneg_left
    (geometricScale_antitone (by norm_num : (0:ℝ) ≤ 1/8) hik) (sqrt_nonneg _)

/-- A finite-information four-prior certificate supplies an explicit
unbounded testing schedule for one common admissible central segment. -/
theorem certificate_scheduled_frequently {R : Type} [MeasurableSpace R]
    (μ : Measure Gap) [IsProbabilityMeasure μ] (A : AdaptiveEstimator R)
    (H : ∀ n, R × Prefix n → ℝ) (hH : ∀ n, Measurable (H n))
    {ρ δ : ℝ} (hd : 0 ≤ δ ∧ δ ≤ 1/2) (t : ℕ → ℝ)
    (hacc : OnlineAccuracy μ A H ρ δ t)
    (Q : FourPriors) (hQ : Admissible μ ρ Q)
    {J : ℝ} (hJ : 0 < J) (hI : infiniteInformationRatio μ Q ≤ ENNReal.ofReal J)
    (hgap : 0 < signMean μ Q.high.val-signMean μ Q.low.val) :
    ∃ᶠ k in atTop, centralShift k*(signMean μ Q.high.val-signMean μ Q.low.val)/18 ≤
      t (testingBudget δ (certificateScale J) k) := by
  let q := centralPrior Q (1/2) (by norm_num)
  let a (k : ℕ) := centralShift k*(signMean μ Q.high.val-signMean μ Q.low.val)/3
  let N := testingBudget δ (certificateScale J)
  have ha (k : ℕ) : 0 < a k := by
    dsimp [a]
    exact div_pos (mul_pos (centralShift_bounds k).1 hgap) (by norm_num)
  have hm (k : ℕ) : signMean μ (certificateAlternative Q k).val = signMean μ q.val+a k := by
    have he := centralPrior_mean_difference μ Q (1/2-centralShift k) (1/2)
      (by constructor <;> linarith [(centralShift_bounds k).1,(centralShift_bounds k).2]) (by norm_num)
    change signMean μ (certificateAlternative Q k).val-signMean μ q.val = _ at he
    dsimp [a]
    linarith
  have hsep (i k : ℕ) (hik : i < k) : 3*a k ≤ a i := by
    have he := mul_le_mul_of_nonneg_right (centralShift_separated i k hik) hgap.le
    have hp := mul_pos (centralShift_bounds k).1 hgap
    dsimp [a]
    nlinarith
  have hk (k : ℕ) : klDiv (observablePrefixLaw μ A (certificateAlternative Q k) (N k))
      (observablePrefixLaw μ A q (N k)) ≤ ENNReal.ofReal ((N k:ℝ)*(certificateScale J k)^2) := by
    have he := quartet_prefix_kl μ A Q J hJ.le hI (1/2-centralShift k) (1/2)
      (by constructor <;> linarith [(centralShift_bounds k).1,(centralShift_bounds k).2]) (by norm_num) (N k)
    have heq : (64/3)*J*((1/2-centralShift k)-1/2)^2*(N k:ℝ) =
        (N k:ℝ)*(certificateScale J k)^2 := by
      dsimp [certificateScale]
      rw [mul_pow,sq_sqrt (by positivity : 0 ≤ (64/3:ℝ)*J)]
      ring
    rw [heq] at he
    exact he
  have hf := observed_separated_frequently μ A H hH hd t hacc q
    (centralPrior_rare μ Q hQ _ _) (certificateAlternative Q)
    (fun k => centralPrior_rare μ Q hQ _ _) a ha hm hsep N
    (testingBudget_mono (by linarith) _ (certificateScale_pos hJ) certificateScale_antitone)
    (fun k => (N k:ℝ)*(certificateScale J k)^2) (fun k => by positivity) hk
    (testingBudget_not_summable (by linarith) _ (certificateScale_pos hJ))
  apply hf.mono
  intro k hk
  have he : a k/6 = centralShift k*(signMean μ Q.high.val-signMean μ Q.low.val)/18 := by
    dsimp [a]
    ring
  rw [he] at hk
  exact hk

end ThresholdHC.AnytimeLower
