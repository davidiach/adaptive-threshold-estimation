import ThresholdHC.WeightedSignSharp.SignFloor
import ThresholdHC.WeightedSignSharp.SharpOverlap

/-! Weighted sign entropy with the paper's coefficient 214
(`paper/v6/appendix-lower-foundations.tex`, Lemma `lem:weighted-sign`).

Gibbs' inequality against the normalized masses `e^{-65 cⱼ}/((25/3) e⁸)`
gives `1 + Ent(π) ≤ 65 c̄ + 9 + log(25/3)`, and the floor `cⱼ > 3/40` with
`log(25/3) ≤ 87/40` turns this into `214 c̄`. The weights may vanish and need
not sum to one. Only finite negative-sign work is assumed. -/

noncomputable section
open MeasureTheory Real
open scoped ENNReal
namespace ThresholdHC.WeightedSignSharp
open ThresholdHC.CriticalEntropy

/-- Stopped change-of-measure floor `d² E₋τ > 3/40`. -/
theorem sign_work_floor : SignWorkFloorStatement := sign_work_floor_proof

/-- Pathwise weighted overlap `∑ⱼ 1_{Eⱼ}/(1+cⱼ) ≤ 25/3` of the stopping windows. -/
theorem window_overlap : WindowOverlapStatement := window_overlap_proof

theorem log_twenty_five_thirds_le : log (25/3 : ℝ) ≤ 87/40 := by
  rw [Real.log_le_iff_le_exp (by norm_num)]
  have he : exp (87/40 : ℝ) = exp 1 * exp 1 * exp (7/40) := by
    rw [← exp_add, ← exp_add]
    norm_num
  have h1 := Real.exp_one_gt_d9
  have h2 := add_one_le_exp (7/40 : ℝ)
  have h3 : (0 : ℝ) < exp 1 := exp_pos 1
  rw [he]
  have h4 := mul_le_mul h1.le h1.le (by norm_num) h3.le
  have h5 := mul_le_mul h4 h2 (by norm_num) (by positivity)
  nlinarith

/-- Weighted sign entropy with the paper's coefficient 214. -/
theorem weighted_sign_entropy_214 : WeightedSignEntropy214Statement := by
  intro R _ ν _ A K d hgap hfinite herror a ha
  let cost := fun i : Fin K => (d i : ℝ)^2*
    (expectedSignTestWork ν (signParameter (d i) false) A).toReal
  let p := fun i : Fin K => exp (-65*cost i)/(25/3*exp 8)
  have hp (i : Fin K) : 0 < p i := by dsimp [p]; positivity
  have hsum : (∑ i, p i) ≤ 1 := by
    simp only [p,← Finset.sum_div]
    apply (div_le_one (by positivity : (0:ℝ) < 25/3*exp 8)).mpr
    exact signTest_exponential_sum_sharp ν A d hgap hfinite herror
  have hc (i : Fin K) : (3/40:ℝ) < cost i :=
    sign_work_floor ν A (d i) (hfinite i)
      (by simpa using herror i false) (by simpa using herror i true)
  have hlog := log_twenty_five_thirds_le
  have hpoint (i : Fin K) : 1-log (p i) ≤ 214*cost i := by
    dsimp [p]
    rw [log_div (exp_pos _).ne' (by positivity),log_exp,
      log_mul (by norm_num : (25/3:ℝ) ≠ 0) (exp_pos _).ne',log_exp]
    linarith [hc i]
  calc
    _ ≤ ∑ i, a i*(1-log (p i)) :=
      ThresholdHC.EntropyTailQuantile.costEntropy_le_reference ha hp hsum
    _ ≤ ∑ i, a i*(214*cost i) :=
      Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hpoint i) (ha i))
    _ = 214*∑ i, a i*cost i := by rw [Finset.mul_sum]; congr 1; funext i; ring

end ThresholdHC.WeightedSignSharp
