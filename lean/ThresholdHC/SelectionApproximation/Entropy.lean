import ThresholdHC.SelectionApproximation.Model
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.MeanValue

noncomputable section
open scoped BigOperators
namespace ThresholdHC.SelectionApproximation
open ThresholdHC.EntropyTailQuantile Real

theorem close_abs_sub {c x y : ℝ} (hc : 1 ≤ c) (hx : 0 ≤ x)
    (h : Close c x y) : |y-x| ≤ (c-1)*x := by
  apply abs_le.mpr
  constructor
  · rcases le_total x y with hxy | hyx
    · nlinarith [mul_nonneg (sub_nonneg.mpr hc) hx]
    · have hm := mul_le_mul_of_nonneg_left hyx (sub_nonneg.mpr hc)
      nlinarith [h.1]
  · nlinarith [h.2]

/-- Zero total cost is preserved exactly and has zero entropy on both sides. -/
theorem entropy_zero_of_close {ι κ : Type*} [Fintype ι] [Fintype κ]
    {a : ι → ℝ} {b : κ → ℝ} {c : ℝ}
    (ha : ∀ i, 0 ≤ a i) (hb : ∀ i, 0 ≤ b i)
    (hzero : costTotal a = 0) (hclose : Close c (costTotal a) (costTotal b)) :
    costEntropy a = 0 ∧ costEntropy b = 0 := by
  have hbzero : costTotal b = 0 := le_antisymm
    (by simpa [hzero] using hclose.2) (costTotal_nonneg hb)
  have ha0 : a = fun _ => 0 := eq_zero_of_costTotal_eq_zero ha hzero
  have hb0 : b = fun _ => 0 := eq_zero_of_costTotal_eq_zero hb hbzero
  simp [ha0, hb0]

/-- The logarithmic surrogate is related to the original project entropy exactly. -/
theorem costEntropy_eq_potential_sub {ι : Type*} [Fintype ι]
    (a : ι → ℝ) {r : ℝ} (hr : 0 < r) :
    costEntropy a = potential r (costTotal a) - baseSummary r a := by
  have hi (i : ι) : a i*(1+log (a i/r)) =
      a i + a i*log (a i) - a i*log r := by
    by_cases hz : a i = 0
    · simp [hz]
    · rw [log_div hz hr.ne']
      ring
  simp only [baseSummary, hi, Finset.sum_sub_distrib, Finset.sum_add_distrib,
    ← Finset.sum_mul, costEntropy, potential, negMulLog, neg_mul, Finset.sum_neg_distrib]
  unfold costTotal
  ring

theorem potential_hasDerivAt {r x : ℝ} (hx : 0 < x) :
    HasDerivAt (potential r) (3+log x-log r) x := by
  have h := (hasDerivAt_id x).mul (((hasDerivAt_log hx.ne').const_add 2).sub_const (log r))
  convert h using 1
  · rfl
  · simp only [id_eq, one_mul]
    rw [mul_inv_cancel₀ hx.ne']
    ring

/-- The derivative bound is proved, not supplied as a Lipschitz premise. -/
theorem potential_lipschitz {r U L x y : ℝ} (hr : 0 < r)
    (hx : x ∈ Set.Icc r U) (hy : y ∈ Set.Icc r U)
    (hL : 3+log (U/r) ≤ L) : |potential r y-potential r x| ≤ L*|y-x| := by
  have hU : 0 < U := hr.trans_le (hx.1.trans hx.2)
  have hbound (z : ℝ) (hz : z ∈ Set.Icc r U) : ‖3+log z-log r‖ ≤ L := by
    have hzpos : 0 < z := hr.trans_le hz.1
    have hlo := log_le_log hr hz.1
    have hhi := log_le_log hzpos hz.2
    rw [log_div hU.ne' hr.ne'] at hL
    rw [Real.norm_eq_abs, abs_of_nonneg (by linarith)]
    linarith
  have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun z (hz : z ∈ Set.Icc r U) =>
      (potential_hasDerivAt (r := r) (hr.trans_le hz.1)).hasDerivWithinAt)
    hbound (convex_Icc r U) hx hy
  simpa only [Real.norm_eq_abs] using h

/-- Rounding each positive logarithm gives certified additive summary bounds.
Zero-cost coordinates need no logarithm approximation. -/
theorem surrogate_bounds {ι : Type*} [Fintype ι] {a u : ι → ℝ}
    {r U δ L : ℝ} (ha : ∀ i, 0 ≤ a i) (hr : 0 < r)
    (hlower : ∀ i, a i ≠ 0 → r ≤ a i) (hU : costTotal a ≤ U)
    (_hδ : 0 ≤ δ) (hL : 1+log (U/r)+δ ≤ L)
    (hu : ∀ i, a i ≠ 0 → log (a i/r) ≤ u i ∧ u i ≤ log (a i/r)+δ) :
    let H := ∑ i, a i*(1+u i)
    baseSummary r a ≤ H ∧ H ≤ baseSummary r a+δ*costTotal a ∧
      0 ≤ H ∧ H ≤ L*costTotal a := by
  dsimp
  have hlo (i : ι) : a i*(1+log (a i/r)) ≤ a i*(1+u i) := by
    by_cases hz : a i = 0
    · simp [hz]
    · exact mul_le_mul_of_nonneg_left (by linarith [(hu i hz).1]) (ha i)
  have hhi (i : ι) : a i*(1+u i) ≤ a i*(1+log (a i/r))+δ*a i := by
    by_cases hz : a i = 0
    · simp [hz]
    · have hm := mul_le_mul_of_nonneg_left (hu i hz).2 (ha i)
      nlinarith
  have hnonneg (i : ι) : 0 ≤ a i*(1+u i) := by
    by_cases hz : a i = 0
    · simp [hz]
    · have hlog : 0 ≤ log (a i/r) := log_nonneg ((le_div_iff₀ hr).2 (by simpa using hlower i hz))
      exact mul_nonneg (ha i) (by linarith [(hu i hz).1])
  have hscale (i : ι) : a i*(1+u i) ≤ L*a i := by
    by_cases hz : a i = 0
    · simp [hz]
    · have hai : 0 < a i := lt_of_le_of_ne (ha i) (Ne.symm hz)
      have harg := div_le_div_of_nonneg_right ((le_costTotal ha i).trans hU) hr.le
      have hlog := log_le_log (div_pos hai hr) harg
      have hcoef : 1+u i ≤ L := by linarith [(hu i hz).2]
      simpa [mul_comm] using mul_le_mul_of_nonneg_left hcoef (ha i)
  refine ⟨Finset.sum_le_sum (fun i _ => hlo i), ?_,
    Finset.sum_nonneg (fun i _ => hnonneg i), ?_⟩
  · simpa only [Finset.sum_add_distrib, ← Finset.mul_sum, baseSummary, costTotal]
      using Finset.sum_le_sum (fun i _ => hhi i)
  · simpa only [← Finset.mul_sum, costTotal]
      using Finset.sum_le_sum (fun i _ => hscale i)

theorem entropy_perturbation : EntropyPerturbationStatement := by
  intro ι κ _ _ a b r U L δ η Ha Hb ha hb hr hL hδ hη hra hUa hrb hUb
    hderiv hHaLower _hHaUpper _hHbLower hHbUpper hHa0 hHaL hA hH
  have hAabs : |costTotal b-costTotal a| ≤ η*costTotal a := by
    simpa using close_abs_sub (by linarith : 1 ≤ 1+η) (costTotal_nonneg ha) hA
  have hHabs : |Hb-Ha| ≤ η*Ha := by
    simpa using close_abs_sub (by linarith : 1 ≤ 1+η) hHa0 hH
  have hpot := potential_lipschitz hr ⟨hra,hUa⟩ ⟨hrb,hUb⟩ hderiv
  have hpot' := mul_le_mul_of_nonneg_left hAabs hL
  have hp : potential r (costTotal b)-potential r (costTotal a) ≤ L*(η*costTotal a) :=
    (le_abs_self _).trans (hpot.trans hpot')
  have hh : Ha-Hb ≤ η*Ha := by
    have := (abs_le.mp hHabs).1
    linarith
  have hh' := mul_le_mul_of_nonneg_left hHaL hη
  have hb' := mul_le_mul_of_nonneg_left hA.2 hδ
  rw [costEntropy_eq_potential_sub a hr, costEntropy_eq_potential_sub b hr]
  nlinarith only [hp, hh, hh', hb', hHaLower, hHbUpper]

/-- The error allocation in the paper gives the relative entropy comparison. -/
theorem entropy_relative {ι κ : Type*} [Fintype ι] [Fintype κ]
    (a : ι → ℝ) (b : κ → ℝ) {r U L ε η Ha Hb : ℝ}
    (ha : ∀ i, 0 ≤ a i) (hb : ∀ i, 0 ≤ b i)
    (hr : 0 < r) (hL : 0 ≤ L) (hε : 0 ≤ ε) (hη : 0 ≤ η) (hη1 : η ≤ 1)
    (hsmall : L*η ≤ ε/8)
    (hra : r ≤ costTotal a) (hUa : costTotal a ≤ U)
    (hrb : r ≤ costTotal b) (hUb : costTotal b ≤ U)
    (hderiv : 3+log (U/r) ≤ L)
    (hHaLower : baseSummary r a ≤ Ha)
    (hHaUpper : Ha ≤ baseSummary r a+(ε/8)*costTotal a)
    (hHbLower : baseSummary r b ≤ Hb)
    (hHbUpper : Hb ≤ baseSummary r b+(ε/8)*costTotal b)
    (hHa0 : 0 ≤ Ha) (hHaL : Ha ≤ L*costTotal a)
    (hA : Close (1+η) (costTotal a) (costTotal b)) (hH : Close (1+η) Ha Hb) :
    costEntropy b ≤ (1+ε/2)*costEntropy a := by
  have h := entropy_perturbation a b r U L (ε/8) η Ha Hb ha hb hr hL
    (by positivity) hη hra hUa hrb hUb hderiv hHaLower hHaUpper hHbLower hHbUpper
    hHa0 hHaL hA hH
  have hcoef : 2*L*η+(ε/8)*(1+η) ≤ ε/2 := by
    nlinarith [mul_nonneg hε (sub_nonneg.mpr hη1)]
  have ht := mul_le_mul_of_nonneg_right hcoef (costTotal_nonneg ha)
  have he := mul_le_mul_of_nonneg_left (costTotal_le_costEntropy ha)
    (show 0 ≤ ε/2 by positivity)
  nlinarith only [h,ht,he]

end ThresholdHC.SelectionApproximation
