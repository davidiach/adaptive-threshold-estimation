import ThresholdHC.ShiftedPower.PopulationBounds

noncomputable section
open Real
namespace ThresholdHC.ShiftedPower

def massBound (α a : ℝ) (k : ℕ) : ℝ := (resolution k/a)^α
def decay (α : ℝ) : ℝ := ((Real.sqrt 2)⁻¹)^α
def summationRatio (α : ℝ) : ℝ := Real.sqrt 2*decay α
def workConstant (α : ℝ) : ℝ := 17/((1-workPower α/2)*(1-α/workPower α))

theorem mass_positive {α a : ℝ} (ha : 0 < a) (k : ℕ) : 0 < massBound α a k :=
  Real.rpow_pos_of_pos (div_pos (resolution_pos k) ha) _

theorem decay_bounds {α : ℝ} (hα : 0 < α) (hu : α < 2) :
    1/2 < decay α ∧ decay α < 1 := by
  have hs : 1 < Real.sqrt (2:ℝ) := by exact (Real.lt_sqrt (by norm_num)).mpr (by norm_num)
  have hx : 0 < (Real.sqrt (2:ℝ))⁻¹ := inv_pos.mpr (by positivity)
  have hx' : (Real.sqrt (2:ℝ))⁻¹ < 1 := inv_lt_one_of_one_lt₀ hs
  constructor
  · have he : ((Real.sqrt (2:ℝ))⁻¹)^(2:ℝ) = 1/2 := by rw [Real.rpow_two,inv_pow,Real.sq_sqrt (by norm_num)]; norm_num
    rw [← he]
    exact Real.rpow_lt_rpow_of_exponent_gt hx hx' hu
  · exact Real.rpow_lt_one hx.le hx' hα

theorem resolution_succ (k : ℕ) : resolution (k+1) = resolution k*(Real.sqrt 2)⁻¹ := by
  simp only [resolution,pow_succ,Real.sqrt_mul (by positivity : 0 ≤ (2:ℝ)^k),mul_inv]

theorem mass_succ {α a : ℝ} (ha : 0 < a) (k : ℕ) :
    massBound α a (k+1) = massBound α a k*decay α := by
  unfold massBound decay
  rw [resolution_succ,show resolution k*(Real.sqrt 2)⁻¹/a = (resolution k/a)*(Real.sqrt 2)⁻¹ by ring,
    Real.mul_rpow (div_nonneg (resolution_pos k).le ha.le) (by positivity)]

theorem mass_add {α a : ℝ} (ha : 0 < a) (k j : ℕ) :
    massBound α a (k+j) = massBound α a k*(decay α)^j := by
  induction j with
  | zero => simp
  | succ j hj => rw [Nat.add_succ,mass_succ ha,hj,pow_succ,mul_assoc]

theorem error_le_mass {α a : ℝ} (ha : 0 < a) (_hα : 0 < α) (hu : α < 2) (k : ℕ) :
    errorBound α a k ≤ 2*massBound α a k := by
  unfold errorBound massBound
  apply (div_le_iff₀ (by linarith : 0 < 1-α/4)).mpr
  have hx : 0 ≤ (resolution k/a)^α := Real.rpow_nonneg (div_nonneg (resolution_pos k).le ha.le) _
  nlinarith [mul_nonneg (show 0 ≤ 2-α by linarith) hx]

theorem workConstant_pos {α : ℝ} (hα : 0 < α) (hu : α < 2) : 0 < workConstant α := by
  have hp : 0 < workPower α := by unfold workPower; linarith
  have hratio : α/workPower α < 1 := (div_lt_one hp).mpr (by unfold workPower; linarith)
  unfold workConstant
  apply div_pos (by norm_num)
  apply mul_pos (by unfold workPower; linarith)
  linarith

theorem work_formula (α a : ℝ) (k : ℕ) :
    workBound α a k = workConstant α*(2:ℝ)^k*massBound α a k := by
  unfold workBound workConstant massBound
  simp only [div_eq_mul_inv,mul_inv]
  ring

theorem work_mono {α a : ℝ} (hα : 0 < α) (hu : α < 2) (ha : 0 < a) :
    Monotone (workBound α a) := by
  apply monotone_nat_of_le_succ
  intro k
  rw [work_formula,work_formula,pow_succ,mass_succ ha]
  have hd := (decay_bounds hα hu).1
  have hn := mass_positive (α := α) ha k
  have hW := workConstant_pos hα hu
  nlinarith [mul_nonneg (mul_nonneg hW.le (by positivity : 0 ≤ (2:ℝ)^k)) hn.le,
    mul_le_mul_of_nonneg_left (show 1 ≤ 2*decay α by linarith)
      (mul_nonneg (mul_nonneg hW.le (by positivity : 0 ≤ (2:ℝ)^k)) hn.le)]

theorem ratio_eq_one : summationRatio 1 = 1 := by
  unfold summationRatio decay
  rw [Real.rpow_one,mul_inv_cancel₀ (by positivity : Real.sqrt (2:ℝ) ≠ 0)]

theorem ratio_lt_one {α : ℝ} (hα : 1 < α) :
    summationRatio α < 1 := by
  have hs : 1 < Real.sqrt (2:ℝ) := by exact (Real.lt_sqrt (by norm_num)).mpr (by norm_num)
  have hx : 0 < (Real.sqrt (2:ℝ))⁻¹ := inv_pos.mpr (by positivity)
  have hx' : (Real.sqrt (2:ℝ))⁻¹ < 1 := inv_lt_one_of_one_lt₀ hs
  have h := Real.rpow_lt_rpow_of_exponent_gt hx hx' hα
  rw [Real.rpow_one] at h
  have hh := mul_lt_mul_of_pos_left h (show 0 < Real.sqrt (2:ℝ) by positivity)
  simpa only [summationRatio,decay,mul_inv_cancel₀ (show Real.sqrt (2:ℝ) ≠ 0 by positivity)] using hh

end ThresholdHC.ShiftedPower
