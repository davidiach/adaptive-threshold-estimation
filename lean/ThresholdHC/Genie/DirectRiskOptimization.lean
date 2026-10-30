import Mathlib

/-! Exact optimization of the contracted-affinity lower certificate. -/

noncomputable section
namespace ThresholdHC.Genie

def directRiskProfile (t x s : ℝ) : ℝ := s*t/2*max (1-s^2*x/4) 0

def directRiskScale (x : ℝ) : ℝ := if x ≤ 4/3 then 1 else Real.sqrt (4/(3*x))

def directRiskSquared (t x : ℝ) : ℝ :=
  if x ≤ 4/3 then t^2/4*(1-x/4)^2 else 4*t^2/(27*x)

theorem direct_small_scale (x s : ℝ) (hx : 0 ≤ x) (hx' : x ≤ 4/3)
    (hs : 0 ≤ s ∧ s ≤ 1) : s*max (1-s^2*x/4) 0 ≤ 1-x/4 := by
  have hs2 : s^2 ≤ 1 := by nlinarith
  have hxs : s^2*x ≤ x := mul_le_of_le_one_left hx hs2
  rw [max_eq_left (by linarith : 0 ≤ 1-s^2*x/4)]
  have hsums : 1+s+s^2 ≤ 3 := by linarith
  have hprod : x*(1+s+s^2) ≤ 4 := by nlinarith [mul_le_mul_of_nonneg_left hsums hx]
  have hnon := mul_nonneg (sub_nonneg.mpr hs.2) (show 0 ≤ 1-x/4*(1+s+s^2) by nlinarith)
  nlinarith

theorem direct_large_scale_data (x : ℝ) (hx : 4/3 ≤ x) :
    let a := Real.sqrt (4/(3*x))
    (0 < a ∧ a ≤ 1) ∧ x*a^2 = 4/3 := by
  have hx0 : 0 < x := by linarith
  have hpos : 0 < 4/(3*x) := by positivity
  have hsq := Real.sq_sqrt hpos.le
  have hroot := Real.sqrt_pos.mpr hpos
  dsimp only
  refine ⟨⟨hroot,?_⟩,?_⟩
  · have hle : 4/(3*x) ≤ 1 := (div_le_one (by positivity)).mpr (by linarith)
    nlinarith
  · rw [hsq]
    field_simp

theorem direct_large_scale (x s : ℝ) (hx : 4/3 ≤ x) (hs : 0 ≤ s) :
    s*max (1-s^2*x/4) 0 ≤ 2*Real.sqrt (4/(3*x))/3 := by
  let a := Real.sqrt (4/(3*x))
  obtain ⟨ha,hxa⟩ := direct_large_scale_data x hx
  change (0 < a ∧ a ≤ 1) at ha
  change x*a^2 = 4/3 at hxa
  change _ ≤ 2*a/3
  by_cases h : 0 ≤ 1-s^2*x/4
  · rw [max_eq_left h]
    have hn : 0 ≤ x/4*(s-a)^2*(s+2*a) :=
      mul_nonneg (mul_nonneg (by linarith) (sq_nonneg _)) (by linarith)
    have he : 2*a/3-s*(1-s^2*x/4) = x/4*(s-a)^2*(s+2*a) := by
      nlinarith [congrArg (fun v : ℝ => v*s) hxa,congrArg (fun v : ℝ => v*a) hxa]
    linarith
  · rw [max_eq_right (le_of_not_ge h),mul_zero]
    positivity

theorem directRiskScale_mem (x : ℝ) : directRiskScale x ∈ Set.Icc (0:ℝ) 1 := by
  unfold directRiskScale
  split_ifs with hx
  · exact ⟨by norm_num,le_rfl⟩
  · exact ⟨(direct_large_scale_data x (le_of_not_ge hx)).1.1.le,
      (direct_large_scale_data x (le_of_not_ge hx)).1.2⟩

theorem directRiskProfile_max (t x : ℝ) (ht : 0 ≤ t) (hx : 0 ≤ x)
    (s : ℝ) (hs : s ∈ Set.Icc (0:ℝ) 1) :
    directRiskProfile t x s ≤ directRiskProfile t x (directRiskScale x) := by
  unfold directRiskScale
  split_ifs with hsmall
  · have hb := mul_le_mul_of_nonneg_left (direct_small_scale x s hx hsmall hs) (by positivity : 0 ≤ t/2)
    simpa only [directRiskProfile,one_pow,one_mul,max_eq_left (by linarith : 0 ≤ 1-x/4)] using
      (show s*t/2*max (1-s^2*x/4) 0 ≤ t/2*(1-x/4) by nlinarith [hb])
  · have hh := direct_large_scale_data x (le_of_not_ge hsmall)
    have hterm : 1-Real.sqrt (4/(3*x))^2*x/4 = 2/3 := by nlinarith [hh.2]
    have hb := mul_le_mul_of_nonneg_left (direct_large_scale x s (le_of_not_ge hsmall) hs.1)
      (by positivity : 0 ≤ t/2)
    unfold directRiskProfile
    rw [hterm,max_eq_left (by norm_num : (0:ℝ) ≤ 2/3)]
    nlinarith [hb]

theorem directRiskProfile_greatest (t x : ℝ) (ht : 0 ≤ t) (hx : 0 ≤ x) :
    IsGreatest ((directRiskProfile t x) '' Set.Icc (0:ℝ) 1)
      (directRiskProfile t x (directRiskScale x)) := by
  refine ⟨⟨directRiskScale x,directRiskScale_mem x,rfl⟩,?_⟩
  rintro y ⟨s,hs,rfl⟩
  exact directRiskProfile_max t x ht hx s hs

theorem directRiskProfile_square (t x : ℝ) (hx : 0 ≤ x) :
    (directRiskProfile t x (directRiskScale x))^2 = directRiskSquared t x := by
  unfold directRiskScale directRiskSquared
  split_ifs with hsmall
  · unfold directRiskProfile
    rw [one_pow,one_mul,one_mul,max_eq_left (by linarith : 0 ≤ 1-x/4)]
    ring
  · have hh := direct_large_scale_data x (le_of_not_ge hsmall)
    have hterm : 1-Real.sqrt (4/(3*x))^2*x/4 = 2/3 := by nlinarith [hh.2]
    have hx0 : 0 < x := by linarith
    unfold directRiskProfile
    rw [hterm,max_eq_left (by norm_num : (0:ℝ) ≤ 2/3)]
    calc
      _ = Real.sqrt (4/(3*x))^2*t^2/9 := by ring
      _ = _ := by rw [Real.sq_sqrt (by positivity : 0 ≤ 4/(3*x))]; ring

end ThresholdHC.Genie
