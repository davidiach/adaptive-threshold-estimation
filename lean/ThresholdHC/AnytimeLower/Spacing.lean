
import ThresholdHC.AnytimeLower.TestingSchedule

noncomputable section
open Real Filter
open scoped Topology
namespace ThresholdHC.AnytimeLower

theorem sqrt_increment_bound {x y : ℝ} (hx : 0 ≤ x)
    (hy : y ≤ x+sqrt x) : sqrt y ≤ sqrt x+1/2 := by
  apply (sqrt_le_iff).mpr
  refine ⟨by positivity,?_⟩
  nlinarith [sq_sqrt hx,sqrt_nonneg x]

theorem sqrt_growth_bound (x : ℕ → ℝ) (hx : ∀ k, 0 ≤ x k)
    (m : ℕ) (hstep : ∀ k, m ≤ k → x (k+1)-x k ≤ sqrt (x k)) (k : ℕ) :
    sqrt (x (m+k)) ≤ sqrt (x m)+(k:ℝ)/2 := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hb := sqrt_increment_bound (hx (m+k))
      (show x (m+k+1) ≤ x (m+k)+sqrt (x (m+k)) by
        linarith [hstep (m+k) (Nat.le_add_right m k)])
    have hi : sqrt (x (m+(k+1))) ≤ sqrt (x (m+k))+1/2 := by
      simpa only [Nat.add_assoc] using hb
    push_cast
    linarith

/-- If the indices exceed a quadratic bound infinitely often, infinitely
many successive blocks have length at least the square root of their start. -/
theorem frequently_long_blocks (x : ℕ → ℝ) (hx : ∀ k, 0 ≤ x k)
    (hlarge : ∃ᶠ k : ℕ in atTop, (k:ℝ)^2 < x k) :
    ∃ᶠ k in atTop, sqrt (x k) ≤ x (k+1)-x k := by
  by_contra hh
  simp only [not_frequently,not_le] at hh
  obtain ⟨m,hm⟩ := eventually_atTop.mp hh
  obtain ⟨n,hn⟩ := exists_nat_gt (2*sqrt (x m))
  obtain ⟨k,hk,hkn⟩ := (hlarge.and_eventually (eventually_ge_atTop (max m n))).exists
  have hmk : m ≤ k := (le_max_left _ _).trans hkn
  have hnk : n ≤ k := (le_max_right _ _).trans hkn
  have hrec := sqrt_growth_bound x hx m (fun i hi => (hm i hi).le) (k-m)
  rw [Nat.add_sub_of_le hmk] at hrec
  have hnreal : (n:ℝ) ≤ k := by exact_mod_cast hnk
  have hsub : ((k-m:ℕ):ℝ) ≤ k := by exact_mod_cast Nat.sub_le k m
  have hroot : sqrt (x k) ≤ (k:ℝ) := by linarith
  have hsq := sq_sqrt (hx k)
  have hknn := Nat.cast_nonneg (α:=ℝ) k
  nlinarith [sqrt_nonneg (x k)]

end ThresholdHC.AnytimeLower
