import ThresholdHC.DeterministicCertificates.Intervals

open scoped BigOperators
namespace ThresholdHC.DeterministicCertificates

/-- A finite rational lower sum and a geometric remainder for the atanh series.
The remainder deliberately uses Mathlib's independent (looser) bound, rather
than trusting the toolkit's smaller remainder formula. -/
def unitLog (x : ℚ) (n : ℕ) : Interval :=
  let z := (x-1)/(x+1)
  let s := 2 * ∑ i ∈ Finset.range n, z^(2*i+1)/(2*i+1)
  ⟨s,s+2*z^(2*n+1)/(1-z^2)⟩

theorem unitLog_sound {x : ℚ} (hx : 1 ≤ x) (n : ℕ) :
    Contains (unitLog x n) (Real.log (x:ℝ)) := by
  have hxr : (1:ℝ) ≤ x := by exact_mod_cast hx
  let z : ℝ := ((x:ℝ)-1)/((x:ℝ)+1)
  have hz0 : 0 ≤ z := div_nonneg (by linarith) (by linarith)
  have hz1 : z < 1 := by dsimp [z]; apply (div_lt_one (by linarith)).mpr; linarith
  have he : (1+z)/(1-z) = (x:ℝ) := by
    dsimp [z]
    field_simp
    <;> ring
  have hlo := Real.sum_range_le_log_div hz0 hz1 n
  have hhi := Real.log_div_le_sum_range_add hz0 hz1 n
  rw [he] at hlo hhi
  unfold Contains unitLog
  dsimp
  push_cast
  change 2*(∑ i ∈ Finset.range n,z^(2*i+1)/(2*(i:ℝ)+1)) ≤ Real.log (x:ℝ) ∧
    Real.log (x:ℝ) ≤ 2*(∑ i ∈ Finset.range n,z^(2*i+1)/(2*(i:ℝ)+1))+2*z^(2*n+1)/(1-z^2)
  constructor
  · linarith
  · calc
      Real.log (x:ℝ) ≤ 2*((∑ i ∈ Finset.range n,z^(2*i+1)/(2*(i:ℝ)+1))+
          z^(2*n+1)/(1-z^2)) := by linarith
      _ = _ := by ring

structure LogWitness where
  exponent : ℤ
  terms : ℕ
  deriving DecidableEq, Repr

def logRange (x : ℚ) (w : LogWitness) : Bool :=
  decide (0 < x ∧ 1 ≤ x/(2:ℚ)^w.exponent ∧ x/(2:ℚ)^w.exponent ≤ 2)

def logBounds (x : ℚ) (w : LogWitness) : Interval :=
  add (unitLog (x/(2:ℚ)^w.exponent) w.terms)
    (scale (w.exponent:ℚ) (unitLog 2 w.terms))

theorem logBounds_sound {x : ℚ} {w : LogWitness} (h : logRange x w = true) :
    Contains (logBounds x w) (Real.log (x:ℝ)) := by
  have hq : 0 < x ∧ 1 ≤ x/(2:ℚ)^w.exponent ∧ x/(2:ℚ)^w.exponent ≤ 2 := by
    simpa [logRange] using h
  have hi := add_sound (unitLog_sound hq.2.1 w.terms)
    (scale_sound (w.exponent:ℚ) (unitLog_sound (x := 2) (by norm_num) w.terms))
  have hx : (x:ℝ) ≠ 0 := ne_of_gt (by exact_mod_cast hq.1)
  have he : Real.log ((x/(2:ℚ)^w.exponent:ℚ):ℝ) +
      ((w.exponent:ℚ):ℝ)*Real.log (2:ℝ) = Real.log (x:ℝ) := by
    push_cast
    rw [Real.log_div hx (by positivity),Real.log_zpow]
    ring
  simpa only [Rat.cast_ofNat,he,logBounds] using hi

/-- Both endpoints of the child interval are enclosed independently; monotonicity
then covers every real argument inside that interval. -/
def logCheck (input output : Interval) (lower upper : LogWitness) : Bool :=
  logRange input.lower lower && logRange input.upper upper &&
    decide (output.lower ≤ (logBounds input.lower lower).lower ∧
      (logBounds input.upper upper).upper ≤ output.upper)

theorem logCheck_sound {input output : Interval} {lower upper : LogWitness} {x : ℝ}
    (h : logCheck input output lower upper = true) (hi : Contains input x) :
    Contains output (Real.log x) := by
  simp only [logCheck,Bool.and_eq_true,decide_eq_true_eq] at h
  have hlo := logBounds_sound h.1.1
  have hhi := logBounds_sound h.1.2
  have hpq : 0 < input.lower := (show 0 < input.lower ∧ _ by
    simpa [logRange] using h.1.1).1
  have hp : (0:ℝ) < input.lower := by exact_mod_cast hpq
  have hx : 0 < x := hp.trans_le hi.1
  refine ⟨?_,?_⟩
  · exact (show (output.lower:ℝ) ≤ (logBounds input.lower lower).lower by exact_mod_cast h.2.1).trans
      (hlo.1.trans (Real.log_le_log hp hi.1))
  · exact ((Real.log_le_log hx hi.2).trans hhi.2).trans
      (by exact_mod_cast h.2.2)

end ThresholdHC.DeterministicCertificates
