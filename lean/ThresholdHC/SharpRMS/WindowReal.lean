import ThresholdHC.SharpRMS.Window
import Mathlib.Tactic

/-! Coverage of real flip biases by the certified integer intervals. -/
namespace ThresholdHC.SharpRMS.Window

private def lastEndpoint (lo : ℕ) : List ℕ → ℕ
  | [] => lo
  | hi :: rest => lastEndpoint hi rest

private theorem cover (lo : ℕ) (rest : List ℕ) (nonempty : rest ≠ [])
    (ok : gridChain lo rest) (x : ℝ) (left : (lo:ℝ) ≤ x)
    (right : x ≤ (lastEndpoint lo rest:ℝ)) :
    ∃ a b : ℕ, b ∈ rest ∧ gridBound a b ∧ (a:ℝ) ≤ x ∧ x ≤ (b:ℝ) := by
  induction rest generalizing lo with
  | nil => contradiction
  | cons hi rest ih =>
    obtain ⟨bound, tail⟩ := ok
    by_cases h : x ≤ (hi:ℝ)
    · exact ⟨lo,hi,List.mem_cons_self,bound,left,h⟩
    · have hr : rest ≠ [] := by
        rintro rfl
        exact h right
      obtain ⟨a,b,mem,rest⟩ := ih hi hr tail (le_of_not_ge h) right
      exact ⟨a,b,List.mem_cons_of_mem _ mem,rest⟩

/-- Every real bias lies below a certified grid endpoint. Rescaling the
integer upper sum from that endpoint to the actual bias preserves the 2/3 cap. -/
theorem real_window_endpoint (s : ℝ) (hs : 2/5 ≤ s) (hs' : s ≤ 39/40) :
    ∃ hi : ℕ, hi < biasDenominator ∧ s ≤ (hi:ℝ)/40960 ∧
      (((hi:ℝ)/40960)/s)^2 * ((upperSum hi:ℝ)/((bins:ℝ)*(scale:ℝ))) ≤ 2/3 := by
  have hl : (16384:ℝ) ≤ 40960*s := by linarith
  have hr : 40960*s ≤ (lastEndpoint 16384 endpoints:ℝ) := by
    change 40960*s ≤ 39936
    linarith
  obtain ⟨a,b,mem,hgrid,hl',hr'⟩ := cover 16384 endpoints (by decide) checked_window (40960*s) hl hr
  have all : ∀ b ∈ endpoints, b < biasDenominator := by decide +kernel
  refine ⟨b,all b mem,by linarith,?_⟩
  have hnat := hgrid.2.2
  have hreal : 3*(b:ℝ)^2*(upperSum b:ℝ) ≤ 2*(a:ℝ)^2*(bins:ℝ)*(scale:ℝ) := by
    exact_mod_cast hnat
  have ha : (a:ℝ)^2 ≤ (40960*s)^2 := by
    nlinarith only [mul_nonneg (sub_nonneg.mpr hl') (show 0 ≤ 40960*s+(a:ℝ) by positivity)]
  have hpos : 0 < s := by linarith
  have bpos : 0 < (bins:ℝ) := by norm_num [bins]
  have spos : 0 < (scale:ℝ) := by norm_num [scale]
  have hraw := hreal.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ha (by norm_num : (0:ℝ) ≤ 2)) bpos.le) spos.le)
  field_simp
  nlinarith only [hraw]

theorem real_window (s : ℝ) (hs : 2/5 ≤ s) (hs' : s ≤ 39/40) :
    ∃ hi : ℕ, s ≤ (hi:ℝ)/40960 ∧
      (((hi:ℝ)/40960)/s)^2 * ((upperSum hi:ℝ)/((bins:ℝ)*(scale:ℝ))) ≤ 2/3 := by
  obtain ⟨hi,_,data⟩ := real_window_endpoint s hs hs'
  exact ⟨hi,data⟩

end ThresholdHC.SharpRMS.Window
