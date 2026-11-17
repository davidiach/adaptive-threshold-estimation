import ThresholdHC.SelectionApproximation.Compression
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Data.Rat.Floor

/-! Concrete zero/dyadic-cell keys, including the rational implementation. -/

namespace ThresholdHC.FiniteSelectionApproximation

/-- Integer dyadic exponent followed by the index of one of `M` equal cells.
The implementation uses integer logarithms and rational floor, not real logarithms. -/
def rationalKey (r : ℚ) (M : ℕ) (x : ℚ) : Option (ℤ × ℕ) :=
  if x ≤ 0 then none else
    let k := Int.log 2 (x/r)
    some (k, ⌊(M : ℚ) * (x / (r * 2^k) - 1)⌋₊)

noncomputable section
open scoped Classical
open ThresholdHC.SelectionApproximation

/-- The same key on real summaries, used by the mathematical finite solver. -/
def binKey (r : ℝ) (M : ℕ) (x : ℝ) : Option (ℤ × ℕ) :=
  if x ≤ 0 then none else
    let k := Int.log 2 (x/r)
    some (k, ⌊(M : ℝ) * (x / (r * 2^k) - 1)⌋₊)

theorem binKey_zero (r : ℝ) (M : ℕ) : binKey r M 0 = none := by
  simp [binKey]

theorem binKey_eq_none {r x : ℝ} {M : ℕ} (hx : 0 ≤ x) :
    binKey r M x = none ↔ x = 0 := by
  by_cases h : x ≤ 0
  · simp [binKey, le_antisymm h hx]
  · simp [binKey, h, ne_of_gt (lt_of_not_ge h)]

theorem dyadic_bounds {r x : ℝ} (hr : 0 < r) (hx : 0 < x) :
    let s := r * 2 ^ Int.log 2 (x/r)
    0 < s ∧ s ≤ x ∧ x < 2*s := by
  dsimp
  have hlo := Int.zpow_log_le_self (R := ℝ) (b := 2) (by decide) (div_pos hx hr)
  have hhi := Int.lt_zpow_succ_log_self (R := ℝ) (b := 2) (by decide) (x/r)
  rw [zpow_add₀ (by norm_num), zpow_one] at hhi
  refine ⟨by positivity, ?_, ?_⟩
  · nlinarith [(le_div_iff₀ hr).mp hlo]
  · nlinarith [(div_lt_iff₀ hr).mp hhi]

theorem binKey_cell {r x : ℝ} {M : ℕ} (hr : 0 < r) (hM : 0 < M)
    (hx : 0 < x) :
    ∃ k : ℤ, ∃ j : ℕ, binKey r M x = some (k,j) ∧ j < M ∧
      r*2^k*(1+(j:ℝ)/M) ≤ x ∧ x < r*2^k*(1+((j:ℝ)+1)/M) := by
  let k := Int.log 2 (x/r)
  let s := r*2^k
  let t := (M:ℝ)*(x/s-1)
  let j := ⌊t⌋₊
  obtain ⟨hs, hlo, hhi⟩ := dyadic_bounds hr hx
  change 0 < s at hs
  change s ≤ x at hlo
  change x < 2*s at hhi
  have hMr : (0:ℝ) < M := Nat.cast_pos.mpr hM
  have ht : 0 ≤ t := mul_nonneg hMr.le (sub_nonneg.mpr ((le_div_iff₀ hs).mpr (by simpa using hlo)))
  have htM : t < M := by
    have := (div_lt_iff₀ hs).mpr hhi
    dsimp [t]
    nlinarith
  have hfloor := Nat.floor_le ht
  have hceil := Nat.lt_floor_add_one t
  refine ⟨k, j, by simp [binKey, hx.not_ge, k, j, t, s],
    (Nat.floor_lt (by omega)).mpr htM, ?_, ?_⟩
  · change s*(1+(j:ℝ)/M) ≤ x
    have h1 : (j:ℝ)/M ≤ x/s-1 := (div_le_iff₀ hMr).mpr (by simpa [j, t, mul_comm] using hfloor)
    have h2 : 1+(j:ℝ)/M ≤ x/s := by linarith
    simpa only [mul_comm] using (le_div_iff₀ hs).mp h2
  · change x < s*(1+((j:ℝ)+1)/M)
    have h1 : x/s-1 < ((j:ℝ)+1)/M := (lt_div_iff₀ hMr).mpr (by simpa [j, t, mul_comm] using hceil)
    have h2 : x/s < 1+((j:ℝ)+1)/M := by linarith
    simpa only [mul_comm] using (div_lt_iff₀ hs).mp h2

/-- The concrete dyadic-cell map supplies the previously abstract bin certificate. -/
theorem binKey_valid {r : ℝ} {M : ℕ} (hr : 0 < r) (hM : 0 < M) :
    ValidBins (1+1/(M:ℝ)) (binKey r M) := by
  intro x y hx hy he
  by_cases hz : x = 0
  · have hyz : y = 0 := (binKey_eq_none hy).mp (he.symm.trans (by simp [hz, binKey_zero]))
    simp [hz, hyz, Close]
  · have hxp : 0 < x := lt_of_le_of_ne hx (Ne.symm hz)
    have hyp : 0 < y := by
      apply lt_of_le_of_ne hy
      intro h
      exact hz ((binKey_eq_none hx).mp (he.trans (by simp [← h, binKey_zero])))
    obtain ⟨k,j,hk,hj,hxl,hxu⟩ := binKey_cell hr hM hxp
    obtain ⟨l,i,hl,hi,hyl,hyu⟩ := binKey_cell hr hM hyp
    have hpair : (k,j) = (l,i) := Option.some.inj (hk.symm.trans (he.trans hl))
    obtain ⟨rfl,rfl⟩ := Prod.mk.inj hpair
    exact dyadic_cell_close (by positivity) (by exact_mod_cast hM) (by positivity)
      ⟨hxl,hxu.le⟩ ⟨hyl,hyu.le⟩

/-- The computable rational key and the mathematical key agree exactly. -/
theorem rationalKey_cast (r x : ℚ) (M : ℕ) :
    rationalKey r M x = binKey (r:ℝ) M (x:ℝ) := by
  have hf (q : ℚ) : ⌊(q:ℝ)⌋₊ = ⌊q⌋₊ :=
    Nat.map_floor (algebraMap ℚ ℝ) (by exact Rat.cast_strictMono) q
  have hc (q : ℚ) : ⌈(q:ℝ)⌉₊ = ⌈q⌉₊ :=
    Nat.map_ceil (algebraMap ℚ ℝ) (by exact Rat.cast_strictMono) q
  have hlog : Int.log 2 (x/r) = Int.log 2 ((x:ℝ)/(r:ℝ)) := by
    simp only [Int.log]
    norm_cast
    simp only [hf, hc]
  simp only [rationalKey, binKey]
  split_ifs with h h' h'
  · rfl
  · exact (h' (by exact_mod_cast h)).elim
  · exact (h (by exact_mod_cast h')).elim
  · rw [hlog]
    congr 2
    have he : ((M:ℝ)*((x:ℝ)/((r:ℝ)*2^Int.log 2 ((x:ℝ)/(r:ℝ)))-1)) =
        (((M:ℚ)*(x/(r*2^Int.log 2 ((x:ℝ)/(r:ℝ)))-1)):ℚ) := by push_cast; rfl
    rw [he, hf]

end
end ThresholdHC.FiniteSelectionApproximation
