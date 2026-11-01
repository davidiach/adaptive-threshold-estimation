import ThresholdHC.EntropyTailLower.EntropyIncrement

noncomputable section
namespace ThresholdHC.EntropyTailLower
open Real ThresholdHC.EntropyTailQuantile
open scoped BigOperators

def maskedCost {I : Type} [DecidableEq I] (a : I → ℝ) (S : Finset I) (i : I) : ℝ :=
  if i ∈ S then a i else 0

def finiteSelectionScore {I : Type} [Fintype I] [DecidableEq I]
    (k : ℝ) (a e : I → ℝ) (S : Finset I) : ℝ :=
  k*sqrt (costEntropy (maskedCost a S)) + ∑ i, if i ∈ S then 0 else e i

theorem maskedCost_nonneg {I : Type} [DecidableEq I] (a : I → ℝ)
    (ha : ∀ i, 0 ≤ a i) (S : Finset I) (i : I) : 0 ≤ maskedCost a S i := by
  unfold maskedCost
  split_ifs
  · exact ha i
  · exact le_rfl

theorem costEntropy_single {I : Type} [Fintype I] [DecidableEq I] (j : I) (x : ℝ) :
    costEntropy (fun i => if i = j then x else 0) = x := by
  simp only [costEntropy, costTotal]
  simp_rw [apply_ite negMulLog,negMulLog_zero]
  simp

theorem finiteSelectionScore_insert_le {I : Type} [Fintype I] [DecidableEq I]
    (k : ℝ) (hk : 0 ≤ k) (a e : I → ℝ) (ha : ∀ i, 0 ≤ a i)
    (S : Finset I) (j : I) (hj : j ∉ S) :
    finiteSelectionScore k a e (insert j S) ≤
      finiteSelectionScore k a e S - e j + 2*k*sqrt (a j) := by
  have hmask : (fun i => maskedCost a S i + (if i = j then a j else 0)) =
      maskedCost a (insert j S) := by
    funext i
    by_cases hij : i = j
    · subst i; simp [maskedCost,hj]
    · simp [maskedCost,hij]
  have hs := sqrt_costEntropy_add (maskedCost a S) (fun i => if i = j then a j else 0)
    (maskedCost_nonneg a ha S) (fun i => by split_ifs; exact ha j; exact le_rfl)
  rw [hmask,costEntropy_single] at hs
  have hp : (∑ i, if i ∈ insert j S then 0 else e i) =
      (∑ i, if i ∈ S then 0 else e i)-e j := by
    have hi (i : I) : (if i ∈ insert j S then 0 else e i) =
        (if i ∈ S then 0 else e i)-(if i = j then e j else 0) := by
      by_cases hij : i = j
      · subst i; simp [hj]
      · simp [hij]
    simp_rw [hi]
    simp [Finset.sum_sub_distrib]
  have hm := mul_le_mul_of_nonneg_left hs hk
  unfold finiteSelectionScore
  rw [hp]
  linarith

theorem finiteSelectionScore_ordinary_penalty {I : Type} [Fintype I] [DecidableEq I]
    (k : ℝ) (hk : 0 ≤ k) (a e : I → ℝ) (ha : ∀ i, 0 ≤ a i)
    (S : Finset I) (j : I) (hj : j ∉ S)
    (hopt : finiteSelectionScore k a e S ≤ finiteSelectionScore k a e (insert j S)) :
    e j ≤ 2*k*sqrt (a j) := by
  have hh := finiteSelectionScore_insert_le k hk a e ha S j hj
  linarith

theorem ordinary_mass_of_penalty (w b ρ h : ℝ) (hw : 0 ≤ w) (hb : 0 < b)
    (hρ : 0 ≤ ρ) (hh : 0 < h)
    (hpen : w*h/b ≤ 2*(h*sqrt ρ)*sqrt (w/b^2)) : w ≤ 4*ρ := by
  rw [sqrt_div hw, sqrt_sq hb.le] at hpen
  have hm := mul_le_mul_of_nonneg_right hpen hb.le
  have hc : w*h ≤ 2*h*sqrt ρ*sqrt w := by
    field_simp at hm
    nlinarith only [mul_le_mul_of_nonneg_right hm hh.le]
  have hc' : w ≤ 2*sqrt ρ*sqrt w := by
    nlinarith only [hc,hh]
  have hr := sq_sqrt hρ
  have hw' := sq_sqrt hw
  have hsρ := sqrt_nonneg ρ
  have hsw := sqrt_nonneg w
  by_cases hz : w = 0
  · rw [hz]; positivity
  · have hpos : 0 < sqrt w := sqrt_pos.mpr (lt_of_le_of_ne hw (Ne.symm hz))
    have hroot : sqrt w ≤ 2*sqrt ρ := by nlinarith only [hc',hw',hpos]
    nlinarith only [hroot,hr,hw',hsρ,hsw]

theorem exists_finiteSelection_minimizer {I : Type} [Fintype I] [DecidableEq I]
    (k : ℝ) (a e : I → ℝ) :
    ∃ S : Finset I, ∀ T, finiteSelectionScore k a e S ≤ finiteSelectionScore k a e T := by
  obtain ⟨S,_,hS⟩ := Finset.exists_min_image Finset.univ
    (finiteSelectionScore k a e) Finset.univ_nonempty
  exact ⟨S,fun T => hS T (Finset.mem_univ T)⟩

theorem optimal_ordinary_band_mass {I : Type} [Fintype I] [DecidableEq I]
    (w b : I → ℝ) (hw : ∀ i, 0 ≤ w i) (hb : ∀ i, 0 < b i)
    (ρ h : ℝ) (hρ : 0 ≤ ρ) (hh : 0 < h) (S : Finset I)
    (hopt : ∀ T, finiteSelectionScore (h*sqrt ρ) (fun i => w i/(b i)^2)
      (fun i => w i*min 1 (h/b i)) S ≤
      finiteSelectionScore (h*sqrt ρ) (fun i => w i/(b i)^2)
      (fun i => w i*min 1 (h/b i)) T)
    (j : I) (hj : j ∉ S) (hordinary : h ≤ b j) : w j ≤ 4*ρ := by
  have he := finiteSelectionScore_ordinary_penalty (h*sqrt ρ) (by positivity)
    (fun i => w i/(b i)^2) (fun i => w i*min 1 (h/b i))
    (fun i => div_nonneg (hw i) (sq_nonneg _)) S j hj (hopt (insert j S))
  rw [min_eq_right ((div_le_one (hb j)).mpr hordinary)] at he
  have hp : w j*h/b j ≤ 2*(h*sqrt ρ)*sqrt (w j/(b j)^2) := by
    simpa only [mul_div_assoc] using he
  exact ordinary_mass_of_penalty (w j) (b j) ρ h (hw j) (hb j) hρ hh hp

end ThresholdHC.EntropyTailLower
