import ThresholdHC.EntropyTailLower.FiniteSelection

noncomputable section
namespace ThresholdHC.EntropyTailLower
open Real ThresholdHC.EntropyTailQuantile
open scoped BigOperators

theorem maskedCost_erase_add {I : Type} [DecidableEq I]
    (a : I → ℝ) (S : Finset I) (j : I) (hj : j ∈ S) (i : I) :
    maskedCost a (S.erase j) i + (if i = j then a j else 0) = maskedCost a S i := by
  by_cases hij : i = j
  · subst i; simp [maskedCost,hj]
  · simp [maskedCost,hij]

theorem costEntropy_erase_difference {I : Type} [Fintype I] [DecidableEq I]
    (a : I → ℝ) (S : Finset I) (j : I) (hj : j ∈ S) :
    costEntropy (maskedCost a S) - costEntropy (maskedCost a (S.erase j)) =
      a j + negMulLog (a j) + negMulLog (costTotal (maskedCost a (S.erase j))) -
        negMulLog (costTotal (maskedCost a S)) := by
  have ht : costTotal (maskedCost a S) = costTotal (maskedCost a (S.erase j)) + a j := by
    have he := funext (maskedCost_erase_add a S j hj)
    rw [← he,costTotal_add]
    simp [costTotal]
  have hn (i : I) : negMulLog (maskedCost a S i) =
      negMulLog (maskedCost a (S.erase j) i) + (if i = j then negMulLog (a j) else 0) := by
    by_cases hij : i = j
    · subst i; simp [maskedCost,hj]
    · simp [maskedCost,hij]
  have hs : (∑ i, negMulLog (maskedCost a S i)) =
      (∑ i, negMulLog (maskedCost a (S.erase j) i)) + negMulLog (a j) := by
    simp_rw [hn]
    simp [Finset.sum_add_distrib]
  unfold costEntropy
  rw [hs]
  linarith

theorem costEntropy_erase_lower {I : Type} [Fintype I] [DecidableEq I]
    (a : I → ℝ) (ha : ∀ i, 0 ≤ a i) (S : Finset I) (j : I)
    (hj : j ∈ S) (haj : 0 < a j) :
    a j * (1 + log (costTotal (maskedCost a S) / a j)) ≤
      costEntropy (maskedCost a S) - costEntropy (maskedCost a (S.erase j)) := by
  have ht : costTotal (maskedCost a S) = costTotal (maskedCost a (S.erase j)) + a j := by
    have he := funext (maskedCost_erase_add a S j hj)
    rw [← he,costTotal_add]
    simp [costTotal]
  have hb := binary_entropy_lower_right (costTotal (maskedCost a (S.erase j))) (a j)
    (costTotal_nonneg (maskedCost_nonneg a ha (S.erase j))) haj
  rw [← ht] at hb
  rw [costEntropy_erase_difference a S j hj]
  nlinarith only [hb]

theorem finiteSelectionScore_erase_penalty {I : Type} [Fintype I] [DecidableEq I]
    (k : ℝ) (a e : I → ℝ) (S : Finset I) (j : I) (hj : j ∈ S)
    (hopt : finiteSelectionScore k a e S ≤ finiteSelectionScore k a e (S.erase j)) :
    k * (sqrt (costEntropy (maskedCost a S)) -
      sqrt (costEntropy (maskedCost a (S.erase j)))) ≤ e j := by
  have hp : (∑ i, if i ∈ S.erase j then 0 else e i) =
      (∑ i, if i ∈ S then 0 else e i) + e j := by
    have hi (i : I) : (if i ∈ S.erase j then 0 else e i) =
        (if i ∈ S then 0 else e i) + (if i = j then e j else 0) := by
      by_cases hij : i = j
      · subst i; simp [hj]
      · simp [hij]
    simp_rw [hi]
    simp [Finset.sum_add_distrib]
  unfold finiteSelectionScore at hopt
  rw [hp] at hopt
  nlinarith only [hopt]

theorem optimal_retained_gap {I : Type} [Fintype I] [DecidableEq I]
    (a b e : I → ℝ) (ha : ∀ i, 0 ≤ a i) (ρ h : ℝ)
    (_hρ : 0 ≤ ρ) (hh : 0 < h) (S : Finset I) (j : I)
    (hj : j ∈ S) (haj : 0 < a j) (he : e j ≤ h*a j*b j)
    (hopt : finiteSelectionScore (h*sqrt ρ) a e S ≤
      finiteSelectionScore (h*sqrt ρ) a e (S.erase j)) :
    sqrt ρ * (1 + log (costTotal (maskedCost a S) / a j)) ≤
      2*b j*sqrt (costEntropy (maskedCost a S)) := by
  let F := costEntropy (maskedCost a S)
  let D := costEntropy (maskedCost a (S.erase j))
  have hF : 0 ≤ F := costEntropy_nonneg (maskedCost_nonneg a ha S)
  have hD : 0 ≤ D := costEntropy_nonneg (maskedCost_nonneg a ha (S.erase j))
  have hDF : D ≤ F := by
    apply costEntropy_mono (maskedCost_nonneg a ha (S.erase j))
    intro i
    by_cases hi : i ∈ S.erase j
    · have his : i ∈ S := (Finset.mem_erase.mp hi).2
      simp [maskedCost,hi,his]
    · simp only [maskedCost,ite_eq_right hi]
      exact maskedCost_nonneg a ha S i
  have hsDF := sqrt_le_sqrt hDF
  have hdiff : 0 ≤ sqrt F - sqrt D := sub_nonneg.mpr hsDF
  have hsq : F-D ≤ 2*sqrt F*(sqrt F-sqrt D) := by
    have hp := mul_nonneg hdiff hdiff
    nlinarith only [hp,sq_sqrt hF,sq_sqrt hD]
  have hpen := finiteSelectionScore_erase_penalty (h*sqrt ρ) a e S j hj hopt
  have hpen' : sqrt ρ*(sqrt F-sqrt D) ≤ a j*b j := by
    have hp : h*(sqrt ρ*(sqrt F-sqrt D)) ≤ h*(a j*b j) := by
      change (h*sqrt ρ)*(sqrt F-sqrt D) ≤ e j at hpen
      nlinarith only [hpen,he]
    exact le_of_mul_le_mul_left hp hh
  have hlow := costEntropy_erase_lower a ha S j hj haj
  change a j*(1+log (costTotal (maskedCost a S)/a j)) ≤ F-D at hlow
  have h1 := mul_le_mul_of_nonneg_left hlow (sqrt_nonneg ρ)
  have h2 := mul_le_mul_of_nonneg_left hsq (sqrt_nonneg ρ)
  have h3 := mul_le_mul_of_nonneg_left hpen' (show 0 ≤ 2*sqrt F by positivity)
  have hall : a j*(sqrt ρ*(1+log (costTotal (maskedCost a S)/a j))) ≤
      a j*(2*b j*sqrt F) := by nlinarith only [h1,h2,h3]
  exact le_of_mul_le_mul_left hall haj

theorem optimal_retained_band_gap {I : Type} [Fintype I] [DecidableEq I]
    (w b : I → ℝ) (hw : ∀ i, 0 ≤ w i) (hb : ∀ i, 0 < b i)
    (ρ h : ℝ) (hρ : 0 ≤ ρ) (hh : 0 < h) (S : Finset I)
    (hopt : ∀ T, finiteSelectionScore (h*sqrt ρ) (fun i => w i/(b i)^2)
      (fun i => w i*min 1 (h/b i)) S ≤
      finiteSelectionScore (h*sqrt ρ) (fun i => w i/(b i)^2)
      (fun i => w i*min 1 (h/b i)) T)
    (j : I) (hj : j ∈ S) (hwj : 0 < w j) :
    sqrt ρ * (1 + log (costTotal (maskedCost (fun i => w i/(b i)^2) S) /
      (w j/(b j)^2))) ≤
      2*b j*sqrt (costEntropy (maskedCost (fun i => w i/(b i)^2) S)) := by
  apply optimal_retained_gap (fun i => w i/(b i)^2) b
    (fun i => w i*min 1 (h/b i)) (fun i => div_nonneg (hw i) (sq_nonneg _))
    ρ h hρ hh S j hj (div_pos hwj (sq_pos_of_pos (hb j)))
  · have hm := mul_le_mul_of_nonneg_left (min_le_right (1:ℝ) (h/b j)) (hw j)
    convert hm using 1
    field_simp [(hb j).ne']
  · exact hopt (S.erase j)

end ThresholdHC.EntropyTailLower
