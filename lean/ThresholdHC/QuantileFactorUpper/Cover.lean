import ThresholdHC.QuantileFactorUpper.Truncation
import ThresholdHC.QuantileFactorUpper.Convexity
import ThresholdHC.QuantileFactorUpper.ExpEnclosure

/-! Soundness of the bisection checker.

On an accepted cell `[l,r]` of the grid, the partition series at
`k = 1462554551280/10^12` is at most the five-term sum plus `2^-62`
(`Truncation`), the five-term sum is at most its larger endpoint value plus
`25(r-l)^2/8` (`Convexity`), and each endpoint value plus `2^-62` is at most the
checker's value (`ExpEnclosure`). The cell test then places the series below one
on the whole cell, and induction on the fuel covers every cell `certify` splits. -/
noncomputable section
open Real
namespace ThresholdHC.QuantileFactorUpper
open ThresholdHC.OptimalQuantile

theorem factor_ge_sqrt : sqrt 2 ≤ (1462554551280/1000000000000 : ℝ) :=
  Real.sqrt_le_iff.mpr ⟨by norm_num, by norm_num⟩

theorem factor_le_cap : (1462554551280/1000000000000 : ℝ) ≤ 31/20 := by norm_num

theorem cell_sound {l r : ℕ} (h : cellOK l r = true) (hl : gridDen ≤ l) (hlr : l ≤ r)
    (hr : 20*r ≤ 31*gridDen) {u : ℝ} (hlu : (l : ℝ)/gridDen ≤ u) (hur : u ≤ (r : ℝ)/gridDen) :
    partitionSeries (1462554551280/1000000000000) u < 1 := by
  have hN : (0 : ℝ) < gridDen := by exact_mod_cast gridDen_pos
  have hs : (0 : ℝ) < scale := by exact_mod_cast scale_pos
  have hl1 : 1 ≤ (l : ℝ)/gridDen := by
    rw [le_div_iff₀ hN, one_mul]
    exact_mod_cast hl
  have hr1 : (r : ℝ)/gridDen ≤ 31/20 := by
    rw [div_le_iff₀ hN]
    have : (20*r : ℝ) ≤ 31*gridDen := by exact_mod_cast hr
    linarith
  have hu1 : 1 ≤ u := hl1.trans hlu
  have htr := partitionSeries_le_truncation factor_ge_sqrt hu1
  have hch := chord_bound factor_ge_sqrt factor_le_cap hl1 hr1 hlu hur
  have hcl := crit_sound (lt_of_lt_of_le gridDen_pos hl)
  have hcr := crit_sound (lt_of_lt_of_le gridDen_pos (hl.trans hlr))
  have hcell : 8*gridDen^2*max (crit l) (crit r)+25*(r-l)^2*scale < 8*gridDen^2*scale :=
    of_decide_eq_true h
  have hreal : 8*(gridDen : ℝ)^2*max (crit l : ℝ) (crit r : ℝ)+25*((r : ℝ)-l)^2*scale <
      8*(gridDen : ℝ)^2*scale := by
    have h' := (Nat.cast_lt (α := ℝ)).mpr hcell
    push_cast [Nat.cast_sub hlr] at h'
    exact h'
  set X := max (crit l : ℝ) (crit r : ℝ)
  have hXl : (crit l : ℝ)/scale ≤ X/scale :=
    div_le_div_of_nonneg_right (le_max_left _ _) hs.le
  have hXr : (crit r : ℝ)/scale ≤ X/scale :=
    div_le_div_of_nonneg_right (le_max_right _ _) hs.le
  have hm : max (finitePartition 5 (1462554551280/1000000000000) ((l : ℝ)/gridDen))
      (finitePartition 5 (1462554551280/1000000000000) ((r : ℝ)/gridDen)) ≤ X/scale-1/2^62 :=
    max_le (by linarith) (by linarith)
  have hfin : X/scale+25*((r : ℝ)/gridDen-(l : ℝ)/gridDen)^2/8 < 1 := by
    have he : X/scale+25*((r : ℝ)/gridDen-(l : ℝ)/gridDen)^2/8 =
        (8*(gridDen : ℝ)^2*X+25*((r : ℝ)-l)^2*scale)/(8*(gridDen : ℝ)^2*scale) := by
      field_simp
    rw [he, div_lt_one (by positivity)]
    exact hreal
  linarith

theorem certify_sound (d : ℕ) : ∀ l r : ℕ, certify d l r = true → gridDen ≤ l → l ≤ r →
    20*r ≤ 31*gridDen → ∀ u : ℝ, (l : ℝ)/gridDen ≤ u → u ≤ (r : ℝ)/gridDen →
      partitionSeries (1462554551280/1000000000000) u < 1 := by
  induction d with
  | zero =>
    intro l r h hl hlr hr u hlu hur
    exact cell_sound h hl hlr hr hlu hur
  | succ d ih =>
    intro l r h hl hlr hr u hlu hur
    simp only [certify, Bool.or_eq_true, Bool.and_eq_true] at h
    rcases h with h | ⟨h1, h2⟩
    · exact cell_sound h hl hlr hr hlu hur
    · have hm1 : l ≤ (l+r)/2 := by omega
      have hm2 : (l+r)/2 ≤ r := by omega
      rcases le_total u ((((l+r)/2 : ℕ) : ℝ)/gridDen) with hu | hu
      · exact ih l ((l+r)/2) h1 hl hm1 (by omega) u hlu hu
      · exact ih ((l+r)/2) r h2 (by omega) hm2 hr u hu hur

theorem cover_of_certify (hc : certify 24 gridDen gridTop = true) {u : ℝ}
    (hu : u ∈ Set.Icc (1 : ℝ) (31/20)) :
    partitionSeries (1462554551280/1000000000000) u < 1 := by
  have hN : (0 : ℝ) < gridDen := by exact_mod_cast gridDen_pos
  have htop : (gridTop : ℝ)/gridDen = 31/20 := by
    unfold gridTop gridDen
    norm_num
  apply certify_sound 24 gridDen gridTop hc le_rfl
  · unfold gridDen gridTop
    norm_num
  · unfold gridDen gridTop
    norm_num
  · rw [div_self hN.ne']
    exact hu.1
  · rw [htop]
    exact hu.2

end ThresholdHC.QuantileFactorUpper
