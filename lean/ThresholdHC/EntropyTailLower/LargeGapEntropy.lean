import ThresholdHC.EntropyTailLower.CertificateLabel
import ThresholdHC.EntropyTailLower.CanonicalBands
import ThresholdHC.EntropyTailQuantile.CostEntropy

noncomputable section
namespace ThresholdHC.EntropyTailLower
open MeasureTheory Real
open scoped BigOperators
open ThresholdHC.Tier6 ThresholdHC.StoppingProgram ThresholdHC.EntropyTailQuantile

theorem six_cost_entropy_bound (a : Fin 6 → ℝ) (ha : ∀ i, 0 ≤ a i) :
    costEntropy a ≤ 4*∑ i, a i := by
  have hp : (∑ _i : Fin 6, (1/6:ℝ)) ≤ 1 := by norm_num
  have hh := costEntropy_le_reference ha (fun _i : Fin 6 => by norm_num : ∀ _i : Fin 6, (0:ℝ) < 1/6) hp
  have h2 := log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 2)
  have h3 := log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 3)
  have he : log (6:ℝ) = log 2+log 3 := by
    rw [← log_mul (by norm_num : (2:ℝ) ≠ 0) (by norm_num : (3:ℝ) ≠ 0)]
    norm_num
  have hl : log (6:ℝ) ≤ 3 := by linarith
  have hn := Finset.sum_nonneg (s := Finset.univ) (fun i _ => ha i)
  have hp' := mul_le_mul_of_nonneg_right hl hn
  simp only [one_div,log_inv,sub_neg_eq_add,← Finset.sum_mul] at hh
  nlinarith only [hh,hp']

theorem six_band_entropy_bound (w : Fin 6 → ℝ) (hw : ∀ i, 0 ≤ w i)
    (hwm : (∑ i, w i) ≤ 1) :
    costEntropy (fun i => w i/((1/2:ℝ)^(i.val+1))^2) ≤ 16384 := by
  have hb (i : Fin 6) : (1/64:ℝ) ≤ (1/2:ℝ)^(i.val+1) := by
    have hh := pow_le_pow_of_le_one (by norm_num : (0:ℝ) ≤ 1/2)
      (by norm_num : (1/2:ℝ) ≤ 1) (show i.val+1 ≤ 6 by omega)
    norm_num at hh
    exact hh
  have hi (i) : w i/((1/2:ℝ)^(i.val+1))^2 ≤ 4096*w i := by
    apply (div_le_iff₀ (show (0:ℝ) < ((1/2:ℝ)^(i.val+1))^2 by positivity)).mpr
    have hs : (1:ℝ) ≤ 4096*((1/2:ℝ)^(i.val+1))^2 := by nlinarith only [hb i]
    nlinarith only [mul_le_mul_of_nonneg_left hs (hw i)]
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hi i)
  rw [← Finset.mul_sum] at hs
  have he := six_cost_entropy_bound (fun i => w i/((1/2:ℝ)^(i.val+1))^2)
    (fun i => div_nonneg (hw i) (sq_nonneg _))
  linarith

theorem canonical_band_mass_sum_le_one {I : Type} [Fintype I]
    (μ : Measure Gap) [IsProbabilityMeasure μ] (j : I → ℕ) (hj : Function.Injective j) :
    (∑ i, μ.real (ThresholdHC.EntropyTail.band (j i))) ≤ 1 := by
  have hh := sum_measureReal_le_measureReal_univ (μ := μ) (s := Finset.univ)
    (t := fun i => ThresholdHC.EntropyTail.band (j i))
    (fun i _ => ThresholdHC.EntropyTail.measurableSet_band (j i))
    (by intro i _ k _ hik; exact ThresholdHC.EntropyTail.band_disjoint (fun he => hik (hj he)))
  simpa using hh

theorem certificate_high_band_entropy_bound {N : ℕ}
    (μ : Measure Gap) [IsProbabilityMeasure μ] (ρ B : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (hB : 0 < B) (C : Certificate N) (hC : Feasible μ ρ B C)
    (p : Fin 6 → Prop) [DecidablePred p] :
    min ρ (sqrt (ρ*costEntropy (fun i : Fin 6 => if p i then
      μ.real (ThresholdHC.EntropyTail.band i.val)/((1/2:ℝ)^(i.val+1))^2 else 0)/B)) ≤
      16384*C.bias+512*sqrt C.variance := by
  let w := fun i : Fin 6 => if p i then μ.real (ThresholdHC.EntropyTail.band i.val) else 0
  have hw (i) : 0 ≤ w i := by
    dsimp [w]
    split_ifs
    · exact measureReal_nonneg
    · exact le_rfl
  have hm : (∑ i, w i) ≤ 1 := by
    apply le_trans _ (canonical_band_mass_sum_le_one μ (fun i : Fin 6 => i.val) Fin.val_injective)
    apply Finset.sum_le_sum
    intro i _
    dsimp [w]
    split_ifs
    · exact le_rfl
    · exact measureReal_nonneg
  have he : (fun i => w i/((1/2:ℝ)^(i.val+1))^2) =
      (fun i => if p i then μ.real (ThresholdHC.EntropyTail.band i.val)/((1/2:ℝ)^(i.val+1))^2 else 0) := by
    funext i
    dsimp [w]
    split_ifs <;> simp
  have hb := six_band_entropy_bound w hw hm
  have hn := costEntropy_nonneg (fun i => div_nonneg (hw i) (sq_nonneg ((1/2:ℝ)^(i.val+1))))
  rw [he] at hb hn
  exact certificate_bounded_entropy_cost μ ρ B hρ hρ1 hB C hC _ hn hb

end ThresholdHC.EntropyTailLower
