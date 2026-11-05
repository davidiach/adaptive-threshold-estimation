import ThresholdHC.QuantileSharpLaw.TailPrice

noncomputable section
open Real
open scoped BigOperators
namespace ThresholdHC.QuantileSharpLaw
open ThresholdHC.EntropyTailQuantile ThresholdHC.OptimalQuantile

theorem scaled_root_identity {T q E : ℝ} (hT : 0 < T) (hq : 0 ≤ q) (hE : 0 ≤ E) :
    T*sqrt ((q/T^2)*E) = sqrt (q*E) := by
  apply (sq_eq_sq₀ (mul_nonneg hT.le (sqrt_nonneg _)) (sqrt_nonneg _)).mp
  rw [mul_pow,sq_sqrt (mul_nonneg (div_nonneg hq (sq_nonneg _)) hE),sq_sqrt (mul_nonneg hq hE)]
  field_simp

theorem fullCoreCost_smul {n : ℕ} (s : ℝ) (b : Option (Fin n) → ℝ) :
    fullCoreCost n (fun i => s*b i) = s*fullCoreCost n b := by
  rw [fullCoreCost_eq_sum,fullCoreCost_eq_sum,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem unnormalized_selection_price {n : ℕ} {v b : Option (Fin n) → ℝ} {T q a M E c : ℝ}
    (hv : ∀ i, 0 ≤ v i) (hb : ∀ i, 0 ≤ b i) (hT : 0 < T) (hq : 0 ≤ q)
    (ha : 0 ≤ a) (haT : a ≤ T) (hE : 0 ≤ E)
    (hM : (T-a)^2 ≤ q*M)
    (hentropy : costEntropy (fun i => v i+M*boundaryUnit i) ≤ E)
    (hwork : q*fullCoreCost n b ≤ T*c) :
    T+sqrt (q*costEntropy (fun i => v i+b i)) ≤ scalarRoot*(sqrt (q*E)+a+c) := by
  let s := q/T^2
  let x := fun i => s*v i
  let y := fun i => s*b i
  have hs : 0 ≤ s := div_nonneg hq (sq_nonneg _)
  have hx : ∀ i, 0 ≤ x i := fun i => mul_nonneg hs (hv i)
  have hy : ∀ i, 0 ≤ y i := fun i => mul_nonneg hs (hb i)
  have he : 0 ≤ a/T := div_nonneg ha hT.le
  have he1 : a/T ≤ 1 := (div_le_one hT).mpr haT
  have hm : (1-a/T)^2 ≤ s*M := by
    have hi : (1-a/T)^2=(T-a)^2/T^2 := by field_simp
    rw [hi]
    calc
      _ ≤ (q*M)/T^2 := div_le_div_of_nonneg_right hM (sq_nonneg _)
      _ = _ := by dsimp [s]; ring
  have hr : sqrt (costEntropy (fun i => x i+(s*M)*boundaryUnit i)) ≤ sqrt (q*E)/T := by
    have hi : (fun i => x i+(s*M)*boundaryUnit i) =
        (fun i => s*(v i+M*boundaryUnit i)) := by
      funext i
      dsimp [x]
      ring
    rw [hi,costEntropy_smul]
    have hp := sqrt_le_sqrt (mul_le_mul_of_nonneg_left hentropy hs)
    apply hp.trans
    apply (le_div_iff₀ hT).mpr
    have hroot := scaled_root_identity hT hq hE
    dsimp only [s]
    nlinarith only [hroot]
  have hc : fullCoreCost n y ≤ c/T := by
    dsimp only [y]
    rw [fullCoreCost_smul]
    calc
      _ = (q*fullCoreCost n b)/T^2 := by dsimp [s]; ring
      _ ≤ (T*c)/T^2 := div_le_div_of_nonneg_right hwork (sq_nonneg _)
      _ = c/T := by field_simp
  have h := normalized_selection_price hx hy he he1 hm hr hc
  have hscaled := mul_le_mul_of_nonneg_left h hT.le
  have hi : (fun i => x i+y i) = (fun i => s*(v i+b i)) := by
    funext i
    dsimp [x,y]
    ring
  rw [hi,costEntropy_smul] at hscaled
  have hroot := scaled_root_identity hT hq
    (costEntropy_nonneg (fun i => add_nonneg (hv i) (hb i)))
  change T*sqrt (s*costEntropy (fun i => v i+b i)) =
    sqrt (q*costEntropy (fun i => v i+b i)) at hroot
  have hright : T*(scalarRoot*(sqrt (q*E)/T+a/T+c/T)) =
      scalarRoot*(sqrt (q*E)+a+c) := by field_simp
  rw [hright,mul_add,mul_one,hroot] at hscaled
  exact hscaled

end ThresholdHC.QuantileSharpLaw
