import ThresholdHC.QuantileOptimality.Geometry

noncomputable section
open Real
open scoped BigOperators
namespace ThresholdHC.QuantileOptimality
open ThresholdHC.OptimalQuantile

def upperMass (m : ℕ) (x : Option (Fin m) → ℝ) : ℝ :=
  1+x none+∑ j : Fin m, x (some j)*((2 : ℝ)^(j.val+1))^2

def chosenRarity (m : ℕ) (x : Option (Fin m) → ℝ) : ℝ := 1/(4*upperMass m x)

def massScale (m : ℕ) (x : Option (Fin m) → ℝ) (η : ℝ) : ℝ :=
  1+x none+∑ j : Fin m, x (some j)*((2 : ℝ)^j.val*(1+η))^2

def easyMass (m : ℕ) (x : Option (Fin m) → ℝ) (η : ℝ) : ℝ :=
  1-chosenRarity m x*massScale m x η

theorem upperMass_ge_one {m : ℕ} {x : Option (Fin m) → ℝ} (hx : ∀ i, 0 ≤ x i) :
    1 ≤ upperMass m x := by
  have hs : 0 ≤ ∑ j : Fin m, x (some j)*((2 : ℝ)^(j.val+1))^2 :=
    Finset.sum_nonneg (fun j _ => mul_nonneg (hx (some j)) (sq_nonneg _))
  unfold upperMass
  linarith only [hx none,hs]

theorem chosenRarity_pos {m : ℕ} {x : Option (Fin m) → ℝ} (hx : ∀ i, 0 ≤ x i) :
    0 < chosenRarity m x := by
  unfold chosenRarity
  exact div_pos (by norm_num) (by linarith [upperMass_ge_one hx])

theorem chosenRarity_le_quarter {m : ℕ} {x : Option (Fin m) → ℝ} (hx : ∀ i, 0 ≤ x i) :
    chosenRarity m x ≤ 1/4 := by
  unfold chosenRarity
  exact div_le_div_of_nonneg_left (by norm_num) (by norm_num : (0 : ℝ) < 4)
    (by linarith [upperMass_ge_one hx])

theorem massScale_ge_one {m : ℕ} {x : Option (Fin m) → ℝ} (hx : ∀ i, 0 ≤ x i) (η : ℝ) :
    1 ≤ massScale m x η := by
  have hs : 0 ≤ ∑ j : Fin m, x (some j)*((2 : ℝ)^j.val*(1+η))^2 :=
    Finset.sum_nonneg (fun j _ => mul_nonneg (hx (some j)) (sq_nonneg _))
  unfold massScale
  linarith only [hx none,hs]

theorem massScale_le_upperMass {m : ℕ} {x : Option (Fin m) → ℝ} (hx : ∀ i, 0 ≤ x i)
    {η : ℝ} (hη : 0 ≤ η) (hη1 : η ≤ 1) : massScale m x η ≤ upperMass m x := by
  apply add_le_add le_rfl
  apply Finset.sum_le_sum
  intro j _
  apply mul_le_mul_of_nonneg_left _ (hx (some j))
  apply (sq_le_sq₀ (by positivity) (by positivity)).mpr
  rw [pow_succ]
  exact mul_le_mul_of_nonneg_left (by linarith : 1+η ≤ 2) (by positivity)

theorem easyMass_bounds {m : ℕ} {x : Option (Fin m) → ℝ} (hx : ∀ i, 0 ≤ x i)
    {η : ℝ} (hη : 0 ≤ η) (hη1 : η ≤ 1) : 3/4 ≤ easyMass m x η ∧ easyMass m x η ≤ 1 := by
  have hr := chosenRarity_pos hx
  have hs := massScale_ge_one hx η
  have hm := mul_le_mul_of_nonneg_left (massScale_le_upperMass hx hη hη1) hr.le
  have he : chosenRarity m x*upperMass m x=1/4 := by
    have hU : 0 < upperMass m x := by linarith [upperMass_ge_one hx]
    unfold chosenRarity
    field_simp
  have hn : 0 ≤ chosenRarity m x*massScale m x η := mul_nonneg hr.le (by linarith)
  rw [he] at hm
  unfold easyMass
  constructor <;> linarith only [hm,hn]

end ThresholdHC.QuantileOptimality
