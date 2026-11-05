import ThresholdHC.AnytimeLower.InflatedScale

noncomputable section
open Real Filter
open scoped Topology
namespace ThresholdHC.AnytimeLower

def sparseOffset (j : ℕ) : ℕ := ⌊sqrt (j:ℝ)/2⌋₊
def sparseIndex (j : ℕ) : ℕ := j+sparseOffset j
def sparseBudget (τ : ℝ) (j : ℕ) : ℕ := ⌈(16:ℝ)^(sparseIndex j)/τ^2⌉₊

theorem sparseOffset_bounds (j : ℕ) :
    (sparseOffset j:ℝ) ≤ sqrt (j:ℝ)/2 ∧ sqrt (j:ℝ)/2 < (sparseOffset j:ℝ)+1 :=
  ⟨Nat.floor_le (by positivity),Nat.lt_floor_add_one _⟩

theorem sixteen_pow_quadratic (a : ℕ) (ha : 2 ≤ a) :
    16*((a:ℝ)+1)^2 ≤ (16:ℝ)^a := by
  induction a,ha using Nat.le_induction with
  | base => norm_num
  | succ a ha ih =>
    rw [pow_succ (16:ℝ) a]
    push_cast
    have hn : (2:ℝ) ≤ a := by exact_mod_cast ha
    nlinarith [sq_nonneg (a:ℝ)]

theorem sparseOffset_power {j : ℕ} (hj : 64 ≤ j) :
    3*((j:ℝ)+1) ≤ (16:ℝ)^(sparseOffset j) := by
  have hjr : (64:ℝ) ≤ j := by exact_mod_cast hj
  have hs : (8:ℝ) ≤ sqrt (j:ℝ) := by
    apply (le_sqrt (by norm_num) (by positivity)).mpr
    norm_num
    exact hj
  have hb := sparseOffset_bounds j
  have ha : 2 ≤ sparseOffset j := by
    apply Nat.le_floor
    norm_num
    linarith
  have hp := sixteen_pow_quadratic _ ha
  have hsq := sq_sqrt (show (0:ℝ) ≤ j by positivity)
  have hnon := Nat.cast_nonneg (α:=ℝ) (sparseOffset j)
  nlinarith

theorem sparseIndex_polynomial (j : ℕ) :
    (sparseIndex j:ℝ) ≤ ((j:ℝ)+2)^2 := by
  have hb := (sparseOffset_bounds j).1
  have hs : sqrt (j:ℝ) ≤ (j:ℝ)+1 := by
    apply (sqrt_le_iff).mpr
    refine ⟨by positivity,?_⟩
    have := Nat.cast_nonneg (α:=ℝ) j
    nlinarith [sq_nonneg (j:ℝ)]
  dsimp [sparseIndex]
  push_cast
  have := Nat.cast_nonneg (α:=ℝ) j
  nlinarith [sq_nonneg (j:ℝ)]

theorem sparseIndex_inside {j l : ℕ} (hj : 64 ≤ j)
    (hl : sqrt (j:ℝ) ≤ (l:ℝ)-j) : sparseIndex j+1 < l := by
  have hjr : (64:ℝ) ≤ j := by exact_mod_cast hj
  have hs : (8:ℝ) ≤ sqrt (j:ℝ) := by
    apply (le_sqrt (by norm_num) (by positivity)).mpr
    norm_num
    exact hj
  have hb := (sparseOffset_bounds j).1
  have he : (sparseIndex j+1:ℝ) < l := by
    dsimp [sparseIndex]
    push_cast
    linarith
  exact_mod_cast he

theorem sparseBudget_bounds {τ : ℝ} (hτ : 0 < τ) (hτ1 : τ ≤ 1) (j : ℕ) :
    (16:ℝ)^(sparseIndex j)/τ^2 ≤ sparseBudget τ j ∧
    (sparseBudget τ j:ℝ) ≤ 2*((16:ℝ)^(sparseIndex j)/τ^2) := by
  have hpow : (1:ℝ) ≤ 16^(sparseIndex j) := one_le_pow₀ (by norm_num)
  have ht : τ^2 ≤ 1 := by nlinarith
  have hbase : (1:ℝ) ≤ 16^(sparseIndex j)/τ^2 := by
    apply (le_div_iff₀ (sq_pos_of_pos hτ)).mpr
    simpa using ht.trans hpow
  refine ⟨Nat.le_ceil _,?_⟩
  have hu := Nat.ceil_lt_add_one (show 0 ≤ (16:ℝ)^(sparseIndex j)/τ^2 by positivity)
  change (sparseBudget τ j:ℝ) < _ at hu
  linarith

theorem sparseBudget_tendsto {τ : ℝ} (hτ : 0 < τ) :
    Tendsto (sparseBudget τ) atTop atTop := by
  apply (tendsto_natCast_atTop_iff (R := ℝ)).mp
  have hp : Tendsto (fun j : ℕ => (16:ℝ)^j/τ^2) atTop atTop :=
    (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1:ℝ) < 16)).atTop_div_const
      (sq_pos_of_pos hτ)
  apply tendsto_atTop_mono _ hp
  intro j
  calc
    (16:ℝ)^j/τ^2 ≤ (16:ℝ)^(sparseIndex j)/τ^2 :=
      div_le_div_of_nonneg_right (pow_le_pow_right₀ (by norm_num) (Nat.le_add_right _ _))
        (sq_nonneg τ)
    _ ≤ sparseBudget τ j := Nat.le_ceil _

theorem sparseBudget_inflation {δ τ : ℝ} (hτ : 0 < τ) (hτ1 : τ ≤ 1) :
    ∀ᶠ j : ℕ in atTop, 0 < budgetInflation δ (sparseBudget τ j) ∧
      budgetInflation δ (sparseBudget τ j) ≤ 3*((j:ℝ)+1) := by
  have hu := geometric_inflation_eventually δ (2/τ^2) (by positivity)
    sparseIndex (sparseBudget τ)
    (Filter.Eventually.of_forall sparseIndex_polynomial) (sparseBudget_tendsto hτ)
    (fun j => by
      have hh := (sparseBudget_bounds hτ hτ1 j).2
      have hn : (1:ℝ) ≤ (j:ℝ)+2 := by have := Nat.cast_nonneg (α:=ℝ) j; linarith
      have hp := mul_le_mul_of_nonneg_left hn
        (show 0 ≤ 2*((16:ℝ)^(sparseIndex j)/τ^2) by positivity)
      calc
        (sparseBudget τ j:ℝ) ≤ 2*((16:ℝ)^(sparseIndex j)/τ^2) := hh
        _ ≤ 2*((16:ℝ)^(sparseIndex j)/τ^2)*((j:ℝ)+2) := by simpa only [mul_one] using hp
        _ = _ := by ring)
  filter_upwards [hu,budgetInflation_eventually_pos δ _ (sparseBudget_tendsto hτ)] with j hj hp
  refine ⟨hp,hj.trans ?_⟩
  have hl := log_le_sub_one_of_pos (by positivity : 0 < (j:ℝ)+2)
  linarith

end ThresholdHC.AnytimeLower
