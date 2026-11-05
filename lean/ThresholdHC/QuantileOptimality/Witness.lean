import ThresholdHC.QuantileOptimality.QuantileLower
import ThresholdHC.QuantileOptimality.Limit

noncomputable section
open MeasureTheory Real Set
open scoped ENNReal BigOperators
namespace ThresholdHC.QuantileOptimality
open ThresholdHC.Tier6 (Gap)
open ThresholdHC.EntropyTailQuantile ThresholdHC.OptimalQuantile

theorem finite_law_witness {m : ℕ} (x : Option (Fin m) → ℝ) (hx : ∀ i, 0 ≤ x i)
    {k : ℝ} (hk : 0 ≤ k)
    (hprice : k*(sqrt (1+x none)+dyadicCost m x) < 1+sqrt (costEntropy x)) :
    ∃ (μ : Measure Gap) (_ : IsProbabilityMeasure μ),
      μ.support.Finite ∧ ∃ ρ B : ℝ, 0 < ρ ∧ ρ ≤ 1/4 ∧ 0 < B ∧
        ENNReal.ofReal k*ThresholdHC.EntropyTail.selection μ ρ B < closedQuantileValue μ ρ B := by
  obtain ⟨N,hN⟩ := exists_finite_price_witness x hprice
  let n := m+N+2
  have hn : m+2 ≤ n := by dsimp [n]; omega
  let η := bandEdge N
  have hη : 0 < η := bandEdge_pos N
  have hη1 : η ≤ 1 := by
    have h := bandEdge_antitone (Nat.zero_le N)
    norm_num [bandEdge] at h
    change bandEdge N ≤ 1
    unfold bandEdge
    linarith
  let ρ := chosenRarity m x
  have hρ : 0 < ρ := chosenRarity_pos hx
  let C := 1+sqrt (costEntropy x)
  have hC : 0 < C := by dsimp [C]; positivity
  have hC1 : 1 ≤ C := by dsimp [C]; linarith [sqrt_nonneg (costEntropy x)]
  let α := 1/(2*C)
  have hα : 0 < α := by dsimp [α]; positivity
  have hα1 : α ≤ 1 := by
    apply (div_le_one (show 0 < 2*C by positivity)).mpr
    linarith
  have hαC : α*C=1/2 := by dsimp [α]; field_simp
  let h := α*bandEdge n
  have hh : 0 < h := mul_pos hα (bandEdge_pos n)
  have hsmall : h ≤ bandEdge n := by
    have hm := mul_le_mul_of_nonneg_right hα1 (bandEdge_pos n).le
    simpa only [one_mul] using hm
  have hT : h*ρ/bandEdge n=α*ρ := by dsimp [h]; field_simp [(bandEdge_pos n).ne']
  have hclip : (h*ρ/bandEdge n)*C ≤ ρ := by
    rw [hT]
    have he : (α*ρ)*C=ρ/2 := by
      calc
        _ = ρ*(α*C) := by ring
        _ = ρ/2 := by rw [hαC]; ring
    rw [he]
    linarith only [hρ]
  let P := sqrt (finiteEnvelope ρ (1+x none) (bandEdge n))+(1+η)*dyadicCost m x
  have hP : 0 ≤ P := by
    have hc : 0 ≤ dyadicCost m x :=
      Finset.sum_nonneg (fun j _ => mul_nonneg (by positivity) (hx (some j)))
    exact add_nonneg (sqrt_nonneg _) (mul_nonneg (by linarith) hc)
  change k*P<C at hN
  let μ := realizingLaw hn x η hη hη1
  let B := h⁻¹^2
  have hK := selection_bound_explicit_budget hn hx hη hη1 hh hsmall
  have hQ := quantile_lower_explicit_budget hn hx hη hη1 hh hsmall hclip
  rw [hT] at hK hQ
  change ThresholdHC.EntropyTail.selection μ ρ B ≤ ENNReal.ofReal ((α*ρ)*P) at hK
  change ENNReal.ofReal ((α*ρ)*C) ≤ closedQuantileValue μ ρ B at hQ
  have hlt : k*((α*ρ)*P) < (α*ρ)*C := by
    have ht := mul_lt_mul_of_pos_left hN (mul_pos hα hρ)
    nlinarith only [ht]
  have hreal : ENNReal.ofReal (k*((α*ρ)*P)) < ENNReal.ofReal ((α*ρ)*C) :=
    (ENNReal.ofReal_lt_ofReal_iff_of_nonneg (mul_nonneg hk
      (mul_nonneg (mul_nonneg hα.le hρ.le) hP))).mpr hlt
  refine ⟨μ,realizingLaw_probability hn hx hη hη1,realizingLaw_support_finite hn x hη hη1,
    ρ,B,hρ,chosenRarity_le_quarter hx,sq_pos_of_pos (inv_pos.mpr hh),?_⟩
  calc
    _ ≤ ENNReal.ofReal k*ENNReal.ofReal ((α*ρ)*P) := mul_le_mul' le_rfl hK
    _ = ENNReal.ofReal (k*((α*ρ)*P)) := (ENNReal.ofReal_mul hk).symm
    _ < ENNReal.ofReal ((α*ρ)*C) := hreal
    _ ≤ _ := hQ

end ThresholdHC.QuantileOptimality
