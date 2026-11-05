import ThresholdHC.QuantileSharpLaw.Vertices
import ThresholdHC.QuantileSharpLaw.BoundaryPrice
import ThresholdHC.QuantileSharpLaw.CoreWeights
import ThresholdHC.QuantileSharpLaw.CoreIdentities
import ThresholdHC.OptimalQuantile.FiniteSharp

noncomputable section
open Real
open scoped BigOperators
namespace ThresholdHC.QuantileSharpLaw
open ThresholdHC.EntropyTailQuantile ThresholdHC.OptimalQuantile

theorem selected_boundary_price {n : ℕ} {v b : Option (Fin n) → ℝ}
    (hv : ∀ i, 0 ≤ v i) (hb : ∀ i, 0 ≤ b i) (hb0 : b none=0) :
    1+sqrt (costEntropy (fun i => v i+b i)) ≤
      scalarRoot*(sqrt (costEntropy (fun i => v i+boundaryUnit i))+fullCoreCost n b) := by
  let E := costEntropy v
  let x := bumpedCost E (fun i => b (some i)) 0
  have hE : 0 ≤ E := costEntropy_nonneg hv
  have hx : ∀ i, 0 ≤ x i := bumpedCost_nonneg hE (fun i => hb (some i)) 0
  have hN : costEntropy (fun i => v i+b i) ≤ costEntropy x := by
    have hi := costEntropy_add_interaction hv hb
    have hm := costInteraction_mono_left (costTotal_nonneg hv) (costTotal_le_costEntropy hv)
      (costTotal_nonneg hb)
    dsimp only [x]
    rw [compressed_entropy_identity E hb0]
    dsimp only [E]
    linarith only [hi,hm]
  have hraw : 1+sqrt (costEntropy x) ≤ scalarRoot*(sqrt (1+E)+dyadicCost n b) := by
    have h := scalarRoot_bounds_all_finite n x hx
    simpa only [x,bumpedCost,pow_two,zero_mul,add_zero,dyadicCost] using h
  have hc : fullCoreCost n b=dyadicCost n b := by simp only [fullCoreCost,hb0,zero_add]
  rw [hc]
  exact (add_le_add le_rfl (sqrt_le_sqrt hN)).trans (hraw.trans
    (mul_le_mul_of_nonneg_left (add_le_add (sqrt_le_sqrt (augmented_entropy_lower hv)) le_rfl)
      ((sqrt_nonneg 2).trans scalarRoot_spec.1.1)))

theorem skipped_boundary_price {n : ℕ} {v b : Option (Fin n) → ℝ}
    (hv : ∀ i, 0 ≤ v i) (hb : ∀ i, 0 ≤ b i) (hv0 : v none=0) :
    1+sqrt (costEntropy (fun i => v i+b i)) ≤
      scalarRoot*(sqrt (costEntropy (fun i => v i+boundaryUnit i))+fullCoreCost n b) := by
  have h := unselected_boundary_price (costTotal_nonneg hv) (costTotal_le_costEntropy hv)
    (costTotal_nonneg hb) (total_le_fullCoreCost hb) (costEntropy_le_twice_coreCost hb)
    (costEntropy_nonneg (fun i => add_nonneg (hv i) (hb i))) (costEntropy_add_interaction hv hb)
  have hbase : 1+sqrt (costEntropy (fun i => v i+b i)) ≤
      sqrt 2*(sqrt (costEntropy (fun i => v i+boundaryUnit i))+fullCoreCost n b) := by
    rw [augmented_entropy_zero_boundary hv0]
    simpa only [add_assoc] using h
  exact hbase.trans (mul_le_mul_of_nonneg_right scalarRoot_spec.1.1
    (add_nonneg (sqrt_nonneg _) ((costTotal_nonneg hb).trans (total_le_fullCoreCost hb))))

theorem core_vector_bound {n : ℕ} (v b : Option (Fin n) → ℝ)
    (hv : ∀ i, 0 ≤ v i) (hb : ∀ i, 0 ≤ b i) :
    1+sqrt (costEntropy (fun i => v i+b i)) ≤
      scalarRoot*(sqrt (costEntropy (fun i => v i+boundaryUnit i))+fullCoreCost n b) := by
  obtain ⟨z,d,hz,hd,hsum,hdisjoint,hprice⟩ :=
    exists_disjoint_core_split boundaryUnit coreWeight v b boundaryUnit_nonneg hv hb
  have hbound : 1+sqrt (costEntropy (fun i => z i+d i)) ≤
      scalarRoot*(sqrt (costEntropy (fun i => z i+boundaryUnit i))+fullCoreCost n d) := by
    rcases hdisjoint none with hzero | hzero
    · exact skipped_boundary_price hz hd hzero
    · exact selected_boundary_price hz hd hzero
  have he : (fun i => z i+d i) = (fun i => v i+b i) := funext hsum
  rw [he] at hbound
  rw [← fullCoreCost_eq_sum,← fullCoreCost_eq_sum] at hprice
  exact hbound.trans (mul_le_mul_of_nonneg_left hprice
    ((sqrt_nonneg 2).trans scalarRoot_spec.1.1))

end ThresholdHC.QuantileSharpLaw
