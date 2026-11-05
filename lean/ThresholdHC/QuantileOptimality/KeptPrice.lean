import ThresholdHC.QuantileOptimality.CoreMeasure
import ThresholdHC.QuantileOptimality.PriceAlgebra
import ThresholdHC.QuantileSelection.MeasureEntropy

noncomputable section
open MeasureTheory Real Set
open scoped ENNReal BigOperators
namespace ThresholdHC.QuantileOptimality
open ThresholdHC.Tier6 (Gap)
open ThresholdHC.EntropyTailQuantile ThresholdHC.OptimalQuantile
open ThresholdHC.BandwiseSuffix (packet)

theorem keptMeasure_support_lower {m : ℕ} (n : ℕ) (x : Option (Fin m) → ℝ) (η : ℝ) :
    ∀ᵐ z : Gap ∂keptMeasure n x η, bandEdge n ≤ (z : ℝ) := by
  rw [keptMeasure,ae_add_measure_iff]
  refine ⟨packet_support_lower _ _,?_⟩
  exact (packet_support_lower (4*easyMass m x η) (edgeGap 0)).mono
    (fun z hz => (bandEdge_antitone (Nat.zero_le n)).trans hz)

theorem keptMeasure_entropy_bound {m : ℕ} (n : ℕ) {x : Option (Fin m) → ℝ}
    (hx : ∀ i, 0 ≤ x i) {η : ℝ} (hη : 0 ≤ η) (hη1 : η ≤ 1) :
    (measureCostEntropy (keptMeasure n x η)).toReal ≤
      inverseScale n x*finiteEnvelope (chosenRarity m x) (1+x none) (bandEdge n) := by
  have hA : 0 ≤ 1+x none := by linarith [hx none]
  have he := easyMass_bounds hx hη hη1
  have hV := packet_entropy_toReal_le (mul_nonneg (inverseScale_pos n hx).le hA) (edgeGap n)
  have hE := packet_entropy_toReal_le (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4)
    (show 0 ≤ easyMass m x η by linarith)) (edgeGap 0)
  have hE4 : (measureCostEntropy (easyAtom x η)).toReal ≤ 4 := by
    change (measureCostEntropy (easyAtom x η)).toReal ≤ 4*easyMass m x η at hE
    linarith only [hE,he.2]
  have hVs : ∀ᵐ z : Gap ∂boundaryAtom n x, bandEdge n ≤ (z : ℝ) := packet_support_lower _ _
  have hEs : ∀ᵐ z : Gap ∂easyAtom x η, bandEdge n ≤ (z : ℝ) :=
    (packet_support_lower (4*easyMass m x η) (edgeGap 0)).mono
      (fun z hz => (bandEdge_antitone (Nat.zero_le n)).trans hz)
  have h := ThresholdHC.QuantileSelection.core_interaction (boundaryAtom n x) (easyAtom x η)
    (bandEdge_pos n) hVs hEs
  rw [inverseScale,finiteEnvelope_scale (chosenRarity_pos hx) hA (bandEdge_pos n)]
  apply h.trans
  apply add_le_add (add_le_add hV hE4)
  apply sqrt_le_sqrt
  exact mul_le_mul (mul_le_mul_of_nonneg_left hV (by norm_num)) hE4 ENNReal.toReal_nonneg
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (mul_nonneg (inverseScale_pos n hx).le hA))

theorem realizingLaw_sub_kept {m n : ℕ} (hn : m+2 ≤ n) (x : Option (Fin m) → ℝ)
    {η : ℝ} (hη : 0 < η) (hη1 : η ≤ 1) :
    realizingLaw hn x η hη hη1-keptMeasure n x η=skippedAtoms hn x η hη hη1 := by
  have he : realizingLaw hn x η hη hη1=skippedAtoms hn x η hη hη1+keptMeasure n x η := by
    unfold realizingLaw keptMeasure
    abel
  rw [he,Measure.add_sub_cancel]

theorem skippedAtoms_tailModulus {m n : ℕ} (hn : m+2 ≤ n) {x : Option (Fin m) → ℝ}
    (hx : ∀ i, 0 ≤ x i) {η h : ℝ} (hη : 0 < η) (hη1 : η ≤ 1)
    (hh : 0 ≤ h) (hsmall : h ≤ bandEdge n) :
    tailModulus (skippedAtoms hn x η hη hη1) h =
      (h*chosenRarity m x/bandEdge n)*(1+η)*dyadicCost m x := by
  rw [skippedAtoms,tailModulus_finset_sum _ _ hh]
  have hterm (j : Fin m) :
      tailModulus (packet (inverseScale n x*x (some j)) (coreGap hn η hη hη1 j)) h =
        (h*chosenRarity m x/bandEdge n)*(1+η)*((2 : ℝ)^j.val*x (some j)) := by
    rw [packet_tailModulus_of_small (mul_nonneg (inverseScale_pos n hx).le (hx (some j))) _
      (hsmall.trans (coreGap_gt_edge hn hη hη1 j).le)]
    change (chosenRarity m x/(bandEdge n)^2*x (some j))*h*
      (bandEdge n*(2 : ℝ)^j.val*(1+η)) = _
    field_simp [(bandEdge_pos n).ne']
  simp only [hterm,dyadicCost,Finset.mul_sum]

end ThresholdHC.QuantileOptimality
