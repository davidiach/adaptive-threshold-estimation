import ThresholdHC.FiniteQuantile.Filter
import ThresholdHC.FiniteQuantile.CoreValue
import ThresholdHC.FiniteQuantile.FilteredPacking
import ThresholdHC.EntropyTailLower.OptimalRetained

/-! The dyadic prefix through the quantile band includes the whole quantile
core. Using the whole boundary band can only increase its cost. -/
noncomputable section
open MeasureTheory Real
open scoped BigOperators ENNReal
namespace ThresholdHC.FiniteQuantile
open ThresholdHC.Tier6 ThresholdHC.StoppingProgram ThresholdHC.EntropyTailQuantile
open ThresholdHC.EntropyTailLower

theorem filtered_prefix_certificate {n N : ℕ} (μ : Measure Gap) [IsProbabilityMeasure μ]
    {ρ B t : ℝ} (hρ : 0 < ρ) (hB : 0 < B) (ht : 0 < t)
    (hbefore : ∀ j < n, t ≤ bandEdge j) (hN : 0 < N)
    (C : Certificate N) (hC : Feasible μ ρ B C)
    (hlarge : 262144 < prefixCoreEntropy μ n)
    (hcut : 32*(65536*(sqrt ρ/sqrt (prefixCoreEntropy μ n))) ≤ t) :
    min ρ (sqrt (ρ*prefixCoreEntropy μ n/B)) ≤
      256*(256*C.bias + sqrt ((4294967296*exp 48)*C.variance)) := by
  classical
  let w := fun i : Fin n => μ.real (EntropyTail.band i.val)
  let b := fun i : Fin n => bandEdge i.val
  let a := fun i => w i/(b i)^2
  let F := costEntropy a
  let A := costTotal a
  let lam := 65536*(sqrt ρ/sqrt F)
  have hw (i) : 0 ≤ w i := measureReal_nonneg
  have hb (i) : 0 < b i := bandEdge_pos _
  have ha (i) : 0 ≤ a i := div_nonneg (hw i) (sq_nonneg _)
  change 262144 < F at hlarge
  have hF : 0 < F := by linarith only [hlarge]
  let bad := fun i : Fin n => discardedBand (a i) (b i) A lam
  let S := Finset.univ.filter (fun i => ¬bad i)
  let X := maskedCost a S
  have hX := maskedCost_nonneg a ha S
  have hbad := discarded_entropy a ha ht (lam := lam)
    (by dsimp [lam]; positivity) hcut hbefore
  change costEntropy (fun i => if bad i then a i else 0) ≤ A/8 at hbad
  have hx : (fun i => if bad i then 0 else a i) = X := by
    funext i
    by_cases h : bad i <;> simp [X, maskedCost, S, h]
  have hfirst := costEntropy_bipartition a ha bad
  rw [hx] at hfirst
  have hAF : A ≤ F := costTotal_le_costEntropy ha
  have hkeep : F ≤ F/4 + 2*costEntropy X := by linarith only [hfirst,hbad,hAF]
  let p := fun i : Fin n => i ∈ S ∧ ¬i.val < 6 ∧ 0 < w i
  let Y := fun i => if p i then a i else 0
  let G := costEntropy Y
  have heLow : (fun i : Fin n => if i.val < 6 then 0 else X i) = Y := by
    funext i
    by_cases hwpos : 0 < w i
    · by_cases hiS : i ∈ S <;> by_cases hi6 : i.val < 6 <;>
        simp [X,maskedCost,Y,p,hiS,hi6,hwpos]
    · have hz : w i = 0 := le_antisymm (le_of_not_gt hwpos) (hw i)
      by_cases hiS : i ∈ S <;> by_cases hi6 : i.val < 6 <;>
        simp [X,maskedCost,Y,p,a,hiS,hi6,hz]
  have hpart := costEntropy_bipartition X hX (fun i => i.val < 6)
  rw [heLow] at hpart
  have hhigh := canonical_high_mask_entropy_bound μ S
  simp only [one_div] at hhigh
  change costEntropy (fun i : Fin n => if i.val < 6 then X i else 0) ≤ 16384 at hhigh
  have hcapture : F ≤ 16*G := by
    change costEntropy X ≤ 2*costEntropy (fun i : Fin n => if i.val < 6 then X i else 0)+2*G at hpart
    nlinarith only [hkeep,hpart,hhigh,hlarge]
  have hG : 0 < G := by nlinarith only [hcapture,hF]
  have hsome : ∃ i, p i := by
    by_contra hnone
    have hpnone := not_exists.mp hnone
    have hz : G = 0 := by simp [G,Y,hpnone]
    exact (ne_of_gt hG) hz
  obtain ⟨i0,hi0⟩ := hsome
  let I := {i : Fin n // p i}
  let : Nonempty I := ⟨⟨i0,hi0⟩⟩
  have hGsub : costEntropy (fun i : I => a i) = G :=
    (costEntropy_indicator_eq_subtype p a).symm
  have hAsub : costTotal (fun i : I => a i) ≤ A :=
    costTotal_comp_injective_le a ha Subtype.val Subtype.val_injective
  have hj : StrictMono (fun i : I => i.val.val) := fun _ _ h => h
  have hgap (i : I) : lam*(1+log (A/a i.val)) ≤ 2*b i.val := by
    have hnot := (Finset.mem_filter.mp i.property.1).2
    exact le_of_not_gt (fun h => hnot ⟨div_pos i.property.2.2 (sq_pos_of_pos (hb _)), h⟩)
  have hpack := filtered_core_certificate_bound μ ρ B F A hρ hB hF hN C hC
    (fun i : I => i.val.val) hj
  simp only [one_div] at hpack
  apply hpack
  · intro i
    have hh := i.property.2.1
    omega
  · exact fun i => i.property.2.2
  · exact hAsub
  · change F ≤ 16*costEntropy (fun i : I => a i.val)
    rw [hGsub]
    exact hcapture
  · exact hgap

end ThresholdHC.FiniteQuantile
