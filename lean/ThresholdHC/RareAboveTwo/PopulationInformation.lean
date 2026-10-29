import ThresholdHC.RareAboveTwo.GapDistance
import ThresholdHC.CriticalEntropy.CreationPopulation

noncomputable section
namespace ThresholdHC.RareAboveTwo
open ThresholdHC.Tier6
open MeasureTheory ThresholdHC.Proofs ThresholdHC.Proofs.Transcript ThresholdHC.CriticalEntropy

theorem gapMixture_zero_le_twice {m n : ℕ} (μ : Measure Gap) [IsProbabilityMeasure μ]
    (pol : List Bool → Option (Fin m)) (q : Fin m → ℝ) (hq : ∀ j, 0 ≤ q j ∧ q j ≤ 1)
    (i : Fin m) (hi : q i ≤ 1/2) (w : Fin n → Option Bool) :
    gapMixture μ pol (Function.update q i 0) w ≤ 2*gapMixture μ pol q w := by
  have he := gapMixture_mix_update μ pol q hq i (q i) w
  rw [Function.update_eq_self] at he
  rw [he]
  have hP := (gapMixture_total (n := n) μ pol _ (update_range q hq i 0 (by norm_num))).1 w
  have hQ := (gapMixture_total (n := n) μ pol _ (update_range q hq i 1 (by norm_num))).1 w
  unfold priorMix
  nlinarith only [mul_nonneg (by linarith : 0 ≤ 1-2*q i) hP,mul_nonneg (hq i).1 hQ]

theorem finite_population_rare_information {m n : ℕ} (μ : Measure Gap) [IsProbabilityMeasure μ]
    (pol : List Bool → Option (Fin m)) (a u v : ℝ) (ha : a ≤ 1/2)
    (hsupp : ∀ᵐ d : Gap ∂μ, (d : ℝ) ≤ a) (hu : 0 < u) (huv : u ≤ v) (hv : v ≤ 1/2) :
    (1-realFiniteAffinity (gapMixture (n := n) μ pol (fun _ => u))
      (gapMixture μ pol (fun _ => v)))*u ≤
      64*(v-u)^2*a^2*(∑ w : Fin n → Option Bool, gapMixture μ pol (fun _ => (u+v)/2) w*workOf w) := by
  classical
  let s : Fin m → ℝ := fun _ => (u+v)/2
  have hs (j) : 0 ≤ s j ∧ s j ≤ 1 := by dsimp [s]; constructor <;> linarith
  have hsh (j) : s j ≤ 1/2 := by dsimp [s]; linarith
  have hn (w : Fin n → Option Bool) : 0 ≤ gapMixture μ pol s w := (gapMixture_total μ pol s hs).1 w
  have hhyb := finite_population_hybrid_decomposition (n := n) μ pol (fun d : Gap => (d : ℝ))
    (fun _ => u) (fun _ => v) measurable_subtype_coe measurable_const measurable_const
    (fun d => ⟨d.property.1.le,d.property.2⟩) (fun _ => ⟨hu.le,by linarith⟩)
    (fun _ => ⟨by linarith,by linarith⟩)
  have he (t : ℝ) (i : Fin m) :
      (fun j : Fin m => if j=i then (fun _ : Gap => t) else fun _ => (u+v)/2) =
      fun j _ => Function.update s i t j := by
    funext j x
    by_cases h : j=i <;> simp [s,Function.update_apply,h]
  simp_rw [he] at hhyb
  change 1-realFiniteAffinity (gapMixture μ pol (fun _ => u)) (gapMixture μ pol (fun _ => v)) ≤
    ∑ i, (1-realFiniteAffinity (gapMixture μ pol (Function.update s i u)) (gapMixture μ pol (Function.update s i v))) at hhyb
  have hlocal (i : Fin m) :
      (1-realFiniteAffinity (gapMixture (n := n) μ pol (Function.update s i u))
        (gapMixture μ pol (Function.update s i v)))*u ≤
      64*(v-u)^2*a^2*(∑ w : Fin n → Option Bool, gapMixture μ pol s w*coinWork pol i w) := by
    have h := gap_rare_distance (n := n) μ pol s hs i a u v ha hsupp hu huv hv
    have hw := Finset.sum_le_sum (s := Finset.univ) (fun (w : Fin n → Option Bool) _ =>
      mul_le_mul_of_nonneg_right (gapMixture_zero_le_twice μ pol s hs i (hsh i) w) (coinWork_nonneg pol i w))
    have hh := mul_le_mul_of_nonneg_left hw (show 0 ≤ 32*(v-u)^2*a^2 by positivity)
    simp only [mul_assoc,← Finset.mul_sum] at hh
    nlinarith only [h,hh]
  calc
    _ ≤ (∑ i, (1-realFiniteAffinity (gapMixture (n := n) μ pol (Function.update s i u))
        (gapMixture μ pol (Function.update s i v))))*u := mul_le_mul_of_nonneg_right hhyb hu.le
    _ = ∑ i, (1-realFiniteAffinity (gapMixture (n := n) μ pol (Function.update s i u))
        (gapMixture μ pol (Function.update s i v)))*u := Finset.sum_mul _ _ _
    _ ≤ ∑ i, 64*(v-u)^2*a^2*(∑ w : Fin n → Option Bool, gapMixture μ pol s w*coinWork pol i w) :=
      Finset.sum_le_sum (fun i _ => hlocal i)
    _ = 64*(v-u)^2*a^2*(∑ w : Fin n → Option Bool, gapMixture μ pol s w*(∑ i, coinWork pol i w)) := by
      rw [← Finset.mul_sum,Finset.sum_comm]
      simp only [Finset.mul_sum]
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact Finset.sum_le_sum (fun w _ => mul_le_mul_of_nonneg_left (sum_coinWork_le_work pol w) (hn w))

theorem creation_rare_information {n : ℕ} (μ : Measure Gap) [IsProbabilityMeasure μ]
    (pol : List Bool → Option ℕ) (a u v : ℝ) (ha : a ≤ 1/2)
    (hsupp : ∀ᵐ d : Gap ∂μ, (d : ℝ) ≤ a) (hu : 0 < u) (huv : u ≤ v) (hv : v ≤ 1/2) :
    (1-realFiniteAffinity (creationPopulationWeight (n := n) μ pol (fun d => (d : ℝ)) (fun _ => u))
      (creationPopulationWeight μ pol (fun d => (d : ℝ)) (fun _ => v)))*u ≤
      64*(v-u)^2*a^2*(∑ w : Fin n → Option Bool,
        creationPopulationWeight μ pol (fun d => (d : ℝ)) (fun _ => (u+v)/2) w*workOf w) := by
  have he (t : ℝ) : creationPopulationWeight (n := n) μ pol (fun d => (d : ℝ)) (fun _ => t) =
      gapMixture μ (Tier5.capPolicy (Tier5.coinCap n pol) pol) (fun _ => t) := by
    funext w
    exact creationPopulationWeight_eq_finite μ pol _ _ measurable_subtype_coe measurable_const w
  rw [he,he,he]
  exact finite_population_rare_information μ _ a u v ha hsupp hu huv hv

end ThresholdHC.RareAboveTwo
