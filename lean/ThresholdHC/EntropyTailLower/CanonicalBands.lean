import ThresholdHC.EntropyTailLower.LocalizedAnnular
import ThresholdHC.EntropyTail.Band

noncomputable section
namespace ThresholdHC.EntropyTailLower
open MeasureTheory Real
open scoped BigOperators ENNReal
open ThresholdHC.Tier6 ThresholdHC.StoppingProgram ThresholdHC.CriticalEntropy

theorem entropyGapInclusion_range : Set.range entropyGapInclusion = {d : Gap | (d:ℝ) ≤ 1/128} := by
  ext d
  constructor
  · rintro ⟨x,rfl⟩
    exact x.property.2
  · intro hd
    refine ⟨⟨(d:ℝ),d.property.1,hd⟩,?_⟩
    exact Subtype.ext rfl

def smallGapLaw (μ : Measure Gap) : Measure EntropyGap := μ.comap entropyGapInclusion

theorem smallGapLaw_map (μ : Measure Gap) (hμ : ∀ᵐ (d : Gap) ∂μ, (d:ℝ) ≤ 1/128) :
    (smallGapLaw μ).map entropyGapInclusion = μ := by
  rw [smallGapLaw,entropyGapInclusion_measurableEmbedding.map_comap,entropyGapInclusion_range]
  exact Measure.restrict_eq_self_of_ae_mem hμ

theorem smallGapLaw_probability (μ : Measure Gap) [IsProbabilityMeasure μ]
    (hμ : ∀ᵐ (d : Gap) ∂μ, (d:ℝ) ≤ 1/128) : IsProbabilityMeasure (smallGapLaw μ) := by
  apply (Measure.isProbabilityMeasure_map_iff entropyGapInclusion_measurableEmbedding.measurable.aemeasurable).mp
  rw [smallGapLaw_map μ hμ]
  infer_instance

theorem certificate_canonical_band_allocation {T : Type} [Fintype T] {N : ℕ}
    (μ : Measure Gap) [IsProbabilityMeasure μ] (ρ B : ℝ) (hB : 0 < B) (hN : 0 < N)
    (C : Certificate N) (hC : Feasible μ ρ B C)
    (j : T → ℕ) (hj : Function.Injective j) (hlow : ∀ i, 6 ≤ j i)
    (hm : ∀ i, μ (ThresholdHC.EntropyTail.band (j i)) ≠ 0)
    (r : T → ℝ) (hr : ∀ i, 0 < r i) (hr4 : ∀ i, r i ≤ 1/4)
    (hρ : ∑ i, μ.real (ThresholdHC.EntropyTail.band (j i))*r i ≤ ρ) :
    (∑ i, μ.real (ThresholdHC.EntropyTail.band (j i))*
      min (r i) (sqrt (r i/(B*((1/2:ℝ)^(j i+1))^2)))) ≤
      256*C.bias + sqrt ((4294967296*exp 48)*C.variance) := by
  let S := fun i => ThresholdHC.EntropyTail.band (j i)
  let b := fun i => (1/2:ℝ)^(j i+1)
  have hS (i) : MeasurableSet (S i) := ThresholdHC.EntropyTail.measurableSet_band (j i)
  have hb (i) : 0 < b i := by dsimp [b]; positivity
  have hbsmall (i) : b i ≤ 1/128 := by
    have hh := pow_le_pow_of_le_one (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num : (1/2:ℝ) ≤ 1)
      (show 7 ≤ j i+1 by have := hlow i; omega)
    norm_num at hh
    exact hh
  let m := fun i => ProbabilityTheory.cond μ (S i)
  let (i : T) : IsProbabilityMeasure (m i) := ProbabilityTheory.cond_isProbabilityMeasure (hm i)
  have hband (i) : ∀ᵐ (d : Gap) ∂m i, b i/2 < (d:ℝ) ∧ (d:ℝ) ≤ b i := by
    apply ProbabilityTheory.ae_cond_of_forall_mem (hS i)
    intro d hd
    change (1/2:ℝ)^(j i+2) < (d:ℝ) ∧ (d:ℝ) ≤ (1/2:ℝ)^(j i+1) at hd
    have heq : b i/2 = (1/2:ℝ)^(j i+2) := by dsimp [b]; rw [show j i+2 = (j i+1)+1 by omega,pow_succ]; ring
    exact ⟨by rw [heq]; exact hd.1,hd.2⟩
  have hsmall (i) : ∀ᵐ (d : Gap) ∂m i, (d:ℝ) ≤ 1/128 := (hband i).mono (fun _ hh => hh.2.trans (hbsmall i))
  let ν := fun i => smallGapLaw (m i)
  let (i : T) : IsProbabilityMeasure (ν i) := smallGapLaw_probability (m i) (hsmall i)
  have hν (i) : (ν i).map entropyGapInclusion = m i := smallGapLaw_map (m i) (hsmall i)
  have hband' (i) : ∀ᵐ (d : EntropyGap) ∂ν i, b i/2 < (d:ℝ) ∧ (d:ℝ) ≤ b i := by
    have hh := hband i
    rw [← hν i] at hh
    exact entropyGapInclusion_measurableEmbedding.ae_map_iff.mp hh
  exact certificate_localized_single_band_bound μ ρ B hB hN C hC S hS
    (fun _ _ hne => ThresholdHC.EntropyTail.band_disjoint (fun he => hne (hj he))) hm
    r hr hr4 hρ ν hν b hb (fun i => by have := hbsmall i; linarith) hband'

end ThresholdHC.EntropyTailLower

namespace ThresholdHC.EntropyTailLower
open MeasureTheory Real
open scoped BigOperators ENNReal
open ThresholdHC.Tier6 ThresholdHC.StoppingProgram

theorem sum_subtype_eq_of_zero {T : Type} [Fintype T] (p : T → Prop)
    [DecidablePred p] (f : T → ℝ) (hf : ∀ i, ¬p i → f i = 0) :
    (∑ i : {i // p i}, f i) = ∑ i, f i := by
  have hh := Fintype.sum_subtype_add_sum_subtype p f
  have hz : (∑ i : {i // ¬p i}, f i) = 0 :=
    Finset.sum_eq_zero (fun i _ => hf i i.property)
  rwa [hz,add_zero] at hh

theorem certificate_canonical_band_allocation_nonneg {T : Type} [Fintype T] {N : ℕ}
    (μ : Measure Gap) [IsProbabilityMeasure μ] (ρ B : ℝ) (hB : 0 < B) (hN : 0 < N)
    (C : Certificate N) (hC : Feasible μ ρ B C)
    (j : T → ℕ) (hj : Function.Injective j) (hlow : ∀ i, 6 ≤ j i)
    (r : T → ℝ) (hr : ∀ i, 0 ≤ r i) (hr4 : ∀ i, r i ≤ 1/4)
    (hρ : ∑ i, μ.real (ThresholdHC.EntropyTail.band (j i))*r i ≤ ρ) :
    (∑ i, μ.real (ThresholdHC.EntropyTail.band (j i))*
      min (r i) (sqrt (r i/(B*((1/2:ℝ)^(j i+1))^2)))) ≤
      256*C.bias + sqrt ((4294967296*exp 48)*C.variance) := by
  classical
  let p := fun i => 0 < r i ∧ μ (ThresholdHC.EntropyTail.band (j i)) ≠ 0
  have hz (i : T) (hi : ¬p i) : r i = 0 ∨ μ (ThresholdHC.EntropyTail.band (j i)) = 0 := by
    by_cases hh : 0 < r i
    · exact Or.inr (by by_contra hn; exact hi ⟨hh,hn⟩)
    · exact Or.inl (le_antisymm (le_of_not_gt hh) (hr i))
  have hm : (∑ i : {i // p i}, μ.real (ThresholdHC.EntropyTail.band (j i))*r i) =
      ∑ i, μ.real (ThresholdHC.EntropyTail.band (j i))*r i := by
    apply sum_subtype_eq_of_zero p (fun i => μ.real (ThresholdHC.EntropyTail.band (j i))*r i)
    intro i hi
    rcases hz i hi with h | h <;> simp [h,Measure.real]
  have hc : (∑ i : {i // p i}, μ.real (ThresholdHC.EntropyTail.band (j i))*
      min (r i) (sqrt (r i/(B*((1/2:ℝ)^(j i+1))^2)))) =
      ∑ i, μ.real (ThresholdHC.EntropyTail.band (j i))*
      min (r i) (sqrt (r i/(B*((1/2:ℝ)^(j i+1))^2))) := by
    apply sum_subtype_eq_of_zero p (fun i => μ.real (ThresholdHC.EntropyTail.band (j i))*
      min (r i) (sqrt (r i/(B*((1/2:ℝ)^(j i+1))^2))))
    intro i hi
    rcases hz i hi with h | h <;> simp [h,Measure.real]
  have hh := certificate_canonical_band_allocation μ ρ B hB hN C hC
    (fun i : {i // p i} => j i) (fun _ _ he => Subtype.ext (hj he))
    (fun i => hlow i) (fun i => i.property.2)
    (fun i => r i) (fun i => i.property.1) (fun i => hr4 i)
    (by rw [hm]; exact hρ)
  rwa [hc] at hh

theorem allocation_min_linear (r t : ℝ) (hr : 0 ≤ r) (hr1 : r ≤ 1) (ht : 0 ≤ t) :
    r*min 1 t ≤ min r (t*sqrt r) := by
  have hs : r ≤ sqrt r := by
    nlinarith [sq_sqrt hr,sqrt_nonneg r]
  apply le_min
  · simpa using mul_le_mul_of_nonneg_left (min_le_left (1:ℝ) t) hr
  · calc
      _ ≤ r*t := mul_le_mul_of_nonneg_left (min_le_right (1:ℝ) t) hr
      _ ≤ t*sqrt r := by nlinarith only [mul_le_mul_of_nonneg_left hs ht]

theorem sqrt_allocation_cost (r B b : ℝ) (hr : 0 ≤ r) (hB : 0 < B) (hb : 0 < b) :
    sqrt (r/(B*b^2)) = (1/(sqrt B*b))*sqrt r := by
  rw [sqrt_div hr, sqrt_mul hB.le, sqrt_sq hb.le]
  ring

end ThresholdHC.EntropyTailLower
