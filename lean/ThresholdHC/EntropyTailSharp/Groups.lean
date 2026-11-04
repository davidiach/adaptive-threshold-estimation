import ThresholdHC.EntropyTailSharp.Certificate
import ThresholdHC.EntropyTailLower.CanonicalGroups

/-! Localize the improved variance price with the actual conditional band masses and work budgets. -/
noncomputable section
open MeasureTheory Set Real
open scoped BigOperators ENNReal
namespace ThresholdHC.EntropyTailSharp
open ThresholdHC.EntropyTailLower
open ThresholdHC.Tier6 ThresholdHC.StoppingProgram ThresholdHC.CriticalEntropy ThresholdHC.EntropyTailQuantile

theorem certificate_localized_annular_bound_sharp {T : Type} [Fintype T] {N : ℕ}
    (μ : Measure Gap) [IsProbabilityMeasure μ] (ρ B : ℝ) (hB : 0 < B) (hN : 0 < N)
    (C : Certificate N) (hC : Feasible μ ρ B C)
    (S : T → Set Gap) (hS : ∀ i, MeasurableSet (S i))
    (hd : Pairwise (fun i j => Disjoint (S i) (S j))) (hm : ∀ i, μ (S i) ≠ 0)
    (r : T → ℝ) (hr : ∀ i, 0 < r i) (hr4 : ∀ i, r i ≤ 1/4)
    (hρ : ∑ i, μ.real (S i)*r i ≤ ρ)
    (ν : T → Measure EntropyGap) [∀ i, IsProbabilityMeasure (ν i)]
    (hν : ∀ i, (ν i).map entropyGapInclusion = ProbabilityTheory.cond μ (S i))
    (a : T → ℝ) (ha : ∀ i, 0 < a i) (ha4 : ∀ i, a i ≤ 1/4)
    (hclose : ∀ i, ∀ᵐ (d : EntropyGap) ∂ν i, (d:ℝ) ≤ a i)
    (K : T → ℕ) (J : (i : T) → Fin (K i) → Set EntropyGap)
    (b : (i : T) → Fin (K i) → ℝ)
    (hb : ∀ i j, 0 < b i j) (hJ : ∀ i j, MeasurableSet (J i j))
    (hdis : ∀ i, Pairwise (fun j k => Disjoint (J i j) (J i k)))
    (hband : ∀ i j d, d ∈ J i j → b i j/2 < (d:ℝ) ∧ (d:ℝ) ≤ b i j)
    (hsep : ∀ i j k, k.val = j.val+1 → 4*b i k ≤ b i j)
    (s : T → ℝ) (hs1 : ∀ i, s i ≤ 1) (hmass : ∀ i j, s i ≤ (ν i).real (J i j))
    (u : T → ℝ) (hu : ∀ i, 0 ≤ u i) (hcap : ∀ i, u i ≤ μ.real (S i)*r i)
    (hcost : ∀ i, (u i)^2*B ≤ (μ.real (S i))^2 *
      min (s i/(a i)^2) (r i*ThresholdHC.EntropyTailQuantile.costEntropy
        (fun j => (ν i).real (J i j)/(b i j)^2))) :
    ∑ i, u i ≤ 256*C.bias + sqrt ((16384*exp 48)*C.variance) := by
  obtain ⟨D,w,hD,he,hv,hw⟩ := certificate_component_localization μ ρ B C hC
    S hS hd hm r (fun i => (hr i).le) hρ
  have ht (i) : 0 < μ.real (S i) := ENNReal.toReal_pos (hm i) (measure_ne_top μ (S i))
  have hg (i) (hsmall : μ.real (S i)*(D i).bias ≤ (μ.real (S i)*r i)/128) :
      (u i)^2*B ≤ (16384*exp 48)*(μ.real (S i)*(D i).variance)*(μ.real (S i)*w i) := by
    have hbias : (D i).bias ≤ r i/128 := by
      have heq : (μ.real (S i)*r i)/128 = μ.real (S i)*(r i/128) := by ring
      rw [heq] at hsmall
      exact (mul_le_mul_iff_right₀ (ht i)).mp hsmall
    have hfeas : Feasible ((ν i).map entropyGapInclusion) (r i) (w i) (D i) := by
      rw [hν i]
      exact (hD i).2.2
    have hl := certificate_gated_annular_saturation_sharp (ν i) (r i) (w i)
      (hr i) (hr4 i) hN (D i) hfeas hbias (a i) (ha i) (ha4 i) (hclose i)
      (J i) (b i) (hb i) (hJ i) (hdis i) (hband i) (hsep i) (s i) (hs1 i) (hmass i)
    have hh := (hcost i).trans (mul_le_mul_of_nonneg_left hl (sq_nonneg (μ.real (S i))))
    convert hh using 1; ring
  have h := finite_component_obstructions u
    (fun i => μ.real (S i)*(D i).bias) (fun i => μ.real (S i)*(D i).variance)
    (fun i => μ.real (S i)*w i) (fun i => μ.real (S i)*r i)
    B C.variance (2*C.bias) (16384*exp 48) 128 hu
    (fun i => mul_nonneg (ht i).le (hD i).2.2.bias_nonneg)
    (fun i => mul_nonneg (ht i).le (hD i).2.2.variance_nonneg)
    (fun i => mul_nonneg (ht i).le (hD i).2.1) hB (by positivity) (by norm_num)
    he hv hw (fun i _ => hcap i) hg
  convert h using 1; ring

theorem certificate_canonical_group_bound_sharp {T : Type} [Fintype T] {N : ℕ}
    (μ : Measure Gap) [IsProbabilityMeasure μ] (ρ B : ℝ) (hB : 0 < B) (hN : 0 < N)
    (C : Certificate N) (hC : Feasible μ ρ B C)
    (K : T → ℕ) (j : (i : T) → Fin (K i) → ℕ)
    (hj : ∀ i, Function.Injective (j i))
    (hcross : ∀ i l, i ≠ l → ∀ k m, j i k ≠ j l m)
    (hm : ∀ i, μ (canonicalGroup (j i)) ≠ 0)
    (a : T → ℝ) (ha : ∀ i, 0 < a i) (hasmall : ∀ i, a i ≤ 1/128)
    (hmax : ∀ i k, (1/2:ℝ)^(j i k+1) ≤ a i)
    (hsep : ∀ i k l, l.val = k.val+1 → 4*((1/2:ℝ)^(j i l+1)) ≤ (1/2:ℝ)^(j i k+1))
    (θ s u : T → ℝ) (hθ : ∀ i, 0 < θ i)
    (hθcap : ∀ i, θ i ≤ μ.real (canonicalGroup (j i))/4)
    (hρ : (∑ i, θ i) ≤ ρ)
    (hsτ : ∀ i, s i ≤ μ.real (canonicalGroup (j i)))
    (hs : ∀ i k, s i ≤ μ.real (ThresholdHC.EntropyTail.band (j i k)))
    (hu : ∀ i, 0 ≤ u i) (hucap : ∀ i, u i ≤ θ i)
    (hcost : ∀ i, (u i)^2*B ≤
      min (μ.real (canonicalGroup (j i))*s i/(a i)^2)
        (θ i*costEntropy (fun k => μ.real (ThresholdHC.EntropyTail.band (j i k))/((1/2:ℝ)^(j i k+1))^2))) :
    (∑ i, u i) ≤ 256*C.bias+sqrt ((16384*exp 48)*C.variance) := by
  let S := fun i => canonicalGroup (j i)
  let τ := fun i => μ.real (S i)
  have hτ (i) : 0 < τ i := ENNReal.toReal_pos (hm i) (measure_ne_top μ (S i))
  have hS (i) : MeasurableSet (S i) := canonicalGroup_measurable (j i)
  let r := fun i => θ i/τ i
  have hr (i) : 0 < r i := div_pos (hθ i) (hτ i)
  have hr4 (i) : r i ≤ 1/4 := (div_le_iff₀ (hτ i)).mpr (by
    change θ i ≤ (1/4:ℝ)*τ i
    have h := hθcap i
    change θ i ≤ τ i/4 at h
    linarith)
  have hmass : (∑ i, μ.real (S i)*r i) ≤ ρ := by
    have he (i) : μ.real (S i)*r i = θ i := by
        change τ i*(θ i/τ i) = θ i
        calc
          _ = θ i*(τ i/τ i) := by ring
          _ = θ i := by rw [div_self (hτ i).ne',mul_one]
    simpa only [he] using hρ
  let m := fun i => ProbabilityTheory.cond μ (S i)
  let (i : T) : IsProbabilityMeasure (m i) := ProbabilityTheory.cond_isProbabilityMeasure (hm i)
  have hclose (i) : ∀ᵐ (d : Gap) ∂m i, (d:ℝ) ≤ a i := by
    apply ProbabilityTheory.ae_cond_of_forall_mem (hS i)
    intro d hd
    rcases Set.mem_iUnion.mp hd with ⟨k,hk⟩
    exact hk.2.trans (hmax i k)
  have hsmall (i) : ∀ᵐ (d : Gap) ∂m i, (d:ℝ) ≤ 1/128 :=
    (hclose i).mono (fun _ h => h.trans (hasmall i))
  let ν := fun i => smallGapLaw (m i)
  let (i : T) : IsProbabilityMeasure (ν i) := smallGapLaw_probability (m i) (hsmall i)
  have hν (i) : (ν i).map entropyGapInclusion = m i := smallGapLaw_map (m i) (hsmall i)
  have hclose' (i) : ∀ᵐ (d : EntropyGap) ∂ν i, (d:ℝ) ≤ a i := by
    have h := hclose i
    rw [← hν i] at h
    exact entropyGapInclusion_measurableEmbedding.ae_map_iff.mp h
  let J := fun i k => entropyGapInclusion ⁻¹' ThresholdHC.EntropyTail.band (j i k)
  let b := fun i k => (1/2:ℝ)^(j i k+1)
  have hJ (i k) : MeasurableSet (J i k) :=
    (ThresholdHC.EntropyTail.measurableSet_band (j i k)).preimage
      entropyGapInclusion_measurableEmbedding.measurable
  have hband (i k) (d : EntropyGap) (hd : d ∈ J i k) : b i k/2 < (d:ℝ) ∧ (d:ℝ) ≤ b i k := by
    change (1/2:ℝ)^(j i k+2) < (d:ℝ) ∧ (d:ℝ) ≤ (1/2:ℝ)^(j i k+1) at hd
    have he : b i k/2 = (1/2:ℝ)^(j i k+2) := by
      dsimp [b]
      rw [show j i k+2 = (j i k+1)+1 by omega,pow_succ]
      ring
    exact ⟨by rw [he]; exact hd.1,hd.2⟩
  have hbandmass (i k) : (ν i).real (J i k) = μ.real (ThresholdHC.EntropyTail.band (j i k))/τ i := by
    have he : ν i (J i k) = m i (ThresholdHC.EntropyTail.band (j i k)) := by
      rw [← hν i,Measure.map_apply entropyGapInclusion_measurableEmbedding.measurable
        (ThresholdHC.EntropyTail.measurableSet_band (j i k))]
    have he' := congrArg ENNReal.toReal he
    exact he'.trans (canonicalGroup_cond_band_real μ (j i) k)
  have hgamma (i) : costEntropy (fun k => (ν i).real (J i k)/(b i k)^2) =
      (1/τ i)*costEntropy (fun k => μ.real (ThresholdHC.EntropyTail.band (j i k))/(b i k)^2) := by
    simp_rw [hbandmass]
    exact normalized_cost_entropy _ _ _
  have hcost' (i) : (u i)^2*B ≤ (μ.real (S i))^2 *
      min ((s i/τ i)/(a i)^2) (r i*costEntropy (fun k => (ν i).real (J i k)/(b i k)^2)) := by
    rw [hgamma]
    change (u i)^2*B ≤ (τ i)^2 * min ((s i/τ i)/(a i)^2)
      ((θ i/τ i)*((1/τ i)*costEntropy (fun k => μ.real (ThresholdHC.EntropyTail.band (j i k))/(b i k)^2)))
    rw [normalized_annular_cost _ _ _ _ _ (hτ i) (ha i)]
    exact hcost i
  apply certificate_localized_annular_bound_sharp μ ρ B hB hN C hC S hS
    (fun i l hil => canonicalGroup_disjoint (j i) (j l) (hcross i l hil)) hm
    r hr hr4 hmass ν hν a ha (fun i => by have := hasmall i; linarith) hclose' K J b
    (fun _ _ => by dsimp [b]; positivity) hJ
    (fun i k l hkl => (ThresholdHC.EntropyTail.band_disjoint (fun he => hkl (hj i he))).preimage entropyGapInclusion)
    hband hsep (fun i => s i/τ i)
    (fun i => (div_le_one (hτ i)).mpr (hsτ i))
    (fun i k => by rw [hbandmass]; exact div_le_div_of_nonneg_right (hs i k) (hτ i).le)
    u hu
    (fun i => by
      have he : μ.real (S i)*r i = θ i := by
        change τ i*(θ i/τ i) = θ i
        calc
          _ = θ i*(τ i/τ i) := by ring
          _ = θ i := by rw [div_self (hτ i).ne',mul_one]
      rw [he]
      exact hucap i)
    hcost'

end ThresholdHC.EntropyTailSharp
