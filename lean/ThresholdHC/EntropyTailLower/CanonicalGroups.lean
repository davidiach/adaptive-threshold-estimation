import ThresholdHC.EntropyTailLower.CanonicalBands

noncomputable section
namespace ThresholdHC.EntropyTailLower
open MeasureTheory Real
open scoped BigOperators ENNReal
open ThresholdHC.Tier6 ThresholdHC.StoppingProgram ThresholdHC.CriticalEntropy
open ThresholdHC.EntropyTailQuantile

def canonicalGroup {K : ℕ} (j : Fin K → ℕ) : Set Gap :=
  ⋃ i, ThresholdHC.EntropyTail.band (j i)

theorem canonicalGroup_measurable {K : ℕ} (j : Fin K → ℕ) : MeasurableSet (canonicalGroup j) :=
  MeasurableSet.iUnion (fun i => ThresholdHC.EntropyTail.measurableSet_band (j i))

theorem band_subset_canonicalGroup {K : ℕ} (j : Fin K → ℕ) (i : Fin K) :
    ThresholdHC.EntropyTail.band (j i) ⊆ canonicalGroup j := Set.subset_iUnion (fun k => ThresholdHC.EntropyTail.band (j k)) i

theorem canonicalGroup_mass {K : ℕ} (μ : Measure Gap) [IsFiniteMeasure μ]
    (j : Fin K → ℕ) (hj : Function.Injective j) :
    μ.real (canonicalGroup j) = ∑ i, μ.real (ThresholdHC.EntropyTail.band (j i)) := by
  exact measureReal_iUnion_fintype
    (fun i k hik => ThresholdHC.EntropyTail.band_disjoint (fun h => hik (hj h)))
    (fun i => ThresholdHC.EntropyTail.measurableSet_band (j i))

theorem canonicalGroup_disjoint {K L : ℕ} (j : Fin K → ℕ) (k : Fin L → ℕ)
    (hjk : ∀ i l, j i ≠ k l) : Disjoint (canonicalGroup j) (canonicalGroup k) := by
  rw [Set.disjoint_left]
  intro d hd he
  rcases Set.mem_iUnion.mp hd with ⟨i,hi⟩
  rcases Set.mem_iUnion.mp he with ⟨l,hl⟩
  exact Set.disjoint_left.mp (ThresholdHC.EntropyTail.band_disjoint (hjk i l)) hi hl

theorem canonicalGroup_cond_band_real {K : ℕ} (μ : Measure Gap)
    (j : Fin K → ℕ) (i : Fin K) :
    (ProbabilityTheory.cond μ (canonicalGroup j)).real (ThresholdHC.EntropyTail.band (j i)) =
      μ.real (ThresholdHC.EntropyTail.band (j i))/μ.real (canonicalGroup j) := by
  rw [measureReal_def,ProbabilityTheory.cond_apply (canonicalGroup_measurable j),
    Set.inter_eq_right.mpr (band_subset_canonicalGroup j i),ENNReal.toReal_mul,ENNReal.toReal_inv]
  change (μ.real (canonicalGroup j))⁻¹*μ.real (ThresholdHC.EntropyTail.band (j i)) = _
  ring

theorem normalized_cost_entropy {I : Type} [Fintype I] (w b : I → ℝ) (τ : ℝ) :
    costEntropy (fun i => (w i/τ)/(b i)^2) = (1/τ)*costEntropy (fun i => w i/(b i)^2) := by
  have he : (fun i => (w i/τ)/(b i)^2) = (fun i => (1/τ)*(w i/(b i)^2)) := by
    funext i
    ring
  rw [he,costEntropy_smul]

theorem normalized_annular_cost (τ s a θ G : ℝ) (hτ : 0 < τ) (ha : 0 < a) :
    τ^2*min ((s/τ)/a^2) ((θ/τ)*((1/τ)*G)) = min (τ*s/a^2) (θ*G) := by
  rw [mul_min_of_nonneg _ _ (sq_nonneg τ)]
  congr 1 <;> field_simp [hτ.ne',ha.ne']

theorem certificate_canonical_group_bound {T : Type} [Fintype T] {N : ℕ}
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
    (∑ i, u i) ≤ 256*C.bias+sqrt ((4294967296*exp 48)*C.variance) := by
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
  apply certificate_localized_annular_bound μ ρ B hB hN C hC S hS
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

end ThresholdHC.EntropyTailLower
