import ThresholdHC.EntropyTailLower.CertificateAnnular
import ThresholdHC.EntropyTailLower.ComponentLocalization
import ThresholdHC.EntropyTailLower.LocalizationAlgebra

noncomputable section
namespace ThresholdHC.EntropyTailLower
open MeasureTheory Real
open scoped BigOperators ENNReal
open ThresholdHC.Tier6 ThresholdHC.StoppingProgram ThresholdHC.CriticalEntropy

/-! The remaining deterministic selection problem must supply the disjoint
components, their rarity allocation, and the component cost bounds below.
The statistical component certificates and their joint budgets are derived. -/
theorem certificate_localized_annular_bound {T : Type} [Fintype T] {N : ℕ}
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
    ∑ i, u i ≤ 256*C.bias + sqrt ((4294967296*exp 48)*C.variance) := by
  obtain ⟨D,w,hD,he,hv,hw⟩ := certificate_component_localization μ ρ B C hC
    S hS hd hm r (fun i => (hr i).le) hρ
  have ht (i) : 0 < μ.real (S i) := ENNReal.toReal_pos (hm i) (measure_ne_top μ (S i))
  have hg (i) (hsmall : μ.real (S i)*(D i).bias ≤ (μ.real (S i)*r i)/128) :
      (u i)^2*B ≤ (4294967296*exp 48)*(μ.real (S i)*(D i).variance)*(μ.real (S i)*w i) := by
    have hbias : (D i).bias ≤ r i/128 := by
      have heq : (μ.real (S i)*r i)/128 = μ.real (S i)*(r i/128) := by ring
      rw [heq] at hsmall
      exact (mul_le_mul_iff_right₀ (ht i)).mp hsmall
    have hfeas : Feasible ((ν i).map entropyGapInclusion) (r i) (w i) (D i) := by
      rw [hν i]
      exact (hD i).2.2
    have hl := certificate_gated_annular_saturation (ν i) (r i) (w i)
      (hr i) (hr4 i) hN (D i) hfeas hbias (a i) (ha i) (ha4 i) (hclose i)
      (J i) (b i) (hb i) (hJ i) (hdis i) (hband i) (hsep i) (s i) (hs1 i) (hmass i)
    have hh := (hcost i).trans (mul_le_mul_of_nonneg_left hl (sq_nonneg (μ.real (S i))))
    convert hh using 1; ring
  have h := finite_component_obstructions u
    (fun i => μ.real (S i)*(D i).bias) (fun i => μ.real (S i)*(D i).variance)
    (fun i => μ.real (S i)*w i) (fun i => μ.real (S i)*r i)
    B C.variance (2*C.bias) (4294967296*exp 48) 128 hu
    (fun i => mul_nonneg (ht i).le (hD i).2.2.bias_nonneg)
    (fun i => mul_nonneg (ht i).le (hD i).2.2.variance_nonneg)
    (fun i => mul_nonneg (ht i).le (hD i).2.1) hB (by positivity) (by norm_num)
    he hv hw (fun i _ => hcap i) hg
  convert h using 1; ring

theorem certificate_localized_single_band_bound {T : Type} [Fintype T] {N : ℕ}
    (μ : Measure Gap) [IsProbabilityMeasure μ] (ρ B : ℝ) (hB : 0 < B) (hN : 0 < N)
    (C : Certificate N) (hC : Feasible μ ρ B C)
    (S : T → Set Gap) (hS : ∀ i, MeasurableSet (S i))
    (hd : Pairwise (fun i j => Disjoint (S i) (S j))) (hm : ∀ i, μ (S i) ≠ 0)
    (r : T → ℝ) (hr : ∀ i, 0 < r i) (hr4 : ∀ i, r i ≤ 1/4)
    (hρ : ∑ i, μ.real (S i)*r i ≤ ρ)
    (ν : T → Measure EntropyGap) [∀ i, IsProbabilityMeasure (ν i)]
    (hν : ∀ i, (ν i).map entropyGapInclusion = ProbabilityTheory.cond μ (S i))
    (b : T → ℝ) (hb : ∀ i, 0 < b i) (hb4 : ∀ i, b i ≤ 1/4)
    (hband : ∀ i, ∀ᵐ (d : EntropyGap) ∂ν i, b i/2 < (d:ℝ) ∧ (d:ℝ) ≤ b i) :
    (∑ i, μ.real (S i)*min (r i) (sqrt (r i/(B*(b i)^2)))) ≤
      256*C.bias + sqrt ((4294967296*exp 48)*C.variance) := by
  let J (i : T) (_ : Fin 1) : Set EntropyGap := {d | b i/2 < (d:ℝ) ∧ (d:ℝ) ≤ b i}
  have hJ (i : T) (j : Fin 1) : MeasurableSet (J i j) :=
    (measurableSet_lt measurable_const measurable_subtype_coe).inter
      (measurableSet_le measurable_subtype_coe measurable_const)
  have hmass (i : T) (j : Fin 1) : (ν i).real (J i j) = 1 := by
    have hh : ν i (J i j) = 1 := (mem_ae_iff_prob_eq_one (hJ i j)).mp (hband i)
    simp [measureReal_def,hh]
  have hgamma (i : T) : ThresholdHC.EntropyTailQuantile.costEntropy
      (fun j : Fin 1 => (ν i).real (J i j)/(b i)^2) = 1/(b i)^2 := by
    simp only [hmass,ThresholdHC.EntropyTailQuantile.costEntropy,ThresholdHC.EntropyTailQuantile.costTotal,
      Fin.sum_univ_one]
    ring
  have hmin (i : T) : min (1/(b i)^2) (r i*(1/(b i)^2)) = r i/(b i)^2 := by
    rw [min_eq_right]
    · ring
    · apply mul_le_of_le_one_left (by positivity)
      linarith [hr4 i]
  have hcost (i : T) : (μ.real (S i)*min (r i) (sqrt (r i/(B*(b i)^2))))^2*B ≤
      (μ.real (S i))^2 * min (1/(b i)^2) (r i*ThresholdHC.EntropyTailQuantile.costEntropy
        (fun j : Fin 1 => (ν i).real (J i j)/(b i)^2)) := by
    rw [hgamma,hmin]
    have hn : 0 ≤ min (r i) (sqrt (r i/(B*(b i)^2))) := le_min (hr i).le (sqrt_nonneg _)
    have hs : (min (r i) (sqrt (r i/(B*(b i)^2))))^2 ≤ r i/(B*(b i)^2) :=
      ((sq_le_sq₀ hn (sqrt_nonneg _)).mpr (min_le_right _ _)).trans_eq
        (sq_sqrt (div_nonneg (hr i).le (mul_nonneg hB.le (sq_nonneg _))))
    have heq : (r i/(B*(b i)^2))*B = r i/(b i)^2 := by field_simp
    have hh := mul_le_mul_of_nonneg_left
      ((mul_le_mul_of_nonneg_right hs hB.le).trans_eq heq) (sq_nonneg (μ.real (S i)))
    convert hh using 1; ring
  exact certificate_localized_annular_bound μ ρ B hB hN C hC S hS hd hm r hr hr4 hρ ν hν
    b hb hb4 (fun i => (hband i).mono (fun _ hh => hh.2)) (fun _ => 1) J (fun i _ => b i)
    (fun i _ => hb i) hJ (fun _ _ _ h => (h (Subsingleton.elim _ _)).elim)
    (fun _ _ _ hh => hh) (fun _ j k hk => by have hj := j.isLt; have hk' := k.isLt; omega)
    (fun _ => 1) (fun _ => le_rfl) (fun i j => (hmass i j).ge)
    (fun i => μ.real (S i)*min (r i) (sqrt (r i/(B*(b i)^2))))
    (fun i => mul_nonneg ENNReal.toReal_nonneg (le_min (hr i).le (sqrt_nonneg _)))
    (fun i => mul_le_mul_of_nonneg_left (min_le_left _ _) ENNReal.toReal_nonneg) hcost

end ThresholdHC.EntropyTailLower
