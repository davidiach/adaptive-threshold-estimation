import ThresholdHC.EntropyTail.Band
import ThresholdHC.EntropyTail.Entropy

/-! The submeasure entropy dominates the full inverse-square cost, equals zero at
the zero measure and equals `d^{-2}` at a point mass. -/
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace ThresholdHC.EntropyTail
open ThresholdHC.Tier6

/-- Every finite prefix of band costs is at most `Γ_σ`. -/
theorem sum_bandCost_le_gamma (σ : Measure Gap) (J : ℕ) :
    ∑ j ∈ Finset.range (J+1), bandCost σ j ≤ gamma σ := by
  unfold gamma
  refine le_iSup_of_le J ?_
  split_ifs with h
  · rw [Finset.sum_range (bandCost σ)]
    calc ∑ j : Fin (J+1), bandCost σ j
        = ENNReal.ofReal (∑ j : Fin (J+1), (bandCost σ j).toReal) := by
          rw [ENNReal.ofReal_sum_of_nonneg (fun j _ => ENNReal.toReal_nonneg)]
          exact Finset.sum_congr rfl (fun j _ => (ENNReal.ofReal_toReal (h j)).symm)
      _ ≤ _ := ENNReal.ofReal_le_ofReal
          (sum_le_costEntropy _ (fun j => ENNReal.toReal_nonneg))
  · exact le_top

/-- `∫ d^{-2} dσ ≤ Γ_σ`. -/
theorem lintegral_le_gamma (σ : Measure Gap) :
    ∫⁻ d, ENNReal.ofReal (((d : ℝ)⁻¹)^2) ∂σ ≤ gamma σ := by
  let f : Gap → ℝ≥0∞ := fun d => ENNReal.ofReal (((d : ℝ)⁻¹)^2)
  let U : ℕ → Set Gap := fun J => ⋃ j ∈ Finset.range (J+1), band j
  have hU : (⋃ J, U J) = Set.univ := by
    refine Set.eq_univ_of_forall fun d => ?_
    obtain ⟨j, hj⟩ := exists_band d
    simp only [U, Set.mem_iUnion, Finset.mem_range]
    exact ⟨j, j, Nat.lt_succ_self j, hj⟩
  have hmono : Monotone U := by
    intro J K hJK d hd
    simp only [U, Set.mem_iUnion, Finset.mem_range] at hd ⊢
    obtain ⟨j, hj, hd⟩ := hd
    exact ⟨j, by omega, hd⟩
  have hint : ∫⁻ d, f d ∂σ = σ.withDensity f Set.univ := by
    rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  change ∫⁻ d, f d ∂σ ≤ gamma σ
  rw [hint, ← hU, hmono.measure_iUnion]
  refine iSup_le fun J => ?_
  change σ.withDensity f (⋃ j ∈ Finset.range (J+1), band j) ≤ gamma σ
  rw [measure_biUnion_finset (fun i _ j _ hij => band_disjoint hij)
    (fun j _ => measurableSet_band j)]
  calc ∑ j ∈ Finset.range (J+1), σ.withDensity f (band j)
      = ∑ j ∈ Finset.range (J+1), bandCost σ j :=
        Finset.sum_congr rfl fun j _ => withDensity_apply _ (measurableSet_band j)
    _ ≤ gamma σ := sum_bandCost_le_gamma σ J

theorem four_le_inv_sq (d : Gap) : (4 : ℝ) ≤ ((d : ℝ)⁻¹)^2 := by
  have hd := d.2
  have h2 : (2 : ℝ) ≤ 1 / (d : ℝ) := by
    rw [le_div_iff₀ hd.1]
    linarith
  rw [one_div] at h2
  nlinarith

/-- `4 σ((0,1/2]) ≤ Γ_σ`, since `d^{-2} ≥ 4`. -/
theorem four_mass_le_gamma (σ : Measure Gap) : 4 * σ Set.univ ≤ gamma σ := by
  refine le_trans ?_ (lintegral_le_gamma σ)
  rw [← lintegral_const]
  refine lintegral_mono fun d => ?_
  calc (4 : ℝ≥0∞) = ENNReal.ofReal 4 := by simp
    _ ≤ _ := ENNReal.ofReal_le_ofReal (four_le_inv_sq d)

theorem gamma_zero : gamma 0 = 0 := by
  have h0 : ∀ j, bandCost 0 j = 0 := fun j => by simp [bandCost]
  unfold gamma
  simp [h0, costEntropy]

theorem bandCost_dirac (d : Gap) (j : ℕ) :
    bandCost (Measure.dirac d) j =
      (band j).indicator (fun x : Gap => ENNReal.ofReal (((x : ℝ)⁻¹)^2)) d := by
  unfold bandCost
  rw [← lintegral_indicator (measurableSet_band j), lintegral_dirac]

/-- At a point mass only one band is charged, so `Γ_{δ_d} ≤ d^{-2}`. -/
theorem gamma_dirac_le (d : Gap) :
    gamma (Measure.dirac d) ≤ ENNReal.ofReal (((d : ℝ)⁻¹)^2) := by
  classical
  unfold gamma
  refine iSup_le fun J => ?_
  split_ifs with h
  · refine ENNReal.ofReal_le_ofReal ?_
    set a : Fin (J+1) → ℝ := fun j => (bandCost (Measure.dirac d) j).toReal with ha
    have hval : ∀ j : Fin (J+1), a j = if d ∈ band j then ((d : ℝ)⁻¹)^2 else 0 := by
      intro j
      simp only [ha, bandCost_dirac, Set.indicator_apply]
      split_ifs
      · exact ENNReal.toReal_ofReal (sq_nonneg _)
      · rfl
    have hone : ∀ i j, a i ≠ 0 → a j ≠ 0 → i = j := by
      intro i j hi hj
      rw [hval] at hi hj
      split_ifs at hi hj with hdi hdj
      · by_contra hne
        exact Set.disjoint_left.1 (band_disjoint (fun e => hne (Fin.ext e))) hdi hdj
      · exact absurd rfl hj
      · exact absurd rfl hi
      · exact absurd rfl hi
    rw [costEntropy_eq_sum a hone]
    by_cases hex : ∃ j : Fin (J+1), d ∈ band j
    · obtain ⟨j, hj⟩ := hex
      rw [Finset.sum_eq_single j (fun i _ hij => ?_) (fun h => absurd (Finset.mem_univ j) h),
        hval, ite_eq_left hj]
      by_contra hi
      exact hij (hone i j hi (by
        rw [hval, ite_eq_left hj]
        exact pow_ne_zero 2 (inv_ne_zero (ne_of_gt d.2.1))))
    · push Not at hex
      rw [Finset.sum_eq_zero (fun j _ => by rw [hval, ite_eq_right (hex j)])]
      positivity
  · exact absurd (fun j => by rw [bandCost_dirac]; unfold Set.indicator; split_ifs <;> simp) h

end ThresholdHC.EntropyTail
