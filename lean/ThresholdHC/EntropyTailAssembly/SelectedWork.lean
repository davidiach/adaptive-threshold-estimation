import ThresholdHC.EntropyTailAssembly.BandEntropy
import ThresholdHC.EntropyTailAssembly.IntegratedSurcharge
import ThresholdHC.EntropyTailAssembly.ConditionalWork

/-! The selected component's integrated work is controlled by its actual cost
entropy and the global rarity allowance. -/

noncomputable section
open MeasureTheory Set Real
open scoped NNReal BigOperators

namespace ThresholdHC.EntropyTailAssembly
open ThresholdHC ThresholdHC.Tier6 ThresholdHC.EntropyTail ThresholdHC.EntropyTailUpper

theorem selected_work_bound (σ τ ζ : Measure Gap)
    [IsFiniteMeasure σ] [IsFiniteMeasure τ] [IsFiniteMeasure ζ] [IsProbabilityMeasure (σ+τ+ζ)]
    {t ε ρ : ℝ} {N : ℕ} (ht : 0 < t) (hs : ∀ᵐ d : Gap ∂σ, t ≤ (d:ℝ))
    (hN : bandEdge N < t) (hA : 0 < ∫ d : Gap, (d:ℝ)⁻¹^2 ∂σ)
    (hτ : Integrable (fun d : Gap => (d:ℝ)⁻¹) τ)
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hρ : 0 < ρ) (hz : ζ.real univ ≤ ρ)
    (q : SignLaw) (hq : RareAboveTwo.RarePrior (σ+τ+ζ) ρ q) (L : ℕ) :
    (∫ d, mixtureRaceWork q (negativeBankTest (bandWeights σ) ε)
      (positiveBankTest (σ+τ+ζ) (bandWeights σ) (ρ*ε)) L d ∂σ) ≤
      12*costEntropy (fun j : Fin N => bandCost σ j.val) +
      12*(∫ d : Gap, (d:ℝ)⁻¹^2 ∂σ)*log (ε⁻¹) +
      12*(log 3+1)*(∫ d : Gap, (d:ℝ)⁻¹^2 ∂σ) +
      6*(∫ d : Gap, (d:ℝ)⁻¹ ∂τ)^2/ρ := by
  let A := ∫ d : Gap, (d:ℝ)⁻¹^2 ∂σ
  let H := ∫ d : Gap, (d:ℝ)⁻¹ ∂τ
  let z := ζ.real univ
  let neg := negativeBankTest (bandWeights σ) ε
  let pos := positiveBankTest (σ+τ+ζ) (bandWeights σ) (ρ*ε)
  let W := mixtureRaceWork q neg pos L
  let K := fun d : Gap => q.val d*(d:ℝ)⁻¹^2*logPlus ((z+A*(d:ℝ)^2+H*(d:ℝ))/ρ)
  let c := fun j : Fin N => 1+log (ε⁻¹)+log ((bandWeights σ j.val:ℝ)⁻¹)
  have hI₂ := inverseSquare_integrable_of_support σ ht hs
  have hσμ : σ ≤ σ+τ+ζ := Measure.le_add_right (Measure.le_add_right le_rfl)
  have hqσ := selected_signMean_le hσμ q hq
  have hH : 0 ≤ H := integral_nonneg (fun d => inv_nonneg.mpr d.property.1.le)
  obtain ⟨hKi,hKb⟩ := integrated_log_surcharge σ q hI₂ (A := A) (H := H) (ρ := ρ)
    (measureReal_nonneg : 0 ≤ z) hz hA.le hH hρ hqσ
  change Integrable K σ at hKi
  change (∫ d, K d ∂σ) ≤ log 3*A+A+H^2/(2*ρ) at hKb
  have hWi : Integrable W σ := integrable_mixtureRaceWork σ q neg pos L
  have hband (j : Fin N) :
      (∫ d in band j.val, W d ∂σ) ≤ 12*c j*bandCost σ j.val+12*(∫ d in band j.val, K d ∂σ) := by
    by_cases hj : bandCost σ j.val = 0
    · rw [Measure.restrict_eq_zero.mpr (bandCost_zero_measure σ j.val hj)]
      simp [hj]
    have hjpos : 0 < bandCost σ j.val := lt_of_le_of_ne (bandCost_nonneg σ j.val) (Ne.symm hj)
    have hw := bandWeights_positive σ hA hjpos
    have hw1 := bandWeights_le_one σ hs hN hA j.val
    have hpt (d : Gap) (hd : d ∈ band j.val) : W d ≤ (12*c j)*(d:ℝ)⁻¹^2+12*K d := by
      have h := bank_mixture_work_bound σ τ ζ hI₂ hτ (bandWeights σ) hε hε1 hρ j.val L hw hw1 q d hd
      apply h.trans_eq
      dsimp [c, K, z, A, H, threePieceEnvelope]
      ring
    have hiR : IntegrableOn (fun d : Gap => (12*c j)*(d:ℝ)⁻¹^2+12*K d) (band j.val) σ :=
      ((band_inverseSquare_integrable σ j.val).const_mul (12*c j)).add (hKi.integrableOn.const_mul 12)
    have h := integral_mono_ae hWi.integrableOn hiR (by
      filter_upwards [ae_restrict_mem (measurableSet_band j.val)] with d hd
      exact hpt d hd)
    rw [integral_add ((band_inverseSquare_integrable σ j.val).const_mul (12*c j))
      (hKi.integrableOn.const_mul 12)] at h
    simp only [integral_const_mul] at h
    exact h
  have hsum :
      (∑ j : Fin N, (12*c j*bandCost σ j.val+12*(∫ d in band j.val, K d ∂σ))) =
      12*costEntropy (fun j : Fin N => bandCost σ j.val)+12*A*log (ε⁻¹)+12*(∫ d, K d ∂σ) := by
    have he : (∑ j : Fin N, (12*c j*bandCost σ j.val+12*(∫ d in band j.val, K d ∂σ))) =
        12*(∑ j : Fin N, bandCost σ j.val*(1+log ((bandWeights σ j.val:ℝ)⁻¹)))+
        12*log (ε⁻¹)*(∑ j : Fin N, bandCost σ j.val)+12*(∑ j : Fin N, ∫ d in band j.val, K d ∂σ) := by
      simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro j _
      dsimp [c]
      ring
    rw [he, bandWeights_entropy σ hs hN, ← integral_eq_sum_bands σ hs hN K (fun _ => hKi.integrableOn)]
    have htot := inverseSquare_eq_band_total σ hs hN
    change A = ∑ j : Fin N, bandCost σ j.val at htot
    rw [← htot]
    ring
  have htotal : (∫ d, W d ∂σ) ≤
      12*costEntropy (fun j : Fin N => bandCost σ j.val)+12*A*log (ε⁻¹)+12*(∫ d, K d ∂σ) := by
    rw [integral_eq_sum_bands σ hs hN W (fun _ => hWi.integrableOn), ← hsum]
    exact Finset.sum_le_sum (fun j _ => hband j)
  have hk := mul_le_mul_of_nonneg_left hKb (by norm_num : (0:ℝ) ≤ 12)
  change (∫ d, W d ∂σ) ≤ _
  dsimp only [A, H] at htotal hk
  exact htotal.trans ((add_le_add le_rfl hk).trans_eq (by ring))

end ThresholdHC.EntropyTailAssembly
