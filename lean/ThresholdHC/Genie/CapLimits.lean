import ThresholdHC.Genie.InfiniteDualLimit

/-! Monotone convergence of the finite-cap primal and ordinary information
values to their unrestricted-cap definitions. -/

noncomputable section
open MeasureTheory Filter
open scoped ENNReal Topology
namespace ThresholdHC.Genie
open ThresholdHC.Tier6 ThresholdHC.StoppingProgram

theorem programValue_tendsto (μ : Measure Gap) (ρ B : ℝ) :
    Tendsto (fun N : ℕ => programValue μ ρ B (N+1)) atTop
      (𝓝 (infiniteProgramValue μ ρ B)) :=
  tendsto_atTop_iInf (fun _ _ h => programValue_antitone μ ρ B (by omega))

theorem informationRatio_tendsto (μ : Measure Gap) (Q : FourPriors) :
    Tendsto (fun N : ℕ => informationRatio μ (N+1) Q) atTop
      (𝓝 (infiniteInformationRatio μ Q)) :=
  tendsto_atTop_iSup (fun _ _ h => informationRatio_mono μ Q (by omega))

theorem informationRatio_le_infinite (μ : Measure Gap) (N : ℕ) (Q : FourPriors) :
    informationRatio μ N Q ≤ infiniteInformationRatio μ Q :=
  (informationRatio_mono μ Q (Nat.le_succ N)).trans
    (le_iSup (fun M : ℕ => informationRatio μ (M+1) Q) N)

theorem infiniteProgramValue_le_cap (μ : Measure Gap) (ρ B : ℝ) (N : ℕ) :
    infiniteProgramValue μ ρ B ≤ programValue μ ρ B N :=
  (iInf_le (fun M : ℕ => programValue μ ρ B (M+1)) N).trans
    (programValue_antitone μ ρ B (Nat.le_succ N))

end ThresholdHC.Genie
