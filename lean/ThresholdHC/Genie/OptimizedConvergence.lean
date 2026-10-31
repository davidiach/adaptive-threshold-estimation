import ThresholdHC.Genie.RevealConvergence
import ThresholdHC.Genie.OptimizedBrackets

/-! Regularizing only the variance reference proves convergence of the
optimized genie brackets, even when unregularized references have infinite
latent divergence. -/

noncomputable section
open MeasureTheory Filter
open scoped ENNReal Topology
namespace ThresholdHC.Genie
open ThresholdHC.Tier6 ThresholdHC.RareAboveTwo ThresholdHC.StoppingProgram

theorem genieDualRatio_tendsto (μ : Measure Gap) [IsProbabilityMeasure μ]
    (B : ℝ) (hB : 0 < B) (Q : FourPriors) (hC : latentDivergence μ Q ≠ ⊤) :
    Tendsto (fun n : ℕ => genieDualRatio μ B (n+1) Q) atTop (𝓝 (infiniteDualRatio μ B Q)) := by
  have hK := genieInformationRatio_tendsto μ Q hC
  have hd : Tendsto (fun n : ℕ => 4+ENNReal.ofReal B*genieInformationRatio μ (n+1) Q) atTop
      (𝓝 (4+ENNReal.ofReal B*infiniteInformationRatio μ Q)) :=
    tendsto_const_nhds.add (ENNReal.Tendsto.const_mul hK (Or.inr ENNReal.ofReal_ne_top))
  exact ENNReal.Tendsto.const_div hd (Or.inr (ENNReal.pow_ne_top ENNReal.ofReal_ne_top))

theorem infiniteDualRatio_le_genieSup_of_finite (μ : Measure Gap) [IsProbabilityMeasure μ]
    {ρ B : ℝ} (hB : 0 < B) (Q : FourPriors) (hQ : Admissible μ ρ Q)
    (hC : latentDivergence μ Q ≠ ⊤) :
    infiniteDualRatio μ B Q ≤ ⨆ n : ℕ, genieSquared μ ρ B (n+1) := by
  apply le_of_tendsto (genieDualRatio_tendsto μ B hB Q hC)
  apply Eventually.of_forall
  intro n
  have hn : genieDualRatio μ B (n+1) Q ≤ genieSquared μ ρ B (n+1) :=
    le_iSup_of_le Q (le_iSup_of_le hQ le_rfl)
  exact hn.trans (le_iSup (fun n : ℕ => genieSquared μ ρ B (n+1)) n)

theorem infiniteDualRatio_le_genieSup (μ : Measure Gap) [IsProbabilityMeasure μ]
    {ρ B : ℝ} (hB : 0 < B) (Q : FourPriors) (hQ : Admissible μ ρ Q) :
    infiniteDualRatio μ B Q ≤ ⨆ n : ℕ, genieSquared μ ρ B (n+1) := by
  by_cases hK : infiniteInformationRatio μ Q = ⊤
  · simp [infiniteDualRatio,hK,(ENNReal.ofReal_pos.mpr hB).ne']
  let ε (n : ℕ) : ℝ := 1/((n:ℝ)+2)
  have hε (n : ℕ) : 0 < ε n ∧ ε n < 1 := by
    dsimp [ε]
    constructor
    · positivity
    · apply (div_lt_one (by positivity : 0 < (n:ℝ)+2)).mpr
      linarith [Nat.cast_nonneg (α := ℝ) n]
  have htε : Tendsto ε atTop (𝓝 0) := by
    convert (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).comp
      (tendsto_add_atTop_nat 1) using 1
    funext n
    norm_num [ε,Function.comp_def,Nat.cast_add,Nat.cast_one,add_assoc]
  have hc : Tendsto (fun n => ENNReal.ofReal (1/(1-ε n))) atTop (𝓝 1) := by
    have hr : Tendsto (fun n => 1/(1-ε n)) atTop (𝓝 ((1:ℝ)/(1-0))) :=
      tendsto_const_nhds.div (tendsto_const_nhds.sub htε) (by norm_num)
    simpa only [Function.comp_def,sub_zero,div_one,ENNReal.ofReal_one] using
      ENNReal.continuous_ofReal.continuousAt.tendsto.comp hr
  have hscale : Tendsto (fun n => ENNReal.ofReal B*(ENNReal.ofReal (1/(1-ε n))*infiniteInformationRatio μ Q))
      atTop (𝓝 (ENNReal.ofReal B*(1*infiniteInformationRatio μ Q))) :=
    ENNReal.Tendsto.const_mul (ENNReal.Tendsto.mul_const hc (Or.inr hK))
      (Or.inr ENNReal.ofReal_ne_top)
  have hden : Tendsto (fun n => 4+ENNReal.ofReal B*(ENNReal.ofReal (1/(1-ε n))*infiniteInformationRatio μ Q))
      atTop (𝓝 (4+ENNReal.ofReal B*(1*infiniteInformationRatio μ Q))) := tendsto_const_nhds.add hscale
  have ht : Tendsto (fun n => ENNReal.ofReal (signMean μ Q.high.val-signMean μ Q.low.val)^2/
      (4+ENNReal.ofReal B*(ENNReal.ofReal (1/(1-ε n))*infiniteInformationRatio μ Q))) atTop
        (𝓝 (infiniteDualRatio μ B Q)) := by
    simpa only [one_mul,infiniteDualRatio] using ENNReal.Tendsto.const_div
      (a := ENNReal.ofReal (signMean μ Q.high.val-signMean μ Q.low.val)^2) hden
      (Or.inr (ENNReal.pow_ne_top ENNReal.ofReal_ne_top))
  apply le_of_tendsto ht
  apply Eventually.of_forall
  intro n
  let A := regularizedPriors Q (ε n) ⟨(hε n).1.le,(hε n).2.le⟩
  have hA : Admissible μ ρ A := regularizedPriors_admissible μ Q hQ _ _
  have hC : latentDivergence μ A ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top
    (regularized_latentDivergence_bound μ Q _ _ (hε n).1)
  apply le_trans _ (infiniteDualRatio_le_genieSup_of_finite μ hB A hA hC)
  exact ENNReal.div_le_div_left (add_le_add le_rfl
    (mul_le_mul_right (regularized_infiniteInformation μ Q _ _ (hε n).2) _)) _

theorem genieSquared_sup_eq_infinite (μ : Measure Gap) [IsProbabilityMeasure μ]
    {ρ B : ℝ} (hρ : 0 < ρ) (hρhalf : ρ ≤ 1/2) (hB : 0 < B) :
    (⨆ n : ℕ, genieSquared μ ρ B (n+1)) = infiniteProgramValue μ ρ B ^ 2 := by
  apply le_antisymm
  · exact iSup_le (fun n => genieSquared_le_infinite μ ρ B hρ hρhalf hB (n+1) (by omega))
  · rw [(infinite_four_prior_duality μ hρ hρhalf hB).1]
    exact iSup_le (fun Q => iSup_le (infiniteDualRatio_le_genieSup μ hB Q))

theorem genieSquared_tendsto (μ : Measure Gap) [IsProbabilityMeasure μ]
    {ρ B : ℝ} (hρ : 0 < ρ) (hρhalf : ρ ≤ 1/2) (hB : 0 < B) :
    Tendsto (fun n : ℕ => genieSquared μ ρ B (n+1)) atTop (𝓝 (infiniteProgramValue μ ρ B ^ 2)) := by
  rw [←genieSquared_sup_eq_infinite μ hρ hρhalf hB]
  exact tendsto_atTop_iSup (genieSquared_mono μ ρ B)

theorem genieValue_tendsto (μ : Measure Gap) [IsProbabilityMeasure μ]
    {ρ B : ℝ} (hρ : 0 < ρ) (hρhalf : ρ ≤ 1/2) (hB : 0 < B) :
    Tendsto (fun n : ℕ => genieValue μ ρ B (n+1)) atTop (𝓝 (infiniteProgramValue μ ρ B)) := by
  have ht := (genieSquared_tendsto μ hρ hρhalf hB).ennrpow_const (1/2)
  rw [←ENNReal.rpow_two,←ENNReal.rpow_mul] at ht
  norm_num at ht
  exact ht

theorem infiniteProgramValue_ne_top (μ : Measure Gap) [IsProbabilityMeasure μ]
    {ρ B : ℝ} (hρ : 0 ≤ ρ) (hB : 0 ≤ B) : infiniteProgramValue μ ρ B ≠ ⊤ := by
  have hs : infiniteProgramValue μ ρ B ^ 2 < ⊤ := by
    rw [infiniteProgramValue_sq]
    exact (iInf_le (fun n : ℕ => programSquared μ ρ B (n+1)) 0).trans_lt
      (programSquared_finite μ hρ hB 1)
  intro ht
  simp [ht] at hs

theorem genie_stopping_eventually (μ : Measure Gap) [IsProbabilityMeasure μ]
    {ρ B : ℝ} (hρ : 0 < ρ) (hρhalf : ρ ≤ 1/2) (hB : 0 < B) :
    ∀ᶠ n : ℕ in atTop, programValue μ ρ B (n+1) ≤ 2*genieValue μ ρ B (n+1) := by
  have hp : 0 < infiniteProgramValue μ ρ B :=
    (genieValue_positive μ ρ B hρ (by linarith) 1).trans_le
      (genieValue_le_infinite μ ρ B hρ hρhalf hB 1 (by omega))
  have hf := infiniteProgramValue_ne_top μ hρ.le hB.le
  have hlt : infiniteProgramValue μ ρ B < 2*infiniteProgramValue μ ρ B := by
    simpa only [one_mul] using ENNReal.mul_lt_mul_left hp.ne' hf (show (1:ℝ≥0∞) < 2 by norm_num)
  have hg : Tendsto (fun n : ℕ => 2*genieValue μ ρ B (n+1)) atTop
      (𝓝 (2*infiniteProgramValue μ ρ B)) :=
    ENNReal.Tendsto.const_mul (genieValue_tendsto μ hρ hρhalf hB) (Or.inl hp.ne')
  exact ((programValue_tendsto μ ρ B).eventually_lt hg hlt).mono (fun _ h => h.le)

theorem genie_stopping_terminates (μ : Measure Gap) [IsProbabilityMeasure μ]
    {ρ B : ℝ} (hρ : 0 < ρ) (hρhalf : ρ ≤ 1/2) (hB : 0 < B) :
    ∃ N : ℕ, 0 < N ∧ programValue μ ρ B N ≤ 2*genieValue μ ρ B N ∧
      rareMinimaxRisk μ ρ B ≤ programValue μ ρ B N ∧
        programValue μ ρ B N ≤ 16*rareMinimaxRisk μ ρ B := by
  obtain ⟨n,hn⟩ := (genie_stopping_eventually μ hρ hρhalf hB).exists
  exact ⟨n+1,by omega,hn,genie_stopping_certificate μ ρ B hρ hρhalf hB (n+1) (by omega) hn⟩

end ThresholdHC.Genie
