import ThresholdHC.Genie.RevealTruncation
import ThresholdHC.Genie.InfiniteDuality
import ThresholdHC.Genie.ReferenceRegularization

/-! Optimizing the reveal dual gives a positive monotone lower certificate
for the original minimax risk. The factor-sixteen stopping test is valid
at every cap at which its explicit inequality is verified. -/

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace ThresholdHC.Genie
open ThresholdHC.Tier6 ThresholdHC.RareAboveTwo ThresholdHC.StoppingProgram

def genieDualRatio (μ : Measure Gap) (B : ℝ) (N : ℕ) (Q : FourPriors) : ℝ≥0∞ :=
  ENNReal.ofReal (signMean μ Q.high.val-signMean μ Q.low.val)^2/
    (4+ENNReal.ofReal B*genieInformationRatio μ N Q)

def genieSquared (μ : Measure Gap) (ρ B : ℝ) (N : ℕ) : ℝ≥0∞ :=
  ⨆ (Q : FourPriors) (_ : Admissible μ ρ Q), genieDualRatio μ B N Q

def genieValue (μ : Measure Gap) (ρ B : ℝ) (N : ℕ) : ℝ≥0∞ :=
  genieSquared μ ρ B N ^ (1/(2:ℝ))

theorem genieDualRatio_le_infinite (μ : Measure Gap) [IsFiniteMeasure μ]
    (B : ℝ) (N : ℕ) (hN : 0 < N) (Q : FourPriors) :
    genieDualRatio μ B N Q ≤ infiniteDualRatio μ B Q :=
  ENNReal.div_le_div_left (add_le_add le_rfl
    (mul_le_mul_right (infiniteInformationRatio_le_genie μ N hN Q) _)) _

theorem genieSquared_mono (μ : Measure Gap) [IsFiniteMeasure μ] (ρ B : ℝ) :
    Monotone (fun N : ℕ => genieSquared μ ρ B (N+1)) := by
  intro N M hNM
  apply iSup_mono
  intro Q
  apply iSup_mono
  intro hQ
  exact ENNReal.div_le_div_left (add_le_add le_rfl
    (mul_le_mul_right (genieInformationRatio_antitone μ Q hNM) _)) _

theorem genieValue_mono (μ : Measure Gap) [IsFiniteMeasure μ] (ρ B : ℝ) :
    Monotone (fun N : ℕ => genieValue μ ρ B (N+1)) := by
  intro N M hNM
  exact ENNReal.rpow_le_rpow (genieSquared_mono μ ρ B hNM) (by norm_num)

theorem genieSquared_le_infinite (μ : Measure Gap) [IsProbabilityMeasure μ]
    (ρ B : ℝ) (hρ : 0 < ρ) (hρhalf : ρ ≤ 1/2) (hB : 0 < B) (N : ℕ) (hN : 0 < N) :
    genieSquared μ ρ B N ≤ infiniteProgramValue μ ρ B ^ 2 := by
  apply iSup_le
  intro Q
  apply iSup_le
  intro hQ
  exact (genieDualRatio_le_infinite μ B N hN Q).trans (infinite_weak_duality μ hρ hρhalf hB Q hQ)

theorem genieValue_le_infinite (μ : Measure Gap) [IsProbabilityMeasure μ]
    (ρ B : ℝ) (hρ : 0 < ρ) (hρhalf : ρ ≤ 1/2) (hB : 0 < B) (N : ℕ) (hN : 0 < N) :
    genieValue μ ρ B N ≤ infiniteProgramValue μ ρ B := by
  have h := ENNReal.rpow_le_rpow (genieSquared_le_infinite μ ρ B hρ hρhalf hB N hN)
    (show (0:ℝ) ≤ 1/2 by norm_num)
  rw [←ENNReal.rpow_two,←ENNReal.rpow_mul] at h
  norm_num at h
  exact h

theorem genie_risk_bracket (μ : Measure Gap) [IsProbabilityMeasure μ]
    (ρ B : ℝ) (hρ : 0 < ρ) (hρhalf : ρ ≤ 1/2) (hB : 0 < B) (N : ℕ) (hN : 0 < N) :
    genieValue μ ρ B N/8 ≤ rareMinimaxRisk μ ρ B ∧
      rareMinimaxRisk μ ρ B ≤ programValue μ ρ B N := by
  refine ⟨?_,minimax_le_program μ hρ hρhalf hB.le N hN⟩
  apply (ENNReal.div_le_iff (by norm_num : (8:ℝ≥0∞) ≠ 0) (by norm_num : (8:ℝ≥0∞) ≠ ⊤)).mpr
  simpa only [mul_comm] using (genieValue_le_infinite μ ρ B hρ hρhalf hB N hN).trans
    (infinite_program_comparison μ ρ B hρ hρhalf hB).2

theorem genie_stopping_certificate (μ : Measure Gap) [IsProbabilityMeasure μ]
    (ρ B : ℝ) (hρ : 0 < ρ) (hρhalf : ρ ≤ 1/2) (hB : 0 < B) (N : ℕ) (hN : 0 < N)
    (hcheck : programValue μ ρ B N ≤ 2*genieValue μ ρ B N) :
    rareMinimaxRisk μ ρ B ≤ programValue μ ρ B N ∧
      programValue μ ρ B N ≤ 16*rareMinimaxRisk μ ρ B := by
  have hg := (genieValue_le_infinite μ ρ B hρ hρhalf hB N hN).trans
    (infinite_program_comparison μ ρ B hρ hρhalf hB).2
  refine ⟨minimax_le_program μ hρ hρhalf hB.le N hN,?_⟩
  calc
    _ ≤ 2*genieValue μ ρ B N := hcheck
    _ ≤ 2*(8*rareMinimaxRisk μ ρ B) := mul_le_mul_right hg 2
    _ = _ := by rw [←mul_assoc]; norm_num

theorem genieValue_positive (μ : Measure Gap) [IsProbabilityMeasure μ]
    (ρ B : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (N : ℕ) : 0 < genieValue μ ρ B N := by
  let q := constantPrior 0 (by norm_num)
  let r := constantPrior ρ ⟨hρ.le,hρ1⟩
  let Q : FourPriors := ⟨q,r,r,r⟩
  have hq : RarePrior μ ρ q := by
    change signMean μ (constantPrior 0 _).val ≤ ρ
    rw [constantPrior_mean]
    exact hρ.le
  have hr : RarePrior μ ρ r := le_of_eq (constantPrior_mean μ ρ _)
  let A := regularizedPriors Q (1/2) (by norm_num)
  have hA : Admissible μ ρ A := regularizedPriors_admissible μ Q ⟨hq,hr,hr,hr⟩ _ _
  have hC : latentDivergence μ A ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top
    (regularized_latentDivergence_bound μ Q (1/2) (by norm_num) (by norm_num))
  have hK : genieInformationRatio μ N A ≠ ⊤ :=
    ne_top_of_le_ne_top hC (genieInformationRatio_le_latent μ N A)
  have hgap : signMean μ A.high.val-signMean μ A.low.val = ρ := by
    simp only [A,regularizedPriors,Q,q,r,constantPrior_mean,sub_zero]
  have hd : 0 < genieDualRatio μ B N A := by
    rw [genieDualRatio,hgap]
    apply ENNReal.div_pos
    · exact (ENNReal.pow_pos (ENNReal.ofReal_pos.mpr hρ) 2).ne'
    · exact ENNReal.add_ne_top.mpr ⟨by norm_num,ENNReal.mul_ne_top ENNReal.ofReal_ne_top hK⟩
  have hs : 0 < genieSquared μ ρ B N := hd.trans_le
    (le_iSup_of_le A (le_iSup_of_le hA le_rfl))
  unfold genieValue
  positivity

end ThresholdHC.Genie
