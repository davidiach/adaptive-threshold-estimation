import ThresholdHC.EntropyTail.Specification
import ThresholdHC.StoppingProgram.FiniteCertificate
import ThresholdHC.StoppingProgram.PrimalAttainment

/-! An equivalent finite-certificate obligation for the missing statistical
lower bound. This theorem is a reduction, not a proof of its premise. The
existing factor-sixteen theorem accounts for arbitrary adaptive population
algorithms, stopping, and actual expected observation work. -/
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace ThresholdHC.EntropyTailLower
open ThresholdHC.Tier6 ThresholdHC.RareAboveTwo ThresholdHC.StoppingProgram
open ThresholdHC.EntropyTail

/-- A purely finite-flow lower bound, uniform over every positive cap. -/
def CertificateLowerStatement : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ (μ : Measure Gap) [IsProbabilityMeasure μ]
    (ρ B : ℝ), 0 < ρ → ρ ≤ 1/4 → 0 < B →
    ∀ (N : ℕ), 0 < N → ∀ C : Certificate N, Feasible μ ρ B C →
      ENNReal.ofReal c * selection μ ρ B ≤ certificateSquared C ^ (1/2 : ℝ)

theorem entropy_tail_lower_iff_certificate_lower :
    EntropyTailLowerStatement ↔ CertificateLowerStatement := by
  constructor
  · rintro ⟨c,hc,h⟩
    refine ⟨c,hc,?_⟩
    intro μ _ ρ B hρ hρ4 hB N hN C hC
    have hp : programSquared μ ρ B N ≤ certificateSquared C :=
      sInf_le ⟨C,hC,rfl⟩
    exact (h ρ B hρ hρ4 hB μ).trans
      ((minimax_le_program μ hρ (by linarith) hB.le N hN).trans
        (ENNReal.rpow_le_rpow hp (by norm_num)))
  · rintro ⟨c,hc,h⟩
    refine ⟨c/16,by positivity,?_⟩
    intro ρ B hρ hρ4 hB μ _
    obtain ⟨C,hC,he⟩ := programSquared_attained (certificateCap ρ B) μ hρ
      (by linarith) hB.le
    have hl := h μ ρ B hρ hρ4 hB _ (certificateCap_pos ρ B hB) C hC
    rw [he] at hl
    have hr : ENNReal.ofReal c * selection μ ρ B ≤ 16*rareMinimaxRisk μ ρ B :=
      hl.trans (finite_certificate μ ρ B hρ hρ4 hB).2
    have hc16 : ENNReal.ofReal (c/16) * selection μ ρ B =
        (ENNReal.ofReal c * selection μ ρ B)/16 := by
      rw [ENNReal.ofReal_div_of_pos (by norm_num : (0:ℝ) < 16)]
      norm_num
      simp only [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]
    rw [hc16]
    exact (ENNReal.div_le_iff (by norm_num : (16:ℝ≥0∞) ≠ 0)
      (by norm_num : (16:ℝ≥0∞) ≠ ⊤)).mpr (by simpa [mul_comm] using hr)

end ThresholdHC.EntropyTailLower
