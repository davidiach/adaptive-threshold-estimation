import ThresholdHC.EntropyTailLower.FiniteCertificateCost
import ThresholdHC.EntropyTailLower.CertificateReduction

noncomputable section
namespace ThresholdHC.EntropyTailLower
open MeasureTheory Real
open ThresholdHC.Tier6 ThresholdHC.StoppingProgram
open scoped ENNReal

theorem certificate_annular_bound_le_root {N : ℕ} (C : Certificate N)
    (hb : 0 ≤ C.bias) (hv : 0 ≤ C.variance) :
    256*C.bias+sqrt ((4294967296*exp 48)*C.variance) ≤
      (256+sqrt (4294967296*exp 48))*sqrt (C.bias^2+C.variance) := by
  have hbroot : C.bias ≤ sqrt (C.bias^2+C.variance) := by
    calc
      _ = sqrt (C.bias^2) := (sqrt_sq hb).symm
      _ ≤ _ := sqrt_le_sqrt (by linarith only [hv])
  have hvroot : sqrt C.variance ≤ sqrt (C.bias^2+C.variance) :=
    sqrt_le_sqrt (by linarith only [sq_nonneg C.bias])
  have hK : 0 ≤ (4294967296:ℝ)*exp 48 := by positivity
  rw [sqrt_mul hK]
  have h1 := mul_le_mul_of_nonneg_left hbroot (by norm_num : (0:ℝ) ≤ 256)
  have h2 := mul_le_mul_of_nonneg_left hvroot (sqrt_nonneg ((4294967296:ℝ)*exp 48))
  nlinarith only [h1,h2]

theorem certificate_lower : CertificateLowerStatement := by
  let M : ℝ := 200000000*(256+sqrt (4294967296*exp 48))
  have hM : 0 < M := by dsimp [M]; positivity
  refine ⟨1/M,by positivity,?_⟩
  intro μ _ ρ B hρ hρ4 hB N hN C hC
  have hρ1 : ρ ≤ 1 := by linarith only [hρ4]
  have hs := certificate_selection_upper μ ρ B hρ hρ1 hB hN C hC
  have hr := certificate_annular_bound_le_root C hC.bias_nonneg hC.variance_nonneg
  have hbound : ThresholdHC.EntropyTail.selection μ ρ B ≤
      ENNReal.ofReal (M*sqrt (C.bias^2+C.variance)) := by
    apply hs.trans
    apply ENNReal.ofReal_le_ofReal
    have h := mul_le_mul_of_nonneg_left hr (by norm_num : (0:ℝ) ≤ 200000000)
    dsimp [M]
    nlinarith only [h]
  calc
    ENNReal.ofReal (1/M)*ThresholdHC.EntropyTail.selection μ ρ B ≤
        ENNReal.ofReal (1/M)*ENNReal.ofReal (M*sqrt (C.bias^2+C.variance)) :=
      mul_le_mul' le_rfl hbound
    _ = ENNReal.ofReal ((1/M)*(M*sqrt (C.bias^2+C.variance))) :=
      (ENNReal.ofReal_mul (show (0:ℝ) ≤ 1/M by positivity)).symm
    _ = ENNReal.ofReal (sqrt (C.bias^2+C.variance)) := by
      congr 1
      field_simp [hM.ne']
    _ = certificateSquared C^(1/2:ℝ) := by
      rw [certificateSquared,ENNReal.ofReal_rpow_of_nonneg
        (show 0 ≤ C.bias^2+C.variance by positivity [hC.variance_nonneg]) (by norm_num),← sqrt_eq_rpow]

end ThresholdHC.EntropyTailLower
