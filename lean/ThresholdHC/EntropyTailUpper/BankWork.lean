import ThresholdHC.EntropyTailUpper.LaplaceEnvelope
import ThresholdHC.EntropyTailUpper.PositiveRaceWork

/-! Conditional positive-bank work with the explicit three-piece surcharge. -/

noncomputable section
open MeasureTheory Set Real
open scoped NNReal

namespace ThresholdHC.EntropyTailUpper
open ThresholdHC ThresholdHC.Tier2 ThresholdHC.Tier6 ThresholdHC.ObservableSimulation

def positiveAllowance (ε w ρ V : ℝ) : ℝ :=
  1+log (ε⁻¹)+log (w⁻¹)+max 0 (log (V/ρ))

theorem positiveAllowance_ge_one {ε w ρ V : ℝ}
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hw : 0 < w) (hw1 : w ≤ 1) :
    1 ≤ positiveAllowance ε w ρ V := by
  have he := log_nonneg ((one_le_inv₀ hε).mpr hε1)
  have hw' := log_nonneg ((one_le_inv₀ hw).mpr hw1)
  have hm := le_max_left (0:ℝ) (log (V/ρ))
  unfold positiveAllowance
  linarith

theorem positiveAllowance_covers {ε w ρ V : ℝ}
    (hε : 0 < ε) (hw : 0 < w) (hρ : 0 < ρ) (hV : 0 ≤ V) :
    V ≤ (ρ*ε)*w*exp (positiveAllowance ε w ρ V) := by
  rcases hV.eq_or_lt with hV | hV
  · rw [← hV]
    positivity
  have he : exp (log (ε⁻¹)+log (w⁻¹)+log (V/ρ)) = ε⁻¹*w⁻¹*(V/ρ) := by
    rw [exp_add, exp_add, exp_log (inv_pos.mpr hε), exp_log (inv_pos.mpr hw), exp_log (div_pos hV hρ)]
  have hs : log (ε⁻¹)+log (w⁻¹)+log (V/ρ) ≤ positiveAllowance ε w ρ V := by
    have h := le_max_right (0:ℝ) (log (V/ρ))
    unfold positiveAllowance
    linarith
  calc
    V = (ρ*ε)*w*(ε⁻¹*w⁻¹*(V/ρ)) := by field_simp [hρ.ne', hε.ne', hw.ne']
    _ = (ρ*ε)*w*exp (log (ε⁻¹)+log (w⁻¹)+log (V/ρ)) := by rw [he]
    _ ≤ _ := mul_le_mul_of_nonneg_left (exp_le_exp.mpr hs) (by positivity)

def threePieceEnvelope (σ τ ζ : Measure Gap) (d : Gap) : ℝ :=
  ζ.real univ+(∫ x : Gap, (x:ℝ)⁻¹^2 ∂σ)*(d:ℝ)^2+(∫ x : Gap, (x:ℝ)⁻¹ ∂τ)*(d:ℝ)

theorem threePieceEnvelope_nonneg (σ τ ζ : Measure Gap) (d : Gap) :
    0 ≤ threePieceEnvelope σ τ ζ d := by
  unfold threePieceEnvelope
  exact add_nonneg (add_nonneg measureReal_nonneg
    (mul_nonneg (integral_nonneg (fun _ => sq_nonneg _)) (sq_nonneg _)))
    (mul_nonneg (integral_nonneg (fun x => inv_nonneg.mpr x.property.1.le)) d.property.1.le)

theorem bank_race_positive_work (σ τ ζ : Measure Gap)
    [IsFiniteMeasure σ] [IsFiniteMeasure τ] [IsFiniteMeasure ζ] [IsProbabilityMeasure (σ+τ+ζ)]
    (hσ : Integrable (fun x : Gap => (x:ℝ)⁻¹^2) σ)
    (hτ : Integrable (fun x : Gap => (x:ℝ)⁻¹) τ)
    (weights : ℕ → ℝ≥0) {ε ρ : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (hρ : 0 < ρ)
    (j L : ℕ) (hw : 0 < (weights j:ℝ)) (hw1 : (weights j:ℝ) ≤ 1)
    (d : Gap) (hd : d ∈ EntropyTailQuantile.band j) :
    (∫ ω, (raceCost (negativeBankTest weights ε) (positiveBankTest (σ+τ+ζ) weights (ρ*ε)) L ω : ℝ)
      ∂tapeMeasure (gapParameter true d)) ≤
      12*positiveAllowance ε (weights j:ℝ) ρ (threePieceEnvelope σ τ ζ d)/(d:ℝ)^2 := by
  have h := positive_raceRounds_work (σ+τ+ζ) weights ε (mul_pos hρ hε).le
    (positiveAllowance_ge_one hε hε1 hw hw1) j L d hd
    (fun n hn => nullLaplace_three_piece σ τ ζ hσ hτ d n hn)
    (positiveAllowance_covers hε hw hρ (threePieceEnvelope_nonneg σ τ ζ d))
  simp only [raceCost, Nat.cast_mul, Nat.cast_ofNat]
  rw [integral_const_mul]
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : (0:ℝ) ≤ 2)
  dsimp only [threePieceEnvelope]
  convert hm using 1
  ring

end ThresholdHC.EntropyTailUpper
