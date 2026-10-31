import ThresholdHC.EntropyTailUpper.BankWork
import ThresholdHC.EntropyTailUpper.PopulationErrors
import ThresholdHC.EntropyTailUpper.LogSurcharge

/-! Conditional and sign-mixture work of the actual finite race. -/

noncomputable section
open MeasureTheory Set Real
open scoped NNReal

namespace ThresholdHC.EntropyTailAssembly
open ThresholdHC ThresholdHC.Tier2 ThresholdHC.Tier6 ThresholdHC.ObservableSimulation
open ThresholdHC.EntropyTailUpper

def conditionalRaceWork (neg pos : PrefixTest) (L : ℕ) (s : Bool) (d : Gap) : ℝ :=
  ∫ ω, (raceCost neg pos L ω : ℝ) ∂tapeMeasure (gapParameter s d)

theorem measurable_conditionalRaceWork (neg pos : PrefixTest) (L : ℕ) (s : Bool) :
    Measurable (conditionalRaceWork neg pos L s) := by
  exact (CriticalUpper.measurable_tape_integral (fun ω => (raceCost neg pos L ω : ℝ))
    ((measurable_of_countable (fun n : ℕ => (n:ℝ))).comp (measurable_raceCost neg pos L))).comp
    (measurable_gapParameter s)

theorem conditionalRaceWork_nonneg (neg pos : PrefixTest) (L : ℕ) (s : Bool) (d : Gap) :
    0 ≤ conditionalRaceWork neg pos L s d := integral_nonneg (fun _ => Nat.cast_nonneg _)

theorem conditionalRaceWork_le_cap (neg pos : PrefixTest) (L : ℕ) (s : Bool) (d : Gap) :
    conditionalRaceWork neg pos L s d ≤ 2*(2^L) := by
  have h := integral_mono (integrable_raceCost neg pos L (gapParameter s d))
    (integrable_const (2*(2^L):ℝ)) (fun ω => show (raceCost neg pos L ω : ℝ) ≤ 2*(2^L) by
      exact_mod_cast raceCost_le neg pos L ω)
  change (∫ ω, (raceCost neg pos L ω : ℝ) ∂tapeMeasure (gapParameter s d)) ≤ 2*(2^L)
  simpa only [integral_const, probReal_univ, smul_eq_mul, one_mul] using h

def mixtureRaceWork (q : SignLaw) (neg pos : PrefixTest) (L : ℕ) (d : Gap) : ℝ :=
  q.val d*conditionalRaceWork neg pos L true d+(1-q.val d)*conditionalRaceWork neg pos L false d

theorem mixtureRaceWork_nonneg (q : SignLaw) (neg pos : PrefixTest) (L : ℕ) (d : Gap) :
    0 ≤ mixtureRaceWork q neg pos L d := by
  exact add_nonneg (mul_nonneg (q.property.2 d).1 (conditionalRaceWork_nonneg neg pos L true d))
    (mul_nonneg (sub_nonneg.mpr (q.property.2 d).2) (conditionalRaceWork_nonneg neg pos L false d))

theorem mixtureRaceWork_le_cap (q : SignLaw) (neg pos : PrefixTest) (L : ℕ) (d : Gap) :
    mixtureRaceWork q neg pos L d ≤ 2*(2^L) := by
  have hp := mul_le_mul_of_nonneg_left (conditionalRaceWork_le_cap neg pos L true d) (q.property.2 d).1
  have hn := mul_le_mul_of_nonneg_left (conditionalRaceWork_le_cap neg pos L false d)
    (sub_nonneg.mpr (q.property.2 d).2)
  unfold mixtureRaceWork
  nlinarith only [hp, hn]

theorem measurable_mixtureRaceWork (q : SignLaw) (neg pos : PrefixTest) (L : ℕ) :
    Measurable (mixtureRaceWork q neg pos L) :=
  (q.property.1.mul (measurable_conditionalRaceWork neg pos L true)).add
    ((measurable_const.sub q.property.1).mul (measurable_conditionalRaceWork neg pos L false))

theorem integrable_mixtureRaceWork (σ : Measure Gap) [IsFiniteMeasure σ]
    (q : SignLaw) (neg pos : PrefixTest) (L : ℕ) : Integrable (mixtureRaceWork q neg pos L) σ := by
  apply Integrable.of_bound (measurable_mixtureRaceWork q neg pos L).aestronglyMeasurable (2*(2^L))
  exact ae_of_all _ (fun d => by
    rw [Real.norm_of_nonneg (mixtureRaceWork_nonneg q neg pos L d)]
    exact mixtureRaceWork_le_cap q neg pos L d)

theorem log_inverse_product {ε w : ℝ} (hε : 0 < ε) (hw : 0 < w) :
    log ((ε*w)⁻¹) = log (ε⁻¹)+log (w⁻¹) := by
  simp only [log_inv, log_mul hε.ne' hw.ne']
  ring

theorem bank_mixture_work_bound (σ τ ζ : Measure Gap)
    [IsFiniteMeasure σ] [IsFiniteMeasure τ] [IsFiniteMeasure ζ] [IsProbabilityMeasure (σ+τ+ζ)]
    (hσ : Integrable (fun x : Gap => (x:ℝ)⁻¹^2) σ)
    (hτ : Integrable (fun x : Gap => (x:ℝ)⁻¹) τ)
    (weights : ℕ → ℝ≥0) {ε ρ : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (hρ : 0 < ρ)
    (j L : ℕ) (hw : 0 < (weights j:ℝ)) (hw1 : (weights j:ℝ) ≤ 1)
    (q : SignLaw) (d : Gap) (hd : d ∈ EntropyTail.band j) :
    mixtureRaceWork q (negativeBankTest weights ε) (positiveBankTest (σ+τ+ζ) weights (ρ*ε)) L d ≤
      12*(d:ℝ)⁻¹^2*(1+log (ε⁻¹)+log ((weights j:ℝ)⁻¹))+
      12*q.val d*(d:ℝ)⁻¹^2*logPlus (threePieceEnvelope σ τ ζ d/ρ) := by
  let B := 12*(d:ℝ)⁻¹^2*(1+log (ε⁻¹)+log ((weights j:ℝ)⁻¹))
  let S := (d:ℝ)⁻¹^2*logPlus (threePieceEnvelope σ τ ζ d/ρ)
  have hb : 0 ≤ 1+log (ε⁻¹)+log ((weights j:ℝ)⁻¹) := by
    have he := log_nonneg ((one_le_inv₀ hε).mpr hε1)
    have hw' := log_nonneg ((one_le_inv₀ hw).mpr hw1)
    linarith
  have hp : conditionalRaceWork (negativeBankTest weights ε) (positiveBankTest (σ+τ+ζ) weights (ρ*ε)) L true d ≤ B+12*S := by
    have h := bank_race_positive_work σ τ ζ hσ hτ weights hε hε1 hρ j L hw hw1 d hd
    apply h.trans_eq
    dsimp [B, S, positiveAllowance, logPlus]
    ring
  have hn : conditionalRaceWork (negativeBankTest weights ε) (positiveBankTest (σ+τ+ζ) weights (ρ*ε)) L false d ≤ B := by
    have h := bank_race_negative_work (σ+τ+ζ) weights hε hε1 (ρ*ε) j L hw hw1 d hd
    rw [log_inverse_product hε hw] at h
    apply h.trans
    have he : (3/(2*(d:ℝ)^2))*(1+(log (ε⁻¹)+log ((weights j:ℝ)⁻¹))) =
        (3/2)*((d:ℝ)⁻¹^2*(1+log (ε⁻¹)+log ((weights j:ℝ)⁻¹))) := by ring
    rw [he]
    dsimp [B]
    nlinarith only [mul_nonneg (sq_nonneg ((d:ℝ)⁻¹)) hb]
  have hp' := mul_le_mul_of_nonneg_left hp (q.property.2 d).1
  have hn' := mul_le_mul_of_nonneg_left hn (sub_nonneg.mpr (q.property.2 d).2)
  unfold mixtureRaceWork
  dsimp [B, S] at hp' hn'
  nlinarith only [hp', hn']

end ThresholdHC.EntropyTailAssembly
