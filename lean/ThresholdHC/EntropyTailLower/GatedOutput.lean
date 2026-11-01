import ThresholdHC.EntropyTailLower.GateMeasure
import ThresholdHC.CriticalEntropy.RepeatedModel
import ThresholdHC.CriticalEntropy.UniformCoin

/-! Observable masking at the original stopping time, with no extra flips.
The masked mean is controlled by activation probability and the original second moment. -/

noncomputable section
open MeasureTheory ProbabilityTheory Set Real
open scoped ENNReal
namespace ThresholdHC.EntropyTailLower
open ThresholdHC.Tier2 ThresholdHC.CriticalEntropy ThresholdHC.EntropyTailUpper ThresholdHC.BlindUpper

theorem stopped_output_prefix_eq {R E : Type} [MeasurableSpace R] [MeasurableSpace E]
    (A : StoppedProcedure R E) (n : ℕ) (r : R) (ω ω' : ℕ → Bool)
    (hs : A.stop (r,ω) ≤ n) (he : tapePrefix n ω = tapePrefix n ω') :
    A.output (r,ω) = A.output (r,ω') := by
  have hf : A.stop (r,ω) ≠ ⊤ := ne_top_of_le_ne_top (by simp) hs
  let k := (A.stop (r,ω)).toNat
  have hk : A.stop (r,ω) = (k:ℕ∞) := (ENat.natCast_toNat hf).symm
  have hkn : k ≤ n := by simpa [k] using ENat.toNat_le_toNat hs (by simp)
  have hp := prefix_eq_restrict he hkn
  have hk' : A.stop (r,ω') = (k:ℕ∞) := by
    apply (A.stop_observable k (r,ω')).mp
    change (r,tapePrefix k ω') ∈ A.stopPrefix k
    rw [← hp]
    exact (A.stop_observable k (r,ω)).mpr hk
  rw [A.output_observable k (r,ω) hk,A.output_observable k (r,ω') hk']
  change A.outputPrefix k (r,tapePrefix k ω) = A.outputPrefix k (r,tapePrefix k ω')
  rw [hp]

/-- Observe a procedure that has already stopped without charging extra flips. -/
def observedPair {R E F : Type} [MeasurableSpace R] [MeasurableSpace E] [MeasurableSpace F]
    (A : StoppedProcedure R E) (B : StoppedProcedure R F) (hB : ∀ z, B.stop z ≤ A.stop z) :
    StoppedProcedure R (E × F) where
  stop := A.stop
  output := fun z => (A.output z,B.output z)
  measurable_stop := A.measurable_stop
  measurable_output := A.measurable_output.prodMk B.measurable_output
  stopPrefix := A.stopPrefix
  measurable_stopPrefix := A.measurable_stopPrefix
  stop_observable := A.stop_observable
  outputPrefix := fun n z => (A.outputPrefix n z,B.output (z.1,completePrefix n z.2))
  measurable_outputPrefix := fun n => (A.measurable_outputPrefix n).prodMk
    (B.measurable_output.comp (measurable_fst.prodMk ((measurable_completePrefix n).comp measurable_snd)))
  output_observable := by
    intro n z hn
    apply Prod.ext (A.output_observable n z hn)
    exact stopped_output_prefix_eq B n z.1 z.2 (completePrefix n (tapePrefix n z.2))
      ((hB z).trans_eq hn) (tapePrefix_completePrefix n _).symm

def gatedProcedure {R : Type} [MeasurableSpace R]
    (A : StoppedProcedure R ℝ) (M H : ℕ) : StoppedProcedure R ℝ :=
  postprocessProcedure (observedPair A (activationGate A M H) (fun z => (activationGate_stop_le A M H z).1))
    (fun z => if z.2 = true then z.1 else 0)
    (measurable_fst.ite (measurableSet_eq_fun measurable_snd measurable_const) measurable_const)

theorem gatedProcedure_output {R : Type} [MeasurableSpace R]
    (A : StoppedProcedure R ℝ) (M H : ℕ) :
    (gatedProcedure A M H).output = {z | (activationGate A M H).output z = true}.indicator A.output := by
  funext z
  simp [gatedProcedure,postprocessProcedure,observedPair,Set.indicator]

theorem gatedProcedure_work {R : Type} [MeasurableSpace R]
    (ν : Measure R) (p : unitInterval) (A : StoppedProcedure R ℝ) (M H : ℕ) :
    expectedStoppedProcedureWork ν p (gatedProcedure A M H) = expectedStoppedProcedureWork ν p A := rfl

theorem gatedProcedure_secondMoment_le {R : Type} [MeasurableSpace R]
    (ν : Measure R) (p : unitInterval) (A : StoppedProcedure R ℝ) (M H : ℕ) :
    conditionalSecondMoment ν p (gatedProcedure A M H) ≤ conditionalSecondMoment ν p A := by
  apply lintegral_mono
  intro z
  apply ENNReal.ofReal_le_ofReal
  change (if (activationGate A M H).output z = true then A.output z else 0)^2 ≤ (A.output z)^2
  split_ifs <;> nlinarith [sq_nonneg (A.output z)]

theorem masked_mean_square_le {X : Type} [MeasurableSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ] (Y : X → ℝ) (hY : MemLp Y 2 μ)
    (S : Set X) (hS : MeasurableSet S) :
    (∫ x, S.indicator Y x ∂μ)^2 ≤ μ.real S*(∫ x, (Y x)^2 ∂μ) := by
  rw [integral_indicator hS]
  by_cases hs : μ S = 0
  · rw [Measure.restrict_eq_zero.mpr hs]
    simp [measureReal_def,hs]
  have hm : 0 < μ.real S := ENNReal.toReal_pos hs (measure_ne_top _ _)
  let c := (∫ x in S, Y x ∂μ)/μ.real S
  have hc : c*μ.real S = ∫ x in S, Y x ∂μ := div_mul_cancel₀ _ hm.ne'
  have hi := (hY.integrable (by norm_num)).integrableOn (s := S)
  have hsq := hY.integrable_sq.integrableOn (s := S)
  have hz : 0 ≤ ∫ x in S, (Y x-c)^2 ∂μ := integral_nonneg (fun x => sq_nonneg _)
  have he : (∫ x in S, (Y x-c)^2 ∂μ) =
      (∫ x in S, (Y x)^2 ∂μ)-2*c*(∫ x in S, Y x ∂μ)+c^2*μ.real S := by
    calc
      _ = ∫ x in S, ((Y x)^2-(2*c)*Y x+c^2) ∂μ := by
        apply integral_congr_ae
        exact ae_of_all _ (fun x => by ring)
      _ = _ := by
        have hscale : Integrable (fun x => (2*c)*Y x) (μ.restrict S) := hi.const_mul (2*c)
        have hadd := integral_add (hsq.sub hscale) (integrable_const (c^2))
        simp only [Pi.sub_apply] at hadd
        rw [hadd,integral_sub hsq hscale,integral_const_mul]
        simp [mul_comm]
  rw [he,← hc] at hz
  have hb : c^2*μ.real S ≤ ∫ x in S, (Y x)^2 ∂μ := by nlinarith
  calc
    _ = μ.real S*(c^2*μ.real S) := by rw [← hc]; ring
    _ ≤ μ.real S*(∫ x in S, (Y x)^2 ∂μ) := mul_le_mul_of_nonneg_left hb hm.le
    _ ≤ _ := mul_le_mul_of_nonneg_left (setIntegral_le_integral hY.integrable_sq
      (ae_of_all _ (fun x => sq_nonneg _))) hm.le

end ThresholdHC.EntropyTailLower
