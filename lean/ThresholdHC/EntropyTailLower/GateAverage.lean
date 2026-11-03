import ThresholdHC.EntropyTailLower.GatedOutput
import ThresholdHC.EntropyTailLower.FiniteAverageProcedure

/-! A fixed number of masked runs reduces moments while charging every run.
Fair activation positivity remains an explicit premise; no original bias guarantee is asserted for the result. -/

noncomputable section
open MeasureTheory ProbabilityTheory Set Real
open scoped ENNReal
namespace ThresholdHC.EntropyTailLower
open ThresholdHC.Tier2 ThresholdHC.CriticalEntropy ThresholdHC.EntropyTailUpper ThresholdHC.BlindUpper

theorem gatedProcedure_mean_square_le {R : Type} [MeasurableSpace R]
    (ν : Measure R) [IsProbabilityMeasure ν] (p : unitInterval)
    (A : StoppedProcedure R ℝ) (hM : conditionalSecondMoment ν p A ≠ ∞) (M H : ℕ) :
    (conditionalMean ν p (gatedProcedure A M H))^2 ≤
      (ν.prod (tapeMeasure p)).real {z | (activationGate A M H).output z = true}*
        (conditionalSecondMoment ν p A).toReal := by
  have hL := (conditionalSecondMoment_finite_iff ν p A).mp hM
  have hY : MemLp A.output 2 (ν.prod (tapeMeasure p)) :=
    (memLp_map_measure_iff measurable_id.aestronglyMeasurable A.measurable_output.aemeasurable).mp hL
  have hm : MeasurableSet {z | (activationGate A M H).output z = true} :=
    measurableSet_eq_fun (activationGate A M H).measurable_output measurable_const
  have he : (∫ z, (A.output z)^2 ∂ν.prod (tapeMeasure p)) = (conditionalSecondMoment ν p A).toReal :=
    integral_eq_lintegral_of_nonneg_ae (ae_of_all _ (fun z => sq_nonneg _))
      (A.measurable_output.pow_const 2).aestronglyMeasurable
  change (∫ z, (gatedProcedure A M H).output z ∂ν.prod (tapeMeasure p))^2 ≤ _
  rw [gatedProcedure_output]
  simpa only [he] using masked_mean_square_le _ A.output hY _ hm

theorem averaged_gate_secondMoment_le {R : Type} [MeasurableSpace R]
    (ν : Measure R) [IsProbabilityMeasure ν] (p : unitInterval)
    (A : StoppedProcedure R ℝ) (hW : expectedStoppedProcedureWork ν p A ≠ ∞)
    (hM : conditionalSecondMoment ν p A ≠ ∞) (M H n : ℕ) :
    (conditionalSecondMoment (Measure.pi (fun _ : Fin (n+1) => ν)) p
      (averageProcedure (gatedProcedure A M H) n)).toReal ≤
      (1/((n:ℝ)+1)+(ν.prod (tapeMeasure p)).real {z | (activationGate A M H).output z = true})*
        (conditionalSecondMoment ν p A).toReal := by
  have hMw := gatedProcedure_secondMoment_le ν p A M H
  have hMf := ne_top_of_le_ne_top hM hMw
  have hWf : expectedStoppedProcedureWork ν p (gatedProcedure A M H) ≠ ∞ := hW
  have hav := averageProcedure_secondMoment_le ν p (gatedProcedure A M H) hWf hMf n
  have hm := ENNReal.toReal_mono hM hMw
  have hd := div_le_div_of_nonneg_right hm (by positivity : (0:ℝ) ≤ (n:ℝ)+1)
  have hmean := gatedProcedure_mean_square_le ν p A hM M H
  calc
    _ ≤ _ := hav
    _ ≤ (conditionalSecondMoment ν p A).toReal/((n:ℝ)+1)+
        (ν.prod (tapeMeasure p)).real {z | (activationGate A M H).output z = true}*
          (conditionalSecondMoment ν p A).toReal := add_le_add hd hmean
    _ = _ := by ring

def gateBatchCount (q : ℝ) : ℕ := ⌈q⁻¹⌉₊

theorem gateBatchCount_bounds (q : ℝ) (hq : 0 < q) (hq1 : q ≤ 1) :
    0 < gateBatchCount q ∧ (gateBatchCount q:ℝ) ≤ 2/q ∧ 1/(gateBatchCount q:ℝ) ≤ q := by
  have hlow : q⁻¹ ≤ (gateBatchCount q:ℝ) := Nat.le_ceil _
  have hhigh : (gateBatchCount q:ℝ) < q⁻¹+1 := Nat.ceil_lt_add_one (inv_nonneg.mpr hq.le)
  have hp : 0 < (gateBatchCount q:ℝ) := (inv_pos.mpr hq).trans_le hlow
  have hmul := mul_le_mul_of_nonneg_right hhigh.le hq.le
  rw [add_mul,inv_mul_cancel₀ hq.ne',one_mul] at hmul
  have hl := mul_le_mul_of_nonneg_right hlow hq.le
  rw [inv_mul_cancel₀ hq.ne'] at hl
  exact ⟨by exact_mod_cast hp,(le_div_iff₀ hq).mpr (by linarith),
    (div_le_iff₀ hp).mpr (by nlinarith only [hl])⟩

def gateAverage {R : Type} [MeasurableSpace R]
    (A : StoppedProcedure R ℝ) (M H : ℕ) (q : ℝ) :
    StoppedProcedure (Fin ((gateBatchCount q-1)+1) → R) ℝ :=
  averageProcedure (gatedProcedure A M H) (gateBatchCount q-1)

theorem gateAverage_work_le {R : Type} [MeasurableSpace R]
    (ν : Measure R) [IsProbabilityMeasure ν] (p : unitInterval)
    (A : StoppedProcedure R ℝ) (hW : expectedStoppedProcedureWork ν p A ≠ ∞)
    (M H : ℕ) (q : ℝ) (hq : 0 < q) (hq1 : q ≤ 1) :
    expectedStoppedProcedureWork (Measure.pi (fun _ : Fin ((gateBatchCount q-1)+1) => ν)) p
      (gateAverage A M H q) ≤ ENNReal.ofReal (2/q)*expectedStoppedProcedureWork ν p A := by
  obtain ⟨hp,hn,_⟩ := gateBatchCount_bounds q hq hq1
  have he : (gateBatchCount q-1)+1 = gateBatchCount q := Nat.sub_add_cancel hp
  have hWf : expectedStoppedProcedureWork ν p (gatedProcedure A M H) ≠ ∞ := hW
  rw [gateAverage,averageProcedure_work ν p _ hWf, gatedProcedure_work]
  have hcast : ((gateBatchCount q-1:ℕ):ℝ≥0∞)+1 = (gateBatchCount q:ℝ≥0∞) := by exact_mod_cast he
  rw [hcast]
  apply mul_le_mul' _ le_rfl
  simpa only [ENNReal.ofReal_natCast] using ENNReal.ofReal_le_ofReal hn

theorem gateAverage_secondMoment_le {R : Type} [MeasurableSpace R]
    (ν : Measure R) [IsProbabilityMeasure ν] (p : unitInterval)
    (A : StoppedProcedure R ℝ) (hW : expectedStoppedProcedureWork ν p A ≠ ∞)
    (hM : conditionalSecondMoment ν p A ≠ ∞) (M H : ℕ) (q C : ℝ)
    (hq : 0 < q) (hq1 : q ≤ 1)
    (hprob : (ν.prod (tapeMeasure p)).real {z | (activationGate A M H).output z = true} ≤ C*q) :
    conditionalSecondMoment (Measure.pi (fun _ : Fin ((gateBatchCount q-1)+1) => ν)) p
      (gateAverage A M H q) ≤ ENNReal.ofReal ((1+C)*q)*conditionalSecondMoment ν p A := by
  obtain ⟨hp,_,hn⟩ := gateBatchCount_bounds q hq hq1
  have he : (gateBatchCount q-1)+1 = gateBatchCount q := Nat.sub_add_cancel hp
  have hcast : ((gateBatchCount q-1:ℕ):ℝ)+1 = (gateBatchCount q:ℝ) := by exact_mod_cast he
  have hMw := gatedProcedure_secondMoment_le ν p A M H
  have hMf := ne_top_of_le_ne_top hM hMw
  have hWf : expectedStoppedProcedureWork ν p (gatedProcedure A M H) ≠ ∞ := hW
  have hav := averaged_gate_secondMoment_le ν p A hW hM M H (gateBatchCount q-1)
  rw [hcast] at hav
  have hcq : 0 ≤ C*q := measureReal_nonneg.trans hprob
  have hC : 0 ≤ (1+C)*q := by nlinarith
  have hcoef : 1/(gateBatchCount q:ℝ)+
      (ν.prod (tapeMeasure p)).real {z | (activationGate A M H).output z = true} ≤ (1+C)*q := by
    nlinarith only [hn,hprob]
  have hr := hav.trans (mul_le_mul_of_nonneg_right hcoef ENNReal.toReal_nonneg)
  apply (ENNReal.toReal_le_toReal
    (averageProcedure_secondMoment_finite ν p (gatedProcedure A M H) hWf hMf _)
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hM)).mp
  simpa only [ENNReal.toReal_mul,ENNReal.toReal_ofReal hC] using hr

def fairActivation {R E : Type} [MeasurableSpace R] [MeasurableSpace E]
    (ν : Measure R) (A : StoppedProcedure R E) (a : ℝ) : ℝ :=
  (ν.prod (tapeMeasure ⟨1/2,by norm_num⟩)).real
    {z | (activationGate A ⌈(a^2)⁻¹⌉₊ ⌈a⁻¹⌉₊).output z = true}

theorem activationGate_probability_real_le {R E : Type} [MeasurableSpace R] [MeasurableSpace E]
    (ν : Measure R) [IsProbabilityMeasure ν] (A : StoppedProcedure R E)
    (a : ℝ) (ha : 0 < a) (ha4 : a ≤ 1/4)
    (p : unitInterval) (hp : |(p:ℝ)-1/2| ≤ a) :
    (ν.prod (tapeMeasure p)).real {z | (activationGate A ⌈(a^2)⁻¹⌉₊ ⌈a⁻¹⌉₊).output z = true} ≤
      exp 12*fairActivation ν A a := by
  have h := (activationGate_probability_comparison ν A a ha ha4 p hp).2
  have hr := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _)) h
  simpa only [ENNReal.toReal_mul,ENNReal.toReal_ofReal (exp_pos 12).le,measureReal_def,fairActivation] using hr

theorem scaled_gateAverage_secondMoment_le {R : Type} [MeasurableSpace R]
    (ν : Measure R) [IsProbabilityMeasure ν] (A : StoppedProcedure R ℝ)
    (a : ℝ) (ha : 0 < a) (ha4 : a ≤ 1/4) (hq : 0 < fairActivation ν A a)
    (p : unitInterval) (hp : |(p:ℝ)-1/2| ≤ a)
    (hW : expectedStoppedProcedureWork ν p A ≠ ∞) (hM : conditionalSecondMoment ν p A ≠ ∞) :
    conditionalSecondMoment (Measure.pi (fun _ : Fin ((gateBatchCount (fairActivation ν A a)-1)+1) => ν)) p
      (gateAverage A ⌈(a^2)⁻¹⌉₊ ⌈a⁻¹⌉₊ (fairActivation ν A a)) ≤
      ENNReal.ofReal ((1+exp 12)*fairActivation ν A a)*conditionalSecondMoment ν p A :=
  gateAverage_secondMoment_le ν p A hW hM _ _ _ _ hq measureReal_le_one
    (activationGate_probability_real_le ν A a ha ha4 p hp)

end ThresholdHC.EntropyTailLower
