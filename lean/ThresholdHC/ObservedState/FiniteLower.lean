import ThresholdHC.ObservedState.Information
import ThresholdHC.ObservedState.Testing

noncomputable section
open MeasureTheory InformationTheory
open scoped ENNReal
namespace ThresholdHC.ObservedState
open ThresholdHC ThresholdHC.Tier3 ThresholdHC.Tier6

def UniformConfidence {m : ℕ} {R : Type} [MeasurableSpace R]
    (A : Estimator m R) (d : Fin m → Gap) (w : Fin m → ℝ) (r δ : ℝ) : Prop :=
  ∀ s, modelLaw A d s {z | r < |A.output z - target w s|} ≤ ENNReal.ofReal δ

theorem small_weights_concentrate {m : ℕ} (w : Fin m → ℝ) (q : Fin m → unitInterval)
    {Δ δ : ℝ} (hΔ : 0 < Δ) (hw : (∑ i, (w i) ^ 2) ≤ δ * Δ ^ 2 / 16) :
    (signLaw q) {s | Δ / 8 < |target w s - ∑ i, w i * (q i : ℝ)|} ≤ ENNReal.ofReal δ := by
  apply (target_concentration q w (div_pos hΔ (by norm_num))).trans
  apply ENNReal.ofReal_le_ofReal
  apply (div_le_iff₀ (by positivity : 0 < 4 * (Δ / 8) ^ 2)).mpr
  nlinarith

/-- Exact finite-cell testing lower bound for deterministic sign targets.
The product priors and the concentration reduction are proved inside this theorem. -/
theorem finite_confidence_lower {m : ℕ} {R : Type} [MeasurableSpace R]
    (A : Estimator m R) (d : Fin m → Gap) (w η : Fin m → ℝ)
    (qp qm : Fin m → unitInterval)
    (hp : ∀ i, (qp i : ℝ) = 1 / 2 + η i) (hm : ∀ i, (qm i : ℝ) = 1 / 2 - η i)
    {B h Δ δ : ℝ} (hB : 0 ≤ B) (hh : 0 < h) (hΔ : 0 < Δ)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1 / 8)
    (hη : ∀ i, 0 ≤ η i ∧ η i ≤ 1 / 8)
    (hd : ∀ i, (d i : ℝ) * η i ≤ h / 8)
    (hsep : (∑ i, w i * (qp i : ℝ)) - (∑ i, w i * (qm i : ℝ)) = Δ)
    (hweights : (∑ i, (w i) ^ 2) ≤ δ * Δ ^ 2 / 16)
    (hw : ∀ s, expectedWork A d s ≤ ENNReal.ofReal B)
    (hc : UniformConfidence A d w (Δ / 4) δ) :
    (225 / (128 * h ^ 2)) * klB (1 - 2 * δ) (2 * δ) ≤ B := by
  let a := ∑ i, w i * (qp i : ℝ)
  let b := ∑ i, w i * (qm i : ℝ)
  let E : Set (R × ProcessTape) := {z | (a + b) / 2 < A.output z}
  have hE : MeasurableSet E := measurableSet_lt measurable_const A.output_measurable
  have hpriorP := small_weights_concentrate w qp hΔ hweights
  have hpriorQ := small_weights_concentrate w qm hΔ hweights
  have hP : bayesLaw A d qp Eᶜ ≤ ENNReal.ofReal (2 * δ) := by
    have he := bayes_event_bound A d qp Eᶜ {s | Δ / 8 < |target w s - a|} (by
      intro s hs
      apply (measure_mono (t := {z | Δ / 4 < |A.output z - target w s|}) ?_).trans (hc s)
      intro z hz
      have hs' : |target w s - a| ≤ Δ / 8 := le_of_not_gt hs
      have hz' : A.output z ≤ (a + b) / 2 := le_of_not_gt hz
      have hmean : a - b = Δ := hsep
      have ha := le_abs_self (a - target w s)
      rw [abs_sub_comm a (target w s)] at ha
      have hf := neg_le_abs (A.output z - target w s)
      change Δ / 4 < |A.output z - target w s|
      linarith)
    apply he.trans
    calc
      _ ≤ ENNReal.ofReal δ + ENNReal.ofReal δ := add_le_add le_rfl hpriorP
      _ = _ := by rw [← ENNReal.ofReal_add hδ.le hδ.le]; congr 1; ring
  have hQ : bayesLaw A d qm E ≤ ENNReal.ofReal (2 * δ) := by
    have he := bayes_event_bound A d qm E {s | Δ / 8 < |target w s - b|} (by
      intro s hs
      apply (measure_mono (t := {z | Δ / 4 < |A.output z - target w s|}) ?_).trans (hc s)
      intro z hz
      have hs' : |target w s - b| ≤ Δ / 8 := le_of_not_gt hs
      have hz' : (a + b) / 2 < A.output z := hz
      have hmean : a - b = Δ := hsep
      have ha := le_abs_self (target w s - b)
      have hf := le_abs_self (A.output z - target w s)
      change Δ / 4 < |A.output z - target w s|
      linarith)
    apply he.trans
    calc
      _ ≤ ENNReal.ofReal δ + ENNReal.ofReal δ := add_le_add le_rfl hpriorQ
      _ = _ := by rw [← ENNReal.ofReal_add hδ.le hδ.le]; congr 1; ring
  have hPR : 1 - 2 * δ ≤ (bayesLaw A d qp).real E := by
    have hp' := ENNReal.toReal_le_of_le_ofReal (by positivity : 0 ≤ 2 * δ) hP
    change (bayesLaw A d qp).real Eᶜ ≤ 2 * δ at hp'
    rw [probReal_compl_eq_one_sub hE] at hp'
    linarith
  have hQR : (bayesLaw A d qm).real E ≤ 2 * δ :=
    ENNReal.toReal_le_of_le_ofReal (by positivity) hQ
  have htest := event_information_lower (bayesLaw A d qp) (bayesLaw A d qm) E hE
    (by positivity : 0 < 2 * δ) (by linarith : 2 * δ < 1 / 2) hPR hQR
  have hinfo := bayes_information_bound A d η qp qm hp hm hh hη hd hw
  have hcost := (ENNReal.ofReal_le_ofReal_iff
    (show 0 ≤ (128 / 225 : ℝ) * h ^ 2 * B by positivity)).mp (htest.trans hinfo)
  field_simp
  nlinarith

end ThresholdHC.ObservedState
