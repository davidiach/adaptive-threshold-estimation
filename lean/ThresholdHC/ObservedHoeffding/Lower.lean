import ThresholdHC.ObservedState.StateModel
import ThresholdHC.ObservedHoeffding.Hoeffding

/-! The finite-cell testing lower bound with the Hoeffding weight condition.

`confidence_lower_of_concentration` is `ThresholdHC.ObservedState.finite_confidence_lower`
with its second-moment concentration step replaced by the two prior concentration
bounds themselves; the rest of the proof is copied unchanged. The Hoeffding
condition `32 log(2/δ) ∑ w² ≤ Δ²` supplies those bounds (`hoeffding_concentrate`),
which gives `hoeffding_confidence_lower` and its cell-design form
`hoeffding_design_lower`. -/
noncomputable section
open MeasureTheory InformationTheory
open scoped ENNReal
namespace ThresholdHC.ObservedHoeffding
open ThresholdHC ThresholdHC.Tier3 ThresholdHC.Tier6 ThresholdHC.ObservedState

/-- The Hoeffding condition `32 log(2/δ) ∑ w² ≤ Δ²` makes the sign target
concentrate to radius `Δ/8` with failure probability `δ`. -/
theorem hoeffding_concentrate {I : Type} [Fintype I] (q : I → unitInterval) (w : I → ℝ)
    {Δ δ : ℝ} (hw : ∀ i, 0 ≤ w i) (hΔ : 0 < Δ) (hδ : 0 < δ) (hδ1 : δ < 2)
    (hcond : 32 * Real.log (2 / δ) * (∑ i, (w i) ^ 2) ≤ Δ ^ 2) :
    signLaw q {s | Δ / 8 < |target w s - ∑ i, w i * (q i : ℝ)|} ≤ ENNReal.ofReal δ := by
  have hlog : 0 < Real.log (2 / δ) := Real.log_pos (by rw [lt_div_iff₀ hδ]; linarith)
  have hv : 0 < Δ ^ 2 / (32 * Real.log (2 / δ)) := by positivity
  have hs : (∑ i, (w i) ^ 2) ≤ Δ ^ 2 / (32 * Real.log (2 / δ)) := by
    rw [le_div_iff₀ (by positivity)]
    linarith
  apply (weighted_hoeffding q w hw hv hs (by positivity : 0 ≤ Δ / 8)).trans
  apply ENNReal.ofReal_le_ofReal
  have he : -2 * (Δ / 8) ^ 2 / (Δ ^ 2 / (32 * Real.log (2 / δ))) = -Real.log (2 / δ) := by
    field_simp
    ring
  rw [he, Real.exp_neg, Real.exp_log (by positivity), inv_div]
  linarith

/-- `finite_confidence_lower` with the concentration of the sign target under both
priors as hypotheses. The proof is that of `finite_confidence_lower`. -/
theorem confidence_lower_of_concentration {m : ℕ} {R : Type} [MeasurableSpace R]
    (A : Estimator m R) (d : Fin m → Gap) (w η : Fin m → ℝ)
    (qp qm : Fin m → unitInterval)
    (hp : ∀ i, (qp i : ℝ) = 1 / 2 + η i) (hm : ∀ i, (qm i : ℝ) = 1 / 2 - η i)
    {B h Δ δ : ℝ} (hB : 0 ≤ B) (hh : 0 < h) (hΔ : 0 < Δ)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1 / 8)
    (hη : ∀ i, 0 ≤ η i ∧ η i ≤ 1 / 8)
    (hd : ∀ i, (d i : ℝ) * η i ≤ h / 8)
    (hsep : (∑ i, w i * (qp i : ℝ)) - (∑ i, w i * (qm i : ℝ)) = Δ)
    (hpriorP : signLaw qp {s | Δ / 8 < |target w s - ∑ i, w i * (qp i : ℝ)|} ≤ ENNReal.ofReal δ)
    (hpriorQ : signLaw qm {s | Δ / 8 < |target w s - ∑ i, w i * (qm i : ℝ)|} ≤ ENNReal.ofReal δ)
    (hw : ∀ s, ThresholdHC.ObservedState.expectedWork A d s ≤ ENNReal.ofReal B)
    (hc : UniformConfidence A d w (Δ / 4) δ) :
    (225 / (128 * h ^ 2)) * klB (1 - 2 * δ) (2 * δ) ≤ B := by
  let a := ∑ i, w i * (qp i : ℝ)
  let b := ∑ i, w i * (qm i : ℝ)
  let E : Set (R × ProcessTape) := {z | (a + b) / 2 < A.output z}
  have hE : MeasurableSet E := measurableSet_lt measurable_const A.output_measurable
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

/-- `finite_confidence_lower` with `0 ≤ w i` and the Hoeffding weight condition
`32 log(2/δ) ∑ w² ≤ Δ²` in place of `∑ w² ≤ δΔ²/16`. -/
theorem hoeffding_confidence_lower {m : ℕ} {R : Type} [MeasurableSpace R]
    (A : Estimator m R) (d : Fin m → Gap) (w η : Fin m → ℝ)
    (qp qm : Fin m → unitInterval)
    (hp : ∀ i, (qp i : ℝ) = 1 / 2 + η i) (hm : ∀ i, (qm i : ℝ) = 1 / 2 - η i)
    {B h Δ δ : ℝ} (hB : 0 ≤ B) (hh : 0 < h) (hΔ : 0 < Δ)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1 / 8)
    (hη : ∀ i, 0 ≤ η i ∧ η i ≤ 1 / 8)
    (hd : ∀ i, (d i : ℝ) * η i ≤ h / 8)
    (hsep : (∑ i, w i * (qp i : ℝ)) - (∑ i, w i * (qm i : ℝ)) = Δ)
    (hwn : ∀ i, 0 ≤ w i) (hcond : 32 * Real.log (2 / δ) * (∑ i, (w i) ^ 2) ≤ Δ ^ 2)
    (hw : ∀ s, ThresholdHC.ObservedState.expectedWork A d s ≤ ENNReal.ofReal B)
    (hc : UniformConfidence A d w (Δ / 4) δ) :
    (225 / (128 * h ^ 2)) * klB (1 - 2 * δ) (2 * δ) ≤ B :=
  confidence_lower_of_concentration A d w η qp qm hp hm hB hh hΔ hδ hδ1 hη hd hsep
    (hoeffding_concentrate qp w hwn hΔ hδ (by linarith) hcond)
    (hoeffding_concentrate qm w hwn hΔ hδ (by linarith) hcond) hw hc

/-- Every measurable cell partition has positive separation. -/
theorem cellDelta_pos (h : Gap) {N : ℕ} (cap : Fin N → Gap) (cell : unitInterval → Fin N)
    (hc : Measurable cell) : 0 < cellDelta cap cell h := by
  have hsum := cellWeight_sum cell hc
  obtain ⟨i, _, hi⟩ := Finset.exists_ne_zero_of_sum_ne_zero (by rw [hsum]; norm_num :
    (∑ i, cellWeight cell i) ≠ 0)
  have hpos : 0 < cellWeight cell i := lt_of_le_of_ne measureReal_nonneg (Ne.symm hi)
  unfold cellDelta
  apply mul_pos (by norm_num)
  apply Finset.sum_pos' (fun j _ => mul_nonneg measureReal_nonneg
    (clippedGap_nonneg h.property.1.le _))
  exact ⟨i, Finset.mem_univ i, mul_pos hpos (clippedGap_pos h.property.1 _)⟩

/-- The design-level lower bound: every finite measurable cell design whose squared
cell lengths meet the Hoeffding condition forces the testing lower bound. The proof
is that of `design_confidence_lower` for an explicit design. -/
theorem hoeffding_design_lower (h : Gap) {N : ℕ} (cap : Fin N → Gap)
    (cell : unitInterval → Fin N) (hcell : Measurable cell) {δ : ℝ} (hδ : 0 < δ)
    (hd : δ ≤ 1 / 8)
    (hcond : 32 * Real.log (2 / δ) * (∑ i, (cellWeight cell i) ^ 2) ≤ (cellDelta cap cell h) ^ 2)
    {R : Type} [MeasurableSpace R] (A : StateEstimator R) {B : ℝ} (hB : 0 ≤ B)
    (hw : ∀ s, (∫⁻ z, totalProcessWork z.2 ∂stateLaw A cap cell hcell s) ≤ ENNReal.ofReal B)
    (hc : ∀ s, stateLaw A cap cell hcell s
      {z | cellDelta cap cell h / 4 < |A.output z - stateTarget cell s|} ≤ ENNReal.ofReal δ) :
    (225 / (128 * (h : ℝ) ^ 2)) * klB (1 - 2 * δ) (2 * δ) ≤ B := by
  let hv := hard_pair_validity (h : ℝ) h.property.1
  let qp (i : Fin N) : unitInterval := ⟨hardPlus h (cap i), (hv.2.2.2 (cap i)).2.2.1⟩
  let qm (i : Fin N) : unitInterval := ⟨hardMinus h (cap i), (hv.2.2.2 (cap i)).2.2.2⟩
  have hsep : (∑ i, cellWeight cell i * (qp i : ℝ)) -
      (∑ i, cellWeight cell i * (qm i : ℝ)) = cellDelta cap cell h := by
    rw [← Finset.sum_sub_distrib]
    unfold cellDelta
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    dsimp [qp, qm, hardPlus, hardMinus, hardEta]
    ring
  apply hoeffding_confidence_lower (onCells A cell hcell) cap (cellWeight cell)
    (fun i => hardEta h (cap i)) qp qm (fun _ => rfl) (fun _ => rfl)
    hB h.property.1 (cellDelta_pos h cap cell hcell) hδ hd
    (fun i => hardEta_bounds h.property.1.le (cap i)) (fun i => gap_mul_hardEta_le (cap i))
    hsep (fun _ => measureReal_nonneg) hcond hw
  intro s
  simpa only [stateTarget_eq cell hcell s, stateLaw, onCells] using hc s

end ThresholdHC.ObservedHoeffding
