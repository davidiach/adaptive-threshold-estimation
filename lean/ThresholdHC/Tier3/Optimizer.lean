import ThresholdHC.Proofs.Tier2.RareEvent
import ThresholdHC.Tier3.OptimizerModel

/-!
The clipped inverse-square allocation solves the rare-event variational problem
for arbitrary probability laws. Dominated convergence and the intermediate
value theorem give its cutoff; a strict scalar comparison proves uniqueness.
The supporting-line inequality from Tier 2 integrates without any inverse
moment assumption. The remaining branch saturates the budget, and the final
identity splits the attained value at the two cutoffs, including atoms there.
-/

noncomputable section
open MeasureTheory Filter Set Real
open scoped Topology

namespace ThresholdHC.Tier3

theorem allocation_nonneg (t d : ℝ) : 0 ≤ allocation t d :=
  le_min (by norm_num) (div_nonneg (sq_nonneg _) (sq_nonneg _))
theorem allocation_le_one (t d : ℝ) : allocation t d ≤ 1 := min_le_left _ _

theorem measurable_allocation {α : Type*} [MeasurableSpace α] {D : α → ℝ}
    (hD : Measurable D) (t : ℝ) : Measurable (fun x => allocation t (D x)) :=
  measurable_const.min (measurable_const.div (hD.pow_const 2))

theorem integrable_allocation {α : Type*} [MeasurableSpace α] {μ : Measure α}
    [IsFiniteMeasure μ] {D : α → ℝ} (hD : Measurable D) (t : ℝ) :
    Integrable (fun x => allocation t (D x)) μ := by
  apply (integrable_const (1:ℝ)).mono' (measurable_allocation hD t).aestronglyMeasurable
  filter_upwards [] with x
  rw [Real.norm_of_nonneg (allocation_nonneg _ _)]
  exact allocation_le_one _ _

theorem allocationMass_continuous {α : Type*} [MeasurableSpace α] {μ : Measure α}
    [IsFiniteMeasure μ] {D : α → ℝ} (hD : Measurable D) : Continuous (allocationMass μ D) := by
  apply continuous_iff_continuousAt.mpr
  intro t
  apply tendsto_integral_filter_of_dominated_convergence (fun _ => (1:ℝ))
  · exact Eventually.of_forall (fun s => (measurable_allocation hD s).aestronglyMeasurable)
  · exact Eventually.of_forall (fun s => ae_of_all _ (fun x => by
      rw [Real.norm_of_nonneg (allocation_nonneg _ _)]
      exact allocation_le_one _ _))
  · exact integrable_const _
  · exact ae_of_all _ (fun x =>
      (continuous_const.min ((continuous_id.pow 2).div_const ((D x)^2))).continuousAt)

theorem allocation_zero (d : ℝ) : allocation 0 d = 0 := by simp [allocation]
theorem allocation_eq_one {t d : ℝ} (hd : 0 < d) (hdt : d ≤ t) : allocation t d = 1 := by
  apply min_eq_left
  apply (le_div_iff₀ (sq_pos_of_pos hd)).2
  nlinarith

theorem allocationMass_zero {α : Type*} [MeasurableSpace α] (μ : Measure α) (D : α → ℝ) :
    allocationMass μ D 0 = 0 := by simp [allocationMass, allocation_zero]

theorem allocationMass_half {α : Type*} [MeasurableSpace α] {μ : Measure α}
    [IsProbabilityMeasure μ] {D : α → ℝ}
    (hD : ∀ᵐ x ∂μ, 0 < D x ∧ D x ≤ 1/2) : allocationMass μ D (1/2) = 1 := by
  unfold allocationMass
  calc
    _ = ∫ _, (1:ℝ) ∂μ := integral_congr_ae (hD.mono (fun x hx => allocation_eq_one hx.1 hx.2))
    _ = 1 := by simp

theorem cutoff_exists {α : Type*} [MeasurableSpace α] {μ : Measure α}
    [IsProbabilityMeasure μ] {D : α → ℝ} (hDmeas : Measurable D)
    (hD : ∀ᵐ x ∂μ, 0 < D x ∧ D x ≤ 1/2) {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ < 1) :
    ∃ t, 0 < t ∧ t < 1/2 ∧ allocationMass μ D t = ρ := by
  have hcont := allocationMass_continuous (μ:=μ) hDmeas
  have hmem : ρ ∈ Set.Icc (allocationMass μ D 0) (allocationMass μ D (1/2)) := by
    rw [allocationMass_zero, allocationMass_half hD]
    exact ⟨hρ.le, hρ1.le⟩
  obtain ⟨t, ht, heq⟩ := intermediate_value_Icc (by norm_num : (0:ℝ) ≤ 1/2) hcont.continuousOn hmem
  refine ⟨t, ?_, ?_, heq⟩
  · apply lt_of_le_of_ne ht.1
    intro he
    rw [← he, allocationMass_zero] at heq
    linarith
  · apply lt_of_le_of_ne ht.2
    intro he
    rw [he, allocationMass_half hD] at heq
    linarith

theorem allocation_mono {t s : ℝ} (ht : 0 ≤ t) (hts : t ≤ s) (d : ℝ) :
    allocation t d ≤ allocation s d := by
  apply min_le_min_left
  apply div_le_div_of_nonneg_right _ (sq_nonneg d)
  nlinarith

theorem allocation_strict_below_one {t s d : ℝ} (ht : 0 ≤ t) (hts : t < s)
    (hd : 0 < d) (hlt : allocation t d < 1) : allocation t d < allocation s d := by
  have hd2 : 0 < d^2 := sq_pos_of_pos hd
  have hratio : t^2/d^2 < 1 := by simpa [allocation, min_lt_iff] using hlt
  have hsq : t^2/d^2 < s^2/d^2 := (div_lt_div_iff_of_pos_right hd2).2 (by nlinarith)
  rw [allocation, min_eq_right hratio.le, allocation]
  exact lt_min hratio hsq

theorem cutoff_unique {α : Type*} [MeasurableSpace α] {μ : Measure α}
    [IsProbabilityMeasure μ] {D : α → ℝ} (hDmeas : Measurable D)
    (hD : ∀ᵐ x ∂μ, 0 < D x ∧ D x ≤ 1/2) {ρ t s : ℝ} (hρ1 : ρ < 1)
    (ht : 0 < t) (hs : 0 < s) (htρ : allocationMass μ D t = ρ)
    (hsρ : allocationMass μ D s = ρ) : t = s := by
  suffices hn : ∀ {t s : ℝ}, 0 < t → t < s → allocationMass μ D t = ρ →
      allocationMass μ D s = ρ → False by
    rcases lt_trichotomy t s with h | h | h
    · exact False.elim (hn ht h htρ hsρ)
    · exact h
    · exact False.elim (hn hs h hsρ htρ)
  intro t s ht hts htρ hsρ
  have hle : (fun x => allocation t (D x)) ≤ᵐ[μ] (fun x => allocation s (D x)) :=
    ae_of_all _ (fun x => allocation_mono ht.le hts.le _)
  have heq : (fun x => allocation t (D x)) =ᵐ[μ] (fun x => allocation s (D x)) :=
    (integral_eq_iff_of_ae_le (integrable_allocation hDmeas t)
      (integrable_allocation hDmeas s) hle).1 (htρ.trans hsρ.symm)
  have hone : (fun x => allocation t (D x)) =ᵐ[μ] (fun _ => (1:ℝ)) := by
    filter_upwards [hD, heq] with x hx he
    apply le_antisymm (allocation_le_one _ _)
    by_contra hn
    have hlt := allocation_strict_below_one ht.le hts hx.1 (not_le.mp hn)
    exact (ne_of_lt hlt) he
  have hm : allocationMass μ D t = 1 := by
    unfold allocationMass
    rw [integral_congr_ae hone]
    simp
  linarith

theorem integrable_feasible {α : Type*} [MeasurableSpace α] {μ : Measure α}
    [IsFiniteMeasure μ] {ρ : ℝ} {v : α → ℝ} (hv : FeasibleAllocation μ ρ v) :
    Integrable v μ := by
  apply (integrable_const (1:ℝ)).mono' hv.1.aestronglyMeasurable
  filter_upwards [hv.2.1] with x hx
  simpa only [Real.norm_of_nonneg hx.1] using hx.2

theorem objective_integrable {α : Type*} [MeasurableSpace α] {μ : Measure α}
    [IsFiniteMeasure μ] {D v : α → ℝ} {h : ℝ} (hDmeas : Measurable D)
    (hD : ∀ᵐ x ∂μ, 0 < D x) (hvmeas : Measurable v)
    (hv : ∀ᵐ x ∂μ, 0 ≤ v x ∧ v x ≤ 1) (hh : 0 ≤ h) :
    Integrable (fun x => min (v x) (h * Real.sqrt (v x) / D x)) μ := by
  apply (integrable_const (1:ℝ)).mono'
    (hvmeas.min ((measurable_const.mul hvmeas.sqrt).div hDmeas)).aestronglyMeasurable
  filter_upwards [hD, hv] with x hd hx
  have hn : 0 ≤ min (v x) (h * Real.sqrt (v x) / D x) :=
    le_min hx.1 (div_nonneg (mul_nonneg hh (Real.sqrt_nonneg _)) hd.le)
  change ‖min (v x) (h * Real.sqrt (v x) / D x)‖ ≤ 1
  rw [Real.norm_of_nonneg hn]
  exact (min_le_left _ _).trans hx.2

theorem allocation_feasible {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {D : α → ℝ} {ρ t : ℝ} (hD : Measurable D) (hm : allocationMass μ D t = ρ) :
    FeasibleAllocation μ ρ (fun x => allocation t (D x)) :=
  ⟨measurable_allocation hD t, ae_of_all _ (fun _x => ⟨allocation_nonneg _ _, allocation_le_one _ _⟩), hm.le⟩

theorem optimizer_below_cutoff {α : Type*} [MeasurableSpace α] {μ : Measure α}
    [IsProbabilityMeasure μ] {D : α → ℝ} (hDmeas : Measurable D)
    (hD : ∀ᵐ x ∂μ, 0 < D x) {ρ t h : ℝ} (hh : 0 < h) (hht : h < t)
    (hm : allocationMass μ D t = ρ) {v : α → ℝ} (hv : FeasibleAllocation μ ρ v) :
    rareObjective μ D h v ≤ rareObjective μ D h (fun x => allocation t (D x)) := by
  have ha := allocation_feasible hDmeas hm
  have hi := objective_integrable hDmeas hD hv.1 hv.2.1 hh.le
  have hai := objective_integrable hDmeas hD ha.1 ha.2.1 hh.le
  have hvai : Integrable (fun x => v x - allocation t (D x)) μ :=
    (integrable_feasible hv).sub (integrable_allocation hDmeas t)
  have hpenaltyInt : Integrable (fun x => (h/(2*t)) * (v x - allocation t (D x))) μ := hvai.const_mul _
  have hs := integral_mono_ae hi (hai.add hpenaltyInt) (by
    filter_upwards [hD, hv.2.1] with x hd hx
    exact ThresholdHC.Proofs.rare_supporting_line h t (D x) (v x) hh hht hd hx.1 hx.2)
  simp only [Pi.add_apply] at hs
  rw [integral_add hai hpenaltyInt, integral_const_mul,
    integral_sub (integrable_feasible hv) (integrable_allocation hDmeas t)] at hs
  change rareObjective μ D h v ≤ rareObjective μ D h (fun x => allocation t (D x)) +
    (h/(2*t)) * ((∫ x, v x ∂μ) - allocationMass μ D t) at hs
  rw [hm] at hs
  have hlambda : 0 ≤ h/(2*t) := by have : 0 < t := hh.trans hht; positivity
  have hp := mul_nonpos_of_nonneg_of_nonpos hlambda (sub_nonpos.mpr hv.2.2)
  linarith

theorem allocation_payoff_saturated {h t d : ℝ} (ht : 0 < t) (hth : t ≤ h) (hd : 0 < d) :
    min (allocation t d) (h * Real.sqrt (allocation t d) / d) = allocation t d := by
  apply min_eq_left
  by_cases hdt : d ≤ t
  · rw [allocation_eq_one hd hdt, Real.sqrt_one, mul_one]
    exact (le_div_iff₀ hd).2 (by linarith)
  · have htd : t < d := lt_of_not_ge hdt
    have hc : t^2/d^2 ≤ 1 := (div_le_iff₀ (sq_pos_of_pos hd)).2 (by nlinarith)
    rw [allocation, min_eq_right hc, Real.sqrt_div (sq_nonneg _),
      Real.sqrt_sq ht.le, Real.sqrt_sq hd.le]
    have heq : h*(t/d)/d = (h*t)/(d^2) := by field_simp
    rw [heq]
    apply div_le_div_of_nonneg_right _ (sq_nonneg d)
    nlinarith

theorem optimizer_saturation {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {D : α → ℝ} (hD : ∀ᵐ x ∂μ, 0 < D x) {ρ t h : ℝ} (ht : 0 < t) (hth : t ≤ h)
    (hm : allocationMass μ D t = ρ) :
    rareObjective μ D h (fun x => allocation t (D x)) = ρ := by
  rw [← hm]
  exact integral_congr_ae (hD.mono (fun x hx => allocation_payoff_saturated ht hth hx))

theorem optimizer_above_cutoff {α : Type*} [MeasurableSpace α] {μ : Measure α}
    [IsProbabilityMeasure μ] {D : α → ℝ} (hDmeas : Measurable D)
    (hD : ∀ᵐ x ∂μ, 0 < D x) {ρ t h : ℝ} (ht : 0 < t) (hth : t ≤ h)
    (hm : allocationMass μ D t = ρ) {v : α → ℝ} (hv : FeasibleAllocation μ ρ v) :
    rareObjective μ D h v ≤ rareObjective μ D h (fun x => allocation t (D x)) := by
  rw [optimizer_saturation hD ht hth hm]
  have hi := objective_integrable hDmeas hD hv.1 hv.2.1 (ht.le.trans hth)
  exact (integral_mono_ae hi (integrable_feasible hv) (ae_of_all _ (fun x => min_le_left _ _))).trans hv.2.2

theorem allocation_payoff_regions {h t d : ℝ} (hh : 0 < h) (hht : h < t) (hd : 0 < d) :
    min (allocation t d) (h * Real.sqrt (allocation t d) / d) =
      (if d ≤ h then 1 else 0) +
        h * (if h < d ∧ d ≤ t then d⁻¹ else 0) +
        h*t * (if t < d then (d⁻¹)^2 else 0) := by
  have ht : 0 < t := hh.trans hht
  by_cases hdh : d ≤ h
  · have hdt : d ≤ t := hdh.trans hht.le
    have hn1 : ¬h < d := not_lt.mpr hdh
    have hn2 : ¬t < d := not_lt.mpr hdt
    rw [allocation_eq_one hd hdt, Real.sqrt_one, mul_one,
      min_eq_left ((le_div_iff₀ hd).2 (by linarith))]
    simp [hdh, hn1, hn2]
  · have hhd : h < d := lt_of_not_ge hdh
    by_cases hdt : d ≤ t
    · have hn2 : ¬t < d := not_lt.mpr hdt
      rw [allocation_eq_one hd hdt, Real.sqrt_one, mul_one,
        min_eq_right ((div_le_one hd).2 hhd.le)]
      simp [hdh, hhd, hdt, hn2, div_eq_mul_inv]
    · have htd : t < d := lt_of_not_ge hdt
      have hc : t^2/d^2 ≤ 1 := (div_le_iff₀ (sq_pos_of_pos hd)).2 (by nlinarith)
      have hb : h*(t/d)/d ≤ t^2/d^2 := by
        have heq : h*(t/d)/d = (h*t)/(d^2) := by field_simp
        rw [heq]
        apply div_le_div_of_nonneg_right _ (sq_nonneg d)
        nlinarith
      rw [allocation, min_eq_right hc, Real.sqrt_div (sq_nonneg _),
        Real.sqrt_sq ht.le, Real.sqrt_sq hd.le, min_eq_right hb]
      simp only [hdh, hdt, htd, and_false, ↓reduceIte, mul_zero, zero_add]
      field_simp

theorem integrable_indicator_inv {α : Type*} [MeasurableSpace α] {μ : Measure α}
    [IsFiniteMeasure μ] {D : α → ℝ} (hD : Measurable D) {s : Set α}
    (hs : MeasurableSet s) {c : ℝ} (hc : 0 < c) (hsc : ∀ x ∈ s, c < D x) :
    Integrable (s.indicator (fun x => (D x)⁻¹)) μ := by
  apply (integrable_const c⁻¹).mono' (hD.inv.indicator hs).aestronglyMeasurable
  filter_upwards [] with x
  by_cases hx : x ∈ s
  · rw [Set.indicator_of_mem hx]
    change ‖(D x)⁻¹‖ ≤ c⁻¹
    rw [Real.norm_of_nonneg (inv_nonneg.mpr (hc.trans (hsc x hx)).le)]
    exact inv_anti₀ hc (hsc x hx).le
  · rw [Set.indicator_of_notMem hx, norm_zero]
    exact inv_nonneg.mpr hc.le

theorem integrable_indicator_inv_sq {α : Type*} [MeasurableSpace α] {μ : Measure α}
    [IsFiniteMeasure μ] {D : α → ℝ} (hD : Measurable D) {s : Set α}
    (hs : MeasurableSet s) {c : ℝ} (hc : 0 < c) (hsc : ∀ x ∈ s, c < D x) :
    Integrable (s.indicator (fun x => ((D x)⁻¹)^2)) μ := by
  apply (integrable_const ((c⁻¹)^2)).mono' ((hD.inv.pow_const 2).indicator hs).aestronglyMeasurable
  filter_upwards [] with x
  by_cases hx : x ∈ s
  · rw [Set.indicator_of_mem hx]
    change ‖((D x)⁻¹)^2‖ ≤ (c⁻¹)^2
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    exact pow_le_pow_left₀ (inv_nonneg.mpr (hc.trans (hsc x hx)).le) (inv_anti₀ hc (hsc x hx).le) 2
  · rw [Set.indicator_of_notMem hx, norm_zero]
    exact sq_nonneg _

theorem optimizer_formula {α : Type*} [MeasurableSpace α] {μ : Measure α}
    [IsProbabilityMeasure μ] {D : α → ℝ} (hDmeas : Measurable D)
    (hD : ∀ᵐ x ∂μ, 0 < D x) {t h : ℝ} (hh : 0 < h) (hht : h < t) :
    rareObjective μ D h (fun x => allocation t (D x)) =
      μ.real {x | D x ≤ h} + h * (∫ x in {x | h < D x ∧ D x ≤ t}, (D x)⁻¹ ∂μ) +
        h*t * (∫ x in {x | t < D x}, ((D x)⁻¹)^2 ∂μ) := by
  classical
  let A := {x | D x ≤ h}
  let B := {x | h < D x ∧ D x ≤ t}
  let C := {x | t < D x}
  have hA : MeasurableSet A := measurableSet_le hDmeas measurable_const
  have hB : MeasurableSet B := (measurableSet_lt measurable_const hDmeas).inter
    (measurableSet_le hDmeas measurable_const)
  have hC : MeasurableSet C := measurableSet_lt measurable_const hDmeas
  have hiA : Integrable (A.indicator (fun _ => (1:ℝ))) μ := (integrable_const _).indicator hA
  have hiB : Integrable (B.indicator (fun x => (D x)⁻¹)) μ :=
    integrable_indicator_inv hDmeas hB hh (fun x hx => hx.1)
  have hiC : Integrable (C.indicator (fun x => ((D x)⁻¹)^2)) μ :=
    integrable_indicator_inv_sq hDmeas hC (hh.trans hht) (fun x hx => hx)
  have heq : rareObjective μ D h (fun x => allocation t (D x)) =
      ∫ x, (A.indicator (fun _ => (1:ℝ))) x + h*(B.indicator (fun x => (D x)⁻¹)) x +
        h*t*(C.indicator (fun x => ((D x)⁻¹)^2)) x ∂μ := by
    apply integral_congr_ae
    filter_upwards [hD] with x hx
    simpa only [A, B, C, Set.indicator, Set.mem_ofPred_eq] using allocation_payoff_regions hh hht hx
  have hiBh : Integrable (fun x => h * (B.indicator (fun x => (D x)⁻¹)) x) μ := hiB.const_mul h
  have hiCt : Integrable (fun x => (h*t) * (C.indicator (fun x => ((D x)⁻¹)^2)) x) μ := hiC.const_mul _
  have hiAB : Integrable (fun x => (A.indicator (fun _ => (1:ℝ))) x +
      h*(B.indicator (fun x => (D x)⁻¹)) x) μ := hiA.add hiBh
  rw [heq, integral_add hiAB hiCt,
    integral_add hiA hiBh, integral_const_mul, integral_const_mul,
    integral_indicator hA, integral_indicator hB, integral_indicator hC]
  simp [A, B, C]

theorem arbitrary_law_cutoff : ArbitraryLawCutoffStatement := by
  intro α _ μ _ D ρ hDmeas hD hρ hρ1
  obtain ⟨t, ht, htHalf, hm⟩ := cutoff_exists hDmeas hD hρ hρ1
  refine ⟨t, ht, htHalf, hm, ?_⟩
  intro s hs hsm
  exact cutoff_unique hDmeas hD hρ1 hs ht hsm hm

theorem arbitrary_law_optimizer : ArbitraryLawOptimizerStatement := by
  intro α _ μ _ D ρ hDmeas hD hρ hρ1
  obtain ⟨t, ht, htHalf, hm, huniq⟩ := arbitrary_law_cutoff α μ D ρ hDmeas hD hρ hρ1
  have hDpos : ∀ᵐ x ∂μ, 0 < D x := hD.mono (fun _ hx => hx.1)
  refine ⟨t, ht, htHalf, hm, huniq, allocation_feasible hDmeas hm, ?_⟩
  intro h hh
  refine ⟨?_, fun hth => optimizer_saturation hDpos ht hth hm,
    fun hht => optimizer_formula hDmeas hDpos hh hht⟩
  intro v hv
  by_cases hht : h < t
  · exact optimizer_below_cutoff hDmeas hDpos hh hht hm hv
  · exact optimizer_above_cutoff hDmeas hDpos ht (not_lt.mp hht) hm hv

end ThresholdHC.Tier3
