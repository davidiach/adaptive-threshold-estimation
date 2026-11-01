import ThresholdHC.EntropyTailLower.ActivationGate
import ThresholdHC.EntropyTailUpper.PredictableWald

/-! The fair stopped-walk square identity and activation probability bound.
The proof uses finite predictable sums and independence of the next flip,
then integrates over the actual seed law. No termination or integrability
assumption on the original procedure is needed. Measure transfer to biased
coins and rejection/restart renewal remain separate obligations. -/

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace ThresholdHC.EntropyTailLower
open ThresholdHC.Tier2 ThresholdHC.CriticalEntropy ThresholdHC.EntropyTailUpper

theorem abs_tapeBalance_le (n : ℕ) (ω : ℕ → Bool) : |tapeBalance n ω| ≤ (n:ℤ) := by
  induction n with
  | zero => simp [tapeBalance_zero]
  | succ n ih =>
    rw [tapeBalance_succ]
    have h := abs_add_le (tapeBalance n ω) (if ω n then (1:ℤ) else -1)
    have hs : |(if ω n then (1:ℤ) else -1)| = 1 := by cases ω n <;> norm_num
    rw [hs] at h
    exact h.trans (by push_cast; omega)

theorem tapeBalance_square_sum (n : ℕ) (ω : ℕ → Bool) :
    (tapeBalance n ω:ℝ)^2 =
      ∑ i ∈ Finset.range n, (1+2*(tapeBalance i ω:ℝ)*(if ω i then (1:ℝ) else -1)) := by
  induction n with
  | zero => simp [tapeBalance_zero]
  | succ n ih =>
    rw [tapeBalance_succ,Finset.sum_range_succ,← ih]
    cases ω n <;> simp only [Bool.false_eq_true,ite_false,ite_true,Int.cast_add,Int.cast_neg,Int.cast_one] <;> ring

theorem stopped_sum_predictable (g : ℕ → (ℕ → Bool) → ℝ)
    (τ : (ℕ → Bool) → ℕ) (M : ℕ) (hM : ∀ ω, τ ω ≤ M) (ω : ℕ → Bool) :
    (∑ i ∈ Finset.range (τ ω), g i ω) =
      ∑ i ∈ Finset.range M, survives τ i ω*g i ω := by
  classical
  calc
    _ = ∑ i ∈ Finset.range (τ ω), survives τ i ω*g i ω := by
      apply Finset.sum_congr rfl
      intro i hi
      simp [survives,Finset.mem_range.mp hi]
    _ = _ := Finset.sum_subset (Finset.range_mono (hM ω)) (fun i _ hi => by
      simp only [Finset.mem_range,not_lt] at hi
      simp [survives,not_lt.mpr hi])

theorem survives_balance_prefix {τ : (ℕ → Bool) → ℕ}
    (hext : ∀ ω ω', tapePrefix (τ ω) ω = tapePrefix (τ ω) ω' → τ ω' = τ ω)
    (n : ℕ) :
    (fun ω => survives τ n ω*(tapeBalance n ω:ℝ)) =
      (fun w => survives τ n (completePrefix n w)*(tapeBalance n (completePrefix n w):ℝ)) ∘ tapePrefix n := by
  funext ω
  have he := (tapePrefix_completePrefix n (tapePrefix n ω)).symm
  have hs := congrFun (survives_prefix hext n) ω
  dsimp only [Function.comp_apply] at hs ⊢
  rw [hs,tapeBalance_prefix he]

theorem integrable_survives_balance_step (p : unitInterval) {τ : (ℕ → Bool) → ℕ}
    (hext : ∀ ω ω', tapePrefix (τ ω) ω = tapePrefix (τ ω) ω' → τ ω' = τ ω)
    (n : ℕ) : Integrable
      (fun ω => (survives τ n ω*(tapeBalance n ω:ℝ))*(if ω n then (1:ℝ) else -1))
      (tapeMeasure p) := by
  have hm : Measurable (fun ω => survives τ n ω*(tapeBalance n ω:ℝ)) := by
    rw [survives_balance_prefix hext]
    exact (measurable_of_countable _).comp (measurable_prefix n)
  apply Integrable.of_bound (hm.mul ((measurable_of_countable
    (fun b : Bool => if b then (1:ℝ) else -1)).comp (measurable_pi_apply n))).aestronglyMeasurable n
  refine ae_of_all _ (fun ω => ?_)
  have hb : |(tapeBalance n ω:ℝ)| ≤ (n:ℝ) := by exact_mod_cast abs_tapeBalance_le n ω
  change ‖(survives τ n ω*(tapeBalance n ω:ℝ))*(if ω n then (1:ℝ) else -1)‖ ≤ (n:ℝ)
  by_cases hn : n < τ ω
  · cases ω n <;> simpa [survives,hn,Real.norm_eq_abs] using hb
  · simp [survives,hn]

theorem integral_survives_balance_step_fair {τ : (ℕ → Bool) → ℕ}
    (hext : ∀ ω ω', tapePrefix (τ ω) ω = tapePrefix (τ ω) ω' → τ ω' = τ ω)
    (n : ℕ) :
    (∫ ω, (survives τ n ω*(tapeBalance n ω:ℝ))*(if ω n then (1:ℝ) else -1)
      ∂tapeMeasure ⟨1/2,by norm_num⟩) = 0 := by
  have hm : Measurable (fun ω => survives τ n ω*(tapeBalance n ω:ℝ)) := by
    rw [survives_balance_prefix hext]
    exact (measurable_of_countable _).comp (measurable_prefix n)
  have hi : IndepFun (fun ω => survives τ n ω*(tapeBalance n ω:ℝ))
      (fun ω : ℕ → Bool => if ω n then (1:ℝ) else -1) (tapeMeasure ⟨1/2,by norm_num⟩) := by
    rw [survives_balance_prefix hext]
    exact (prefix_indep_next _ n).comp
      (measurable_of_countable (fun w : Fin n → Bool =>
        survives τ n (completePrefix n w)*(tapeBalance n (completePrefix n w):ℝ)))
      (measurable_of_countable (fun b : Bool => if b then (1:ℝ) else -1))
  rw [hi.integral_fun_mul_eq_mul_integral hm.aestronglyMeasurable
    (((measurable_of_countable (fun b : Bool => if b then (1:ℝ) else -1)).comp
      (measurable_pi_apply n)).aestronglyMeasurable),
    integral_bitScore _ (fun b : Bool => if b then (1:ℝ) else -1) n]
  norm_num [bitScoreMean]

theorem bounded_fair_square_identity (τ : (ℕ → Bool) → ℕ) (M : ℕ)
    (hM : ∀ ω, τ ω ≤ M)
    (hext : ∀ ω ω', tapePrefix (τ ω) ω = tapePrefix (τ ω) ω' → τ ω' = τ ω) :
    (∫ ω, (tapeBalance (τ ω) ω:ℝ)^2 ∂tapeMeasure ⟨1/2,by norm_num⟩) =
      ∫ ω, (τ ω:ℝ) ∂tapeMeasure ⟨1/2,by norm_num⟩ := by
  have he (ω : ℕ → Bool) : (tapeBalance (τ ω) ω:ℝ)^2 =
      ∑ i ∈ Finset.range M, (survives τ i ω +
        2*((survives τ i ω*(tapeBalance i ω:ℝ))*(if ω i then (1:ℝ) else -1))) := by
    rw [tapeBalance_square_sum,stopped_sum_predictable
      (fun i ω => 1+2*(tapeBalance i ω:ℝ)*(if ω i then (1:ℝ) else -1)) τ M hM ω]
    apply Finset.sum_congr rfl
    intro i _
    ring
  simp_rw [he,stopped_count_eq τ M hM]
  have hi (i : ℕ) := (integrable_survives_balance_step ⟨1/2,by norm_num⟩ hext i).const_mul 2
  have hs (i : ℕ) : Integrable (fun ω => survives τ i ω +
        2*((survives τ i ω*(tapeBalance i ω:ℝ))*(if ω i then (1:ℝ) else -1)))
      (tapeMeasure ⟨1/2,by norm_num⟩) := (integrable_survives _ hext i).add (hi i)
  rw [integral_finsetSum _ (fun i _ => hs i),
    integral_finsetSum _ (fun i _ => integrable_survives ⟨1/2,by norm_num⟩ hext i)]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_add (integrable_survives _ hext i) (hi i),integral_const_mul,
    integral_survives_balance_step_fair hext i]
  ring

theorem measurable_activationGate_balance {R E : Type} [MeasurableSpace R] [MeasurableSpace E]
    (A : StoppedProcedure R E) (M H : ℕ) :
    Measurable (fun z : R × (ℕ → Bool) => (tapeBalance (activationGateCost A M H z) z.2:ℝ)) := by
  have hb : Measurable (fun x : ℕ × (ℕ → Bool) => tapeBalance x.1 x.2) :=
    measurable_from_prod_countable_right (fun n => measurable_tapeBalance n)
  exact (measurable_of_countable (fun k : ℤ => (k:ℝ))).comp
    (hb.comp ((measurable_activationGateCost A M H).prodMk measurable_snd))

theorem integrable_activationGate_count {R E : Type} [MeasurableSpace R] [MeasurableSpace E]
    (ν : Measure R) [IsProbabilityMeasure ν] (p : unitInterval)
    (A : StoppedProcedure R E) (M H : ℕ) :
    Integrable (fun z => (activationGateCost A M H z:ℝ)) (ν.prod (tapeMeasure p)) := by
  apply Integrable.of_bound
    ((measurable_of_countable (fun n : ℕ => (n:ℝ))).comp
      (measurable_activationGateCost A M H)).aestronglyMeasurable M
  refine ae_of_all _ (fun z => ?_)
  change ‖(activationGateCost A M H z:ℝ)‖ ≤ (M:ℝ)
  rw [Real.norm_of_nonneg (Nat.cast_nonneg _)]
  exact_mod_cast (activationGate_bounds A M H z).1

theorem integrable_activationGate_square {R E : Type} [MeasurableSpace R] [MeasurableSpace E]
    (ν : Measure R) [IsProbabilityMeasure ν] (p : unitInterval)
    (A : StoppedProcedure R E) (M H : ℕ) :
    Integrable (fun z => (tapeBalance (activationGateCost A M H z) z.2:ℝ)^2)
      (ν.prod (tapeMeasure p)) := by
  apply Integrable.of_bound ((measurable_activationGate_balance A M H).pow_const 2).aestronglyMeasurable
    ((H:ℝ)^2)
  refine ae_of_all _ (fun z => ?_)
  rw [Real.norm_of_nonneg (sq_nonneg _)]
  have hb : |(tapeBalance (activationGateCost A M H z) z.2:ℝ)| ≤ (H:ℝ) := by
    exact_mod_cast (activationGate_bounds A M H z).2
  nlinarith [sq_abs (tapeBalance (activationGateCost A M H z) z.2:ℝ),
    (sq_le_sq₀ (abs_nonneg _) (Nat.cast_nonneg H)).mpr hb]

theorem activationGate_fair_square_identity {R E : Type} [MeasurableSpace R] [MeasurableSpace E]
    (ν : Measure R) [IsProbabilityMeasure ν] (A : StoppedProcedure R E) (M H : ℕ) :
    (∫ z, (tapeBalance (activationGateCost A M H z) z.2:ℝ)^2
      ∂ν.prod (tapeMeasure ⟨1/2,by norm_num⟩)) =
      ∫ z, (activationGateCost A M H z:ℝ) ∂ν.prod (tapeMeasure ⟨1/2,by norm_num⟩) := by
  rw [integral_prod _ (integrable_activationGate_square ν _ A M H),
    integral_prod _ (integrable_activationGate_count ν _ A M H)]
  apply integral_congr_ae
  refine ae_of_all _ (fun r => ?_)
  exact bounded_fair_square_identity (fun ω => activationGateCost A M H (r,ω)) M
    (fun ω => (activationGate_bounds A M H (r,ω)).1) (activationGateCost_prefix A M H r)

theorem activationGate_indicator_bound {R E : Type} [MeasurableSpace R] [MeasurableSpace E]
    (A : StoppedProcedure R E) (M H : ℕ) (hM : 0 < M) (hH : 0 < H)
    (z : R × (ℕ → Bool)) :
    {z | (activationGate A M H).output z = true}.indicator (fun _ => (1:ℝ)) z ≤
      (activationGateCost A M H z:ℝ)/(M:ℝ) +
        (tapeBalance (activationGateCost A M H z) z.2:ℝ)^2/(H:ℝ)^2 := by
  have hMr : 0 < (M:ℝ) := by exact_mod_cast hM
  have hHr : 0 < (H:ℝ) := by exact_mod_cast hH
  have hc : 0 ≤ (activationGateCost A M H z:ℝ)/(M:ℝ) := by positivity
  have hs : 0 ≤ (tapeBalance (activationGateCost A M H z) z.2:ℝ)^2/(H:ℝ)^2 := by positivity
  by_cases hz : (activationGate A M H).output z = true
  · rw [Set.indicator_of_mem (show z ∈ {z | (activationGate A M H).output z = true} from hz)]
    change activationGateValue A M H z = true at hz
    simp only [activationGateValue,ite_eq_left_iff,Bool.false_eq_true,imp_false,not_not] at hz
    rcases hz with hb | hcap
    · have hb' : (H:ℝ) ≤ |(tapeBalance (activationGateCost A M H z) z.2:ℝ)| := by
        exact_mod_cast hb
      have hsq : (H:ℝ)^2 ≤ (tapeBalance (activationGateCost A M H z) z.2:ℝ)^2 := by
        nlinarith [(sq_le_sq₀ hHr.le (abs_nonneg _)).mpr hb',
          sq_abs (tapeBalance (activationGateCost A M H z) z.2:ℝ)]
      have hd := (one_le_div (sq_pos_of_pos hHr)).mpr hsq
      linarith
    · rw [hcap,div_self hMr.ne']
      exact le_add_of_nonneg_right (div_nonneg (sq_nonneg _) (sq_nonneg _))
  · rw [Set.indicator_of_notMem hz]
    exact add_nonneg hc hs

theorem activationGate_fair_probability_le {R E : Type} [MeasurableSpace R] [MeasurableSpace E]
    (ν : Measure R) [IsProbabilityMeasure ν] (A : StoppedProcedure R E)
    (M H : ℕ) (hM : 0 < M) (hH : 0 < H) :
    (ν.prod (tapeMeasure ⟨1/2,by norm_num⟩)).real
      {z | (activationGate A M H).output z = true} ≤
      (1/(M:ℝ)+1/(H:ℝ)^2)*
        ∫ z, (activationGateCost A M H z:ℝ) ∂ν.prod (tapeMeasure ⟨1/2,by norm_num⟩) := by
  have hm : MeasurableSet {z | (activationGate A M H).output z = true} :=
    measurableSet_eq_fun (activationGate A M H).measurable_output measurable_const
  have hic := (integrable_activationGate_count ν ⟨1/2,by norm_num⟩ A M H).div_const (M:ℝ)
  have his := (integrable_activationGate_square ν ⟨1/2,by norm_num⟩ A M H).div_const ((H:ℝ)^2)
  have hi := integral_mono ((integrable_const (1:ℝ)).indicator hm) (hic.add his)
    (activationGate_indicator_bound A M H hM hH)
  have he : (∫ z, {z | (activationGate A M H).output z = true}.indicator (fun _ => (1:ℝ)) z
      ∂ν.prod (tapeMeasure ⟨1/2,by norm_num⟩)) =
      (ν.prod (tapeMeasure ⟨1/2,by norm_num⟩)).real {z | (activationGate A M H).output z = true} :=
    integral_indicator_one hm
  simp only [Pi.add_apply] at hi
  rw [he,integral_add hic his,integral_div,integral_div,
    activationGate_fair_square_identity ν A M H] at hi
  convert hi using 1
  ring

theorem gate_scale_reciprocal_bound (a : ℝ) (ha : 0 < a) :
    0 < ⌈(a^2)⁻¹⌉₊ ∧ 0 < ⌈a⁻¹⌉₊ ∧
      1/(⌈(a^2)⁻¹⌉₊:ℝ)+1/(⌈a⁻¹⌉₊:ℝ)^2 ≤ 2*a^2 := by
  have ha2 : 0 < a^2 := sq_pos_of_pos ha
  have hN : (a^2)⁻¹ ≤ (⌈(a^2)⁻¹⌉₊:ℝ) := Nat.le_ceil _
  have hH : a⁻¹ ≤ (⌈a⁻¹⌉₊:ℝ) := Nat.le_ceil _
  have hNp : 0 < (⌈(a^2)⁻¹⌉₊:ℝ) := (inv_pos.mpr ha2).trans_le hN
  have hHp : 0 < (⌈a⁻¹⌉₊:ℝ) := (inv_pos.mpr ha).trans_le hH
  refine ⟨by exact_mod_cast hNp,by exact_mod_cast hHp,?_⟩
  have hmN := mul_le_mul_of_nonneg_right hN ha2.le
  have hmH := mul_le_mul_of_nonneg_right hH ha.le
  rw [inv_mul_cancel₀ ha2.ne'] at hmN
  rw [inv_mul_cancel₀ ha.ne'] at hmH
  have hNr : 1/(⌈(a^2)⁻¹⌉₊:ℝ) ≤ a^2 := (div_le_iff₀ hNp).mpr (by nlinarith only [hmN])
  have hHr : 1/(⌈a⁻¹⌉₊:ℝ)^2 ≤ a^2 := by
    apply (div_le_iff₀ (sq_pos_of_pos hHp)).mpr
    nlinarith [sq_nonneg ((⌈a⁻¹⌉₊:ℝ)*a-1)]
  linarith

theorem expected_activationGate_work_toReal {R E : Type} [MeasurableSpace R] [MeasurableSpace E]
    (ν : Measure R) [IsProbabilityMeasure ν] (p : unitInterval)
    (A : StoppedProcedure R E) (M H : ℕ) :
    (expectedStoppedProcedureWork ν p (activationGate A M H)).toReal =
      ∫ z, (activationGateCost A M H z:ℝ) ∂ν.prod (tapeMeasure p) := by
  have he := integral_eq_lintegral_of_nonneg_ae
    (ae_of_all (ν.prod (tapeMeasure p)) (fun z => Nat.cast_nonneg (α := ℝ) (activationGateCost A M H z)))
    (integrable_activationGate_count ν p A M H).aestronglyMeasurable
  rw [he]
  congr 1
  apply lintegral_congr
  intro z
  change ((activationGateCost A M H z:ℕ∞):ℝ≥0∞) = ENNReal.ofReal (activationGateCost A M H z:ℝ)
  simp

/-- Fair activation is rare when the gate uses little expected work. This
does not yet transfer that work to a biased-coin law. -/
theorem activationGate_fair_scaled_probability {R E : Type} [MeasurableSpace R] [MeasurableSpace E]
    (ν : Measure R) [IsProbabilityMeasure ν] (A : StoppedProcedure R E)
    (a : ℝ) (ha : 0 < a) :
    (ν.prod (tapeMeasure ⟨1/2,by norm_num⟩)).real
      {z | (activationGate A ⌈(a^2)⁻¹⌉₊ ⌈a⁻¹⌉₊).output z = true} ≤
      2*a^2*(expectedStoppedProcedureWork ν ⟨1/2,by norm_num⟩
        (activationGate A ⌈(a^2)⁻¹⌉₊ ⌈a⁻¹⌉₊)).toReal := by
  obtain ⟨hN,hH,hs⟩ := gate_scale_reciprocal_bound a ha
  have hp := activationGate_fair_probability_le ν A _ _ hN hH
  rw [← expected_activationGate_work_toReal] at hp
  exact hp.trans (mul_le_mul_of_nonneg_right hs ENNReal.toReal_nonneg)

end ThresholdHC.EntropyTailLower
