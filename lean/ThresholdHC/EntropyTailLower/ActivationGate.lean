import ThresholdHC.EntropyTailUpper.BoundedSearch

/-! The observable bounded-prefix gate. It stops at the earlier of the
original procedure and a symmetric random-walk boundary or deterministic
cap. Ties activate the gate. No latent magnitude or sign is an input. -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace ThresholdHC.EntropyTailLower
open ThresholdHC.Tier2 ThresholdHC.CriticalEntropy ThresholdHC.EntropyTailUpper
open ThresholdHC.BlindUpper

def tapeBalance (n : ℕ) (ω : ℕ → Bool) : ℤ :=
  ∑ i ∈ Finset.range n, if ω i then (1:ℤ) else -1

theorem tapeBalance_zero (ω : ℕ → Bool) : tapeBalance 0 ω = 0 := by simp [tapeBalance]

theorem tapeBalance_succ (n : ℕ) (ω : ℕ → Bool) :
    tapeBalance (n+1) ω = tapeBalance n ω+(if ω n then (1:ℤ) else -1) := by
  exact Finset.sum_range_succ _ n

theorem tapeBalance_prefix {n : ℕ} {ω ω' : ℕ → Bool}
    (h : tapePrefix n ω = tapePrefix n ω') : tapeBalance n ω = tapeBalance n ω' := by
  apply Finset.sum_congr rfl
  intro i hi
  have he := congrFun h ⟨i,Finset.mem_range.mp hi⟩
  change ω i = ω' i at he
  rw [he]

theorem measurable_tapeBalance (n : ℕ) : Measurable (tapeBalance n) := by
  unfold tapeBalance
  apply Finset.measurable_sum
  intro i _
  exact (measurable_of_countable (fun b : Bool => if b then (1:ℤ) else -1)).comp
    (measurable_pi_apply i)

theorem measurable_boundedFirst {Ω : Type} [MeasurableSpace Ω]
    (hit : Ω → ℕ → Prop) (M : ℕ) (hm : ∀ n, MeasurableSet {z | hit z n}) :
    Measurable (fun z => boundedFirst (hit z) M) := by
  classical
  unfold boundedFirst
  apply measurable_find
  intro k
  by_cases hk : k ≤ M
  · by_cases he : k = M
    · simp [he]
    · simpa only [hk,he,or_false,true_and] using hm k
  · simp [hk]

def boundaryGateCost (M H : ℕ) (ω : ℕ → Bool) : ℕ :=
  boundedFirst (fun n => (H:ℤ) ≤ |tapeBalance n ω|) M

def activationGateCost {R E : Type} [MeasurableSpace R] [MeasurableSpace E]
    (A : StoppedProcedure R E) (M H : ℕ) (z : R × (ℕ → Bool)) : ℕ :=
  boundedFirst (fun n => A.stop z = n ∨ (H:ℤ) ≤ |tapeBalance n z.2|) M

def activationGateValue {R E : Type} [MeasurableSpace R] [MeasurableSpace E]
    (A : StoppedProcedure R E) (M H : ℕ) (z : R × (ℕ → Bool)) : Bool :=
  if (H:ℤ) ≤ |tapeBalance (activationGateCost A M H z) z.2| ∨ activationGateCost A M H z = M
    then true else false

theorem activationGateCost_min {R E : Type} [MeasurableSpace R] [MeasurableSpace E]
    (A : StoppedProcedure R E) (M H : ℕ) (z : R × (ℕ → Bool)) :
    (activationGateCost A M H z : ℕ∞) = min (A.stop z) (boundaryGateCost M H z.2 : ℕ∞) := by
  have hc := boundedFirst_spec (fun n => A.stop z = n ∨ (H:ℤ) ≤ |tapeBalance n z.2|) M
  have hg := boundedFirst_spec (fun n => (H:ℤ) ≤ |tapeBalance n z.2|) M
  have hleG : activationGateCost A M H z ≤ boundaryGateCost M H z.2 := by
    rcases hg.2 with h | h
    · exact boundedFirst_le_of_hit _ M _ (Or.inr h)
    · change boundaryGateCost M H z.2 = M at h
      rw [h]
      exact hc.1
  have hleT : (activationGateCost A M H z:ℕ∞) ≤ A.stop z := by
    cases ht : A.stop z with
    | top => exact le_top
    | coe t =>
      exact_mod_cast boundedFirst_le_of_hit
        (fun n => A.stop z = n ∨ (H:ℤ) ≤ |tapeBalance n z.2|) M t (Or.inl ht)
  apply le_antisymm (le_min hleT (by exact_mod_cast hleG))
  rcases hc.2 with (ht | hb) | hcap
  · change A.stop z = (activationGateCost A M H z:ℕ∞) at ht
    exact (min_le_left _ _).trans_eq ht
  · have hg' : boundaryGateCost M H z.2 ≤ activationGateCost A M H z :=
      boundedFirst_le_of_hit _ M _ hb
    exact (min_le_right _ _).trans (by exact_mod_cast hg')
  · have hg' : boundaryGateCost M H z.2 ≤ activationGateCost A M H z := by
      change activationGateCost A M H z = M at hcap
      rw [hcap]
      exact hg.1
    exact (min_le_right _ _).trans (by exact_mod_cast hg')

theorem activationGateCost_prefix {R E : Type} [MeasurableSpace R] [MeasurableSpace E]
    (A : StoppedProcedure R E) (M H : ℕ) (r : R) (ω ω' : ℕ → Bool)
    (he : tapePrefix (activationGateCost A M H (r,ω)) ω =
      tapePrefix (activationGateCost A M H (r,ω)) ω') :
    activationGateCost A M H (r,ω') = activationGateCost A M H (r,ω) := by
  apply (boundedFirst_congr_until _ _ M _).symm
  intro n hn
  have hp := prefix_eq_restrict he hn
  have hs : A.stop (r,ω) = n ↔ A.stop (r,ω') = n := by
    rw [← A.stop_observable n (r,ω),← A.stop_observable n (r,ω')]
    change (r,tapePrefix n ω) ∈ A.stopPrefix n ↔ (r,tapePrefix n ω') ∈ A.stopPrefix n
    rw [hp]
  rw [hs,tapeBalance_prefix hp]

theorem measurable_activationGateCost {R E : Type} [MeasurableSpace R] [MeasurableSpace E]
    (A : StoppedProcedure R E) (M H : ℕ) : Measurable (activationGateCost A M H) := by
  apply measurable_boundedFirst
  intro n
  exact (measurableSet_eq_fun A.measurable_stop measurable_const).union
    (measurableSet_le measurable_const (((measurable_tapeBalance n).comp measurable_snd).abs))

theorem measurable_activationGateValue {R E : Type} [MeasurableSpace R] [MeasurableSpace E]
    (A : StoppedProcedure R E) (M H : ℕ) : Measurable (activationGateValue A M H) := by
  have hb : Measurable (fun x : ℕ × (ℕ → Bool) => tapeBalance x.1 x.2) :=
    measurable_from_prod_countable_right (fun n => measurable_tapeBalance n)
  have hm : Measurable (fun z : R × (ℕ → Bool) => tapeBalance (activationGateCost A M H z) z.2) :=
    hb.comp ((measurable_activationGateCost A M H).prodMk measurable_snd)
  exact Measurable.ite ((measurableSet_le measurable_const hm.abs).union
    (measurableSet_eq_fun (measurable_activationGateCost A M H) measurable_const))
    measurable_const measurable_const

def activationGate {R E : Type} [MeasurableSpace R] [MeasurableSpace E]
    (A : StoppedProcedure R E) (M H : ℕ) : StoppedProcedure R Bool :=
  finiteStoppedProcedure (activationGateCost A M H) (activationGateValue A M H)
    (measurable_activationGateCost A M H) (measurable_activationGateValue A M H) (by
      intro r ω ω' he
      have hc := activationGateCost_prefix A M H r ω ω' he
      refine ⟨hc,?_⟩
      unfold activationGateValue
      rw [hc,tapeBalance_prefix he])

theorem activationGate_accepts_iff {R E : Type} [MeasurableSpace R] [MeasurableSpace E]
    (A : StoppedProcedure R E) (M H : ℕ) (z : R × (ℕ → Bool)) :
    (activationGate A M H).output z = true ↔ (boundaryGateCost M H z.2:ℕ∞) ≤ A.stop z := by
  have hc := activationGateCost_min A M H z
  have he : (activationGate A M H).output z = true ↔
      activationGateCost A M H z = boundaryGateCost M H z.2 := by
    change activationGateValue A M H z = true ↔ _
    simp only [activationGateValue,ite_eq_left_iff,Bool.false_eq_true,imp_false,not_not]
    constructor
    · intro h
      have hle : activationGateCost A M H z ≤ boundaryGateCost M H z.2 := by
        exact_mod_cast hc.le.trans (min_le_right _ _)
      apply le_antisymm hle
      rcases h with hb | hcap
      · exact boundedFirst_le_of_hit _ M _ hb
      · rw [hcap]
        exact (boundedFirst_spec _ M).1
    · intro h
      rw [h]
      exact (boundedFirst_spec (fun n => (H:ℤ) ≤ |tapeBalance n z.2|) M).2
  rw [he]
  constructor
  · intro h
    rw [h] at hc
    exact hc.le.trans (min_le_left _ _)
  · intro h
    rw [min_eq_right h] at hc
    exact_mod_cast hc

theorem balance_before_boundaryGate (M H n : ℕ) (ω : ℕ → Bool)
    (hn : n ≤ boundaryGateCost M H ω) : |tapeBalance n ω| ≤ (H:ℤ) := by
  cases n with
  | zero => simp [tapeBalance_zero]
  | succ n =>
    have hbefore := boundedFirst_before (fun k => (H:ℤ) ≤ |tapeBalance k ω|) M n (by
      change n < boundaryGateCost M H ω
      omega)
    have hprev : |tapeBalance n ω| < (H:ℤ) := lt_of_not_ge hbefore
    rw [tapeBalance_succ]
    have hstep : |(if ω n then (1:ℤ) else -1)| = 1 := by cases ω n <;> norm_num
    have hh := abs_add_le (tapeBalance n ω) (if ω n then (1:ℤ) else -1)
    rw [hstep] at hh
    omega

theorem activationGate_bounds {R E : Type} [MeasurableSpace R] [MeasurableSpace E]
    (A : StoppedProcedure R E) (M H : ℕ) (z : R × (ℕ → Bool)) :
    activationGateCost A M H z ≤ M ∧
      |tapeBalance (activationGateCost A M H z) z.2| ≤ (H:ℤ) := by
  refine ⟨(boundedFirst_spec _ M).1,balance_before_boundaryGate M H _ z.2 ?_⟩
  exact_mod_cast (activationGateCost_min A M H z).le.trans (min_le_right _ _)

theorem activationGate_stop_le {R E : Type} [MeasurableSpace R] [MeasurableSpace E]
    (A : StoppedProcedure R E) (M H : ℕ) (z : R × (ℕ → Bool)) :
    (activationGate A M H).stop z ≤ A.stop z ∧ (activationGate A M H).stop z ≤ M := by
  exact ⟨(activationGateCost_min A M H z).le.trans (min_le_left _ _),
    by change (activationGateCost A M H z:ℕ∞) ≤ M
       exact_mod_cast (activationGate_bounds A M H z).1⟩

theorem expected_activationGate_work_le {R E : Type} [MeasurableSpace R] [MeasurableSpace E]
    (ν : Measure R) (p : unitInterval) (A : StoppedProcedure R E) (M H : ℕ) :
    expectedStoppedProcedureWork ν p (activationGate A M H) ≤ expectedStoppedProcedureWork ν p A := by
  apply lintegral_mono
  intro z
  exact ENat.toENNReal_mono (activationGate_stop_le A M H z).1

theorem expected_activationGate_work_finite {R E : Type} [MeasurableSpace R] [MeasurableSpace E]
    (ν : Measure R) [IsProbabilityMeasure ν] (p : unitInterval)
    (A : StoppedProcedure R E) (M H : ℕ) :
    expectedStoppedProcedureWork ν p (activationGate A M H) ≠ ⊤ := by
  have h : expectedStoppedProcedureWork ν p (activationGate A M H) ≤ (M:ℝ≥0∞) := by
    calc
      _ ≤ ∫⁻ _z, (M:ℝ≥0∞) ∂ν.prod (tapeMeasure p) := by
        apply lintegral_mono
        intro z
        change ((activationGate A M H).stop z:ℝ≥0∞) ≤ (M:ℝ≥0∞)
        simpa only [ENat.toENNReal_coe] using ENat.toENNReal_mono (activationGate_stop_le A M H z).2
      _ = _ := by simp
  exact ne_top_of_le_ne_top (by simp) h

end ThresholdHC.EntropyTailLower
