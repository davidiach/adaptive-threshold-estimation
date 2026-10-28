import ThresholdHC.BlindUpper.ClassifierProcedure
import ThresholdHC.Uniform713.ClassifierModel

/-! An observable bounded asymmetric classifier, tested at dyadic flip counts. -/

noncomputable section
namespace ThresholdHC.CriticalUpper
open MeasureTheory Set ThresholdHC.Uniform713 ThresholdHC.CriticalEntropy

def screenBoundary (A : ℝ) (k : ℕ) : ℝ := Real.sqrt (A/(2*cap k))

theorem screenBoundary_nonneg (A : ℝ) (k : ℕ) : 0 ≤ screenBoundary A k :=
  Real.sqrt_nonneg _

theorem screenBoundary_sq (A : ℝ) (hA : 0 ≤ A) (k : ℕ) :
    (screenBoundary A k)^2 = A/(2*cap k) := Real.sq_sqrt (by positivity [cap_pos k])

def screenStop (A₀ A₁ : ℝ) (m : ℕ → ℝ) (L : ℕ) : ℕ :=
  Nat.find (show ∃ k, L ≤ k ∨ m k < 1/2-screenBoundary A₀ k ∨
      1/2+screenBoundary A₁ k < m k from ⟨L,Or.inl le_rfl⟩)

theorem screenStop_le (A₀ A₁ : ℝ) (m : ℕ → ℝ) (L : ℕ) : screenStop A₀ A₁ m L ≤ L :=
  Nat.find_min' _ (Or.inl le_rfl)

theorem screenStop_spec (A₀ A₁ : ℝ) (m : ℕ → ℝ) (L : ℕ) :
    L ≤ screenStop A₀ A₁ m L ∨
    m (screenStop A₀ A₁ m L) < 1/2-screenBoundary A₀ (screenStop A₀ A₁ m L) ∨
    1/2+screenBoundary A₁ (screenStop A₀ A₁ m L) < m (screenStop A₀ A₁ m L) :=
  Nat.find_spec (show ∃ k, L ≤ k ∨ m k < 1/2-screenBoundary A₀ k ∨
      1/2+screenBoundary A₁ k < m k from ⟨L,Or.inl le_rfl⟩)

theorem screenStop_min (A₀ A₁ : ℝ) (m : ℕ → ℝ) (L k : ℕ)
    (hk : k < screenStop A₀ A₁ m L) :
    k < L ∧ 1/2-screenBoundary A₀ k ≤ m k ∧ m k ≤ 1/2+screenBoundary A₁ k := by
  have h := Nat.find_min (show ∃ k, L ≤ k ∨ m k < 1/2-screenBoundary A₀ k ∨
      1/2+screenBoundary A₁ k < m k from ⟨L,Or.inl le_rfl⟩) hk
  simpa only [not_or,not_le,not_lt] using h

theorem screenStop_eq_iff (A₀ A₁ : ℝ) (m : ℕ → ℝ) (L k : ℕ) :
    screenStop A₀ A₁ m L = k ↔
      (L ≤ k ∨ m k < 1/2-screenBoundary A₀ k ∨ 1/2+screenBoundary A₁ k < m k) ∧
      ∀ j < k, j < L ∧ 1/2-screenBoundary A₀ j ≤ m j ∧ m j ≤ 1/2+screenBoundary A₁ j := by
  rw [screenStop,Nat.find_eq_iff]
  simp only [not_or,not_le,not_lt]

def screenDecision (A₀ A₁ : ℝ) (m : ℕ → ℝ) (L : ℕ) : ℝ :=
  if 1/2 < m (screenStop A₀ A₁ m L) then 1 else 0

theorem screenDecision_zero_or_one (A₀ A₁ : ℝ) (m : ℕ → ℝ) (L : ℕ) :
    screenDecision A₀ A₁ m L = 0 ∨ screenDecision A₀ A₁ m L = 1 := by
  unfold screenDecision
  split_ifs <;> simp

theorem screen_wrong_positive (A₀ A₁ : ℝ) (m : ℕ → ℝ) (L : ℕ) (d : ℝ)
    (hwrong : screenDecision A₀ A₁ m L ≠ 1) :
    (screenStop A₀ A₁ m L = L ∧ d ≤ (1/2+d)-m L) ∨
    (screenStop A₀ A₁ m L < L ∧
      d+screenBoundary A₀ (screenStop A₀ A₁ m L) ≤ (1/2+d)-m (screenStop A₀ A₁ m L)) := by
  have hm : m (screenStop A₀ A₁ m L) ≤ 1/2 := by simpa [screenDecision] using hwrong
  by_cases hs : screenStop A₀ A₁ m L = L
  · left
    exact ⟨hs,by rw [hs] at hm; linarith⟩
  · have hlt := lt_of_le_of_ne (screenStop_le A₀ A₁ m L) hs
    refine Or.inr ⟨hlt,?_⟩
    have hc := (screenStop_spec A₀ A₁ m L).resolve_left (by omega)
    rcases hc with h | h
    · linarith
    · linarith [screenBoundary_nonneg A₁ (screenStop A₀ A₁ m L)]

theorem screen_wrong_negative (A₀ A₁ : ℝ) (m : ℕ → ℝ) (L : ℕ) (d : ℝ)
    (hwrong : screenDecision A₀ A₁ m L ≠ 0) :
    (screenStop A₀ A₁ m L = L ∧ d ≤ m L-(1/2-d)) ∨
    (screenStop A₀ A₁ m L < L ∧
      d+screenBoundary A₁ (screenStop A₀ A₁ m L) ≤ m (screenStop A₀ A₁ m L)-(1/2-d)) := by
  have hm : 1/2 < m (screenStop A₀ A₁ m L) := by simpa [screenDecision] using hwrong
  by_cases hs : screenStop A₀ A₁ m L = L
  · left
    exact ⟨hs,by rw [hs] at hm; linarith⟩
  · have hlt := lt_of_le_of_ne (screenStop_le A₀ A₁ m L) hs
    refine Or.inr ⟨hlt,?_⟩
    have hc := (screenStop_spec A₀ A₁ m L).resolve_left (by omega)
    rcases hc with h | h
    · linarith [screenBoundary_nonneg A₀ (screenStop A₀ A₁ m L)]
    · linarith

theorem measurable_screenStop {Ω : Type*} [MeasurableSpace Ω]
    (A₀ A₁ : ℝ) (m : ℕ → Ω → ℝ) (hm : ∀ k, Measurable (m k)) (L : ℕ) :
    Measurable (fun ω => screenStop A₀ A₁ (fun k => m k ω) L) := by
  apply measurable_to_countable'
  intro k
  have he : {ω | screenStop A₀ A₁ (fun j => m j ω) L = k} =
      ({ω | L ≤ k} ∪ {ω | m k ω < 1/2-screenBoundary A₀ k} ∪
        {ω | 1/2+screenBoundary A₁ k < m k ω}) ∩
      ⋂ j, ⋂ (_ : j < k), ({ω | j < L} ∩
        {ω | 1/2-screenBoundary A₀ j ≤ m j ω} ∩ {ω | m j ω ≤ 1/2+screenBoundary A₁ j}) := by
    ext ω
    simp only [mem_ofPred_eq,mem_inter_iff,mem_union,mem_iInter,screenStop_eq_iff,and_assoc,or_assoc]
  change MeasurableSet {ω | screenStop A₀ A₁ (fun j => m j ω) L = k}
  rw [he]
  apply MeasurableSet.inter
  · exact ((MeasurableSet.const _).union (measurableSet_lt (hm k) measurable_const)).union
      (measurableSet_lt measurable_const (hm k))
  · exact MeasurableSet.iInter fun j => MeasurableSet.iInter fun _ =>
      ((MeasurableSet.const _).inter (measurableSet_le measurable_const (hm j))).inter
        (measurableSet_le (hm j) measurable_const)

theorem measurable_screenDecision {Ω : Type*} [MeasurableSpace Ω]
    (A₀ A₁ : ℝ) (m : ℕ → Ω → ℝ) (hm : ∀ k, Measurable (m k)) (L : ℕ) :
    Measurable (fun ω => screenDecision A₀ A₁ (fun k => m k ω) L) := by
  have hmean : Measurable (fun ω => m (screenStop A₀ A₁ (fun k => m k ω) L) ω) :=
    (measurable_from_prod_countable_left (f := fun z : Ω × ℕ => m z.2 z.1) (fun k => hm k)).comp
      (measurable_id.prodMk (measurable_screenStop A₀ A₁ m hm L))
  exact Measurable.ite (measurableSet_lt measurable_const hmean) measurable_const measurable_const

theorem screenStop_congr_until (A₀ A₁ : ℝ) (m m' : ℕ → ℝ) (L : ℕ)
    (hm : ∀ k ≤ screenStop A₀ A₁ m L, m' k = m k) :
    screenStop A₀ A₁ m' L = screenStop A₀ A₁ m L := by
  apply (screenStop_eq_iff A₀ A₁ m' L _).2
  constructor
  · simpa only [hm _ le_rfl] using screenStop_spec A₀ A₁ m L
  · intro k hk
    simpa only [hm k hk.le] using screenStop_min A₀ A₁ m L k hk

def screenCost (A₀ A₁ : ℝ) (L : ℕ) (ω : ℕ → Bool) : ℕ :=
  2 ^ screenStop A₀ A₁ (fun k => dyadicMean Tier2.observations k ω) L

def screenValue (A₀ A₁ : ℝ) (L : ℕ) (ω : ℕ → Bool) : ℝ :=
  screenDecision A₀ A₁ (fun k => dyadicMean Tier2.observations k ω) L

theorem screen_prefix_ext (A₀ A₁ : ℝ) (L : ℕ) (ω ω' : ℕ → Bool)
    (h : Tier2.tapePrefix (screenCost A₀ A₁ L ω) ω = Tier2.tapePrefix (screenCost A₀ A₁ L ω) ω') :
    screenCost A₀ A₁ L ω' = screenCost A₀ A₁ L ω ∧ screenValue A₀ A₁ L ω' = screenValue A₀ A₁ L ω := by
  let m := fun k => dyadicMean Tier2.observations k ω
  let m' := fun k => dyadicMean Tier2.observations k ω'
  have hm (k : ℕ) (hk : k ≤ screenStop A₀ A₁ m L) : m' k = m k :=
    (BlindUpper.dyadicMean_prefix_ext _ ω ω' h k (Nat.pow_le_pow_right (by omega : 0 < 2) hk)).symm
  have he := screenStop_congr_until A₀ A₁ m m' L hm
  constructor
  · exact congrArg (fun k : ℕ => 2^k) he
  · change screenDecision A₀ A₁ m' L = screenDecision A₀ A₁ m L
    unfold screenDecision
    rw [he,hm _ le_rfl]

theorem measurable_screenCost (A₀ A₁ : ℝ) (L : ℕ) : Measurable (screenCost A₀ A₁ L) :=
  (measurable_of_countable (fun n : ℕ => 2^n)).comp
    (measurable_screenStop A₀ A₁ (dyadicMean Tier2.observations)
      (fun _k => measurable_prefixMean Tier2.measurable_observations _) L)

theorem measurable_screenValue (A₀ A₁ : ℝ) (L : ℕ) : Measurable (screenValue A₀ A₁ L) :=
  measurable_screenDecision A₀ A₁ (dyadicMean Tier2.observations)
    (fun _k => measurable_prefixMean Tier2.measurable_observations _) L

def screenProcedure (A₀ A₁ : ℝ) (L : ℕ) : StoppedProcedure Unit ℝ :=
  BlindUpper.finiteStoppedProcedure (fun z => screenCost A₀ A₁ L z.2) (fun z => screenValue A₀ A₁ L z.2)
    ((measurable_screenCost A₀ A₁ L).comp measurable_snd)
    ((measurable_screenValue A₀ A₁ L).comp measurable_snd)
    (fun _ ω ω' h => screen_prefix_ext A₀ A₁ L ω ω' h)

theorem screenCost_pos (A₀ A₁ : ℝ) (L : ℕ) (ω : ℕ → Bool) : 0 < screenCost A₀ A₁ L ω :=
  Nat.two_pow_pos _

theorem screenCost_le (A₀ A₁ : ℝ) (L : ℕ) (ω : ℕ → Bool) : screenCost A₀ A₁ L ω ≤ 2^L :=
  Nat.pow_le_pow_right (by omega : 0 < 2) (screenStop_le _ _ _ _)

end ThresholdHC.CriticalUpper
