import ThresholdHC.CriticalUpper.ScreenModel

/-! Stage-dependent asymmetric boundaries, with a scale-dependent initial
flip count. All decisions and stopping times depend only on observed flips. -/

noncomputable section
namespace ThresholdHC.RareAboveTwo
open MeasureTheory Set ThresholdHC.Uniform713 ThresholdHC.CriticalEntropy

def bandBoundary (e : ℕ) (A : ℕ → ℝ) (k : ℕ) : ℝ := Real.sqrt (A k/(2*cap (e+k)))

theorem bandBoundary_nonneg (e : ℕ) (A : ℕ → ℝ) (k : ℕ) : 0 ≤ bandBoundary e A k :=
  Real.sqrt_nonneg _

theorem bandBoundary_sq (e : ℕ) (A : ℕ → ℝ) (hA : ∀ k, 0 ≤ A k) (k : ℕ) :
    (bandBoundary e A k)^2 = A k/(2*cap (e+k)) := Real.sq_sqrt (by positivity [cap_pos (e+k),hA k])

def bandStop (e : ℕ) (A₀ A₁ : ℕ → ℝ) (m : ℕ → ℝ) (L : ℕ) : ℕ :=
  Nat.find (show ∃ k, L ≤ k ∨ m k < 1/2-bandBoundary e A₀ k ∨
      1/2+bandBoundary e A₁ k < m k from ⟨L,Or.inl le_rfl⟩)

theorem bandStop_le (e : ℕ) (A₀ A₁ : ℕ → ℝ) (m : ℕ → ℝ) (L : ℕ) : bandStop e A₀ A₁ m L ≤ L :=
  Nat.find_min' _ (Or.inl le_rfl)

theorem bandStop_spec (e : ℕ) (A₀ A₁ : ℕ → ℝ) (m : ℕ → ℝ) (L : ℕ) :
    L ≤ bandStop e A₀ A₁ m L ∨
    m (bandStop e A₀ A₁ m L) < 1/2-bandBoundary e A₀ (bandStop e A₀ A₁ m L) ∨
    1/2+bandBoundary e A₁ (bandStop e A₀ A₁ m L) < m (bandStop e A₀ A₁ m L) :=
  Nat.find_spec (show ∃ k, L ≤ k ∨ m k < 1/2-bandBoundary e A₀ k ∨
      1/2+bandBoundary e A₁ k < m k from ⟨L,Or.inl le_rfl⟩)

theorem bandStop_min (e : ℕ) (A₀ A₁ : ℕ → ℝ) (m : ℕ → ℝ) (L k : ℕ)
    (hk : k < bandStop e A₀ A₁ m L) :
    k < L ∧ 1/2-bandBoundary e A₀ k ≤ m k ∧ m k ≤ 1/2+bandBoundary e A₁ k := by
  have h := Nat.find_min (show ∃ k, L ≤ k ∨ m k < 1/2-bandBoundary e A₀ k ∨
      1/2+bandBoundary e A₁ k < m k from ⟨L,Or.inl le_rfl⟩) hk
  simpa only [not_or,not_le,not_lt] using h

theorem bandStop_eq_iff (e : ℕ) (A₀ A₁ : ℕ → ℝ) (m : ℕ → ℝ) (L k : ℕ) :
    bandStop e A₀ A₁ m L = k ↔
      (L ≤ k ∨ m k < 1/2-bandBoundary e A₀ k ∨ 1/2+bandBoundary e A₁ k < m k) ∧
      ∀ j < k, j < L ∧ 1/2-bandBoundary e A₀ j ≤ m j ∧ m j ≤ 1/2+bandBoundary e A₁ j := by
  rw [bandStop,Nat.find_eq_iff]
  simp only [not_or,not_le,not_lt]

def bandDecision (e : ℕ) (A₀ A₁ : ℕ → ℝ) (m : ℕ → ℝ) (L : ℕ) : ℝ :=
  if 1/2 < m (bandStop e A₀ A₁ m L) then 1 else 0

theorem bandDecision_zero_or_one (e : ℕ) (A₀ A₁ : ℕ → ℝ) (m : ℕ → ℝ) (L : ℕ) :
    bandDecision e A₀ A₁ m L = 0 ∨ bandDecision e A₀ A₁ m L = 1 := by
  unfold bandDecision
  split_ifs <;> simp

theorem band_wrong_positive (e : ℕ) (A₀ A₁ : ℕ → ℝ) (m : ℕ → ℝ) (L : ℕ) (d : ℝ)
    (hwrong : bandDecision e A₀ A₁ m L ≠ 1) :
    (bandStop e A₀ A₁ m L = L ∧ d ≤ (1/2+d)-m L) ∨
    (bandStop e A₀ A₁ m L < L ∧
      d+bandBoundary e A₀ (bandStop e A₀ A₁ m L) ≤ (1/2+d)-m (bandStop e A₀ A₁ m L)) := by
  have hm : m (bandStop e A₀ A₁ m L) ≤ 1/2 := by simpa [bandDecision] using hwrong
  by_cases hs : bandStop e A₀ A₁ m L = L
  · left
    exact ⟨hs,by rw [hs] at hm; linarith⟩
  · have hlt := lt_of_le_of_ne (bandStop_le e A₀ A₁ m L) hs
    refine Or.inr ⟨hlt,?_⟩
    have hc := (bandStop_spec e A₀ A₁ m L).resolve_left (by omega)
    rcases hc with h | h
    · linarith
    · linarith [bandBoundary_nonneg e A₁ (bandStop e A₀ A₁ m L)]

theorem band_wrong_negative (e : ℕ) (A₀ A₁ : ℕ → ℝ) (m : ℕ → ℝ) (L : ℕ) (d : ℝ)
    (hwrong : bandDecision e A₀ A₁ m L ≠ 0) :
    (bandStop e A₀ A₁ m L = L ∧ d ≤ m L-(1/2-d)) ∨
    (bandStop e A₀ A₁ m L < L ∧
      d+bandBoundary e A₁ (bandStop e A₀ A₁ m L) ≤ m (bandStop e A₀ A₁ m L)-(1/2-d)) := by
  have hm : 1/2 < m (bandStop e A₀ A₁ m L) := by simpa [bandDecision] using hwrong
  by_cases hs : bandStop e A₀ A₁ m L = L
  · left
    exact ⟨hs,by rw [hs] at hm; linarith⟩
  · have hlt := lt_of_le_of_ne (bandStop_le e A₀ A₁ m L) hs
    refine Or.inr ⟨hlt,?_⟩
    have hc := (bandStop_spec e A₀ A₁ m L).resolve_left (by omega)
    rcases hc with h | h
    · linarith [bandBoundary_nonneg e A₀ (bandStop e A₀ A₁ m L)]
    · linarith

theorem measurable_bandStop {Ω : Type*} [MeasurableSpace Ω]
    (e : ℕ) (A₀ A₁ : ℕ → ℝ) (m : ℕ → Ω → ℝ) (hm : ∀ k, Measurable (m k)) (L : ℕ) :
    Measurable (fun ω => bandStop e A₀ A₁ (fun k => m k ω) L) := by
  apply measurable_to_countable'
  intro k
  have he : {ω | bandStop e A₀ A₁ (fun j => m j ω) L = k} =
      ({ω | L ≤ k} ∪ {ω | m k ω < 1/2-bandBoundary e A₀ k} ∪
        {ω | 1/2+bandBoundary e A₁ k < m k ω}) ∩
      ⋂ j, ⋂ (_ : j < k), ({ω | j < L} ∩
        {ω | 1/2-bandBoundary e A₀ j ≤ m j ω} ∩ {ω | m j ω ≤ 1/2+bandBoundary e A₁ j}) := by
    ext ω
    simp only [mem_ofPred_eq,mem_inter_iff,mem_union,mem_iInter,bandStop_eq_iff e,and_assoc,or_assoc]
  change MeasurableSet {ω | bandStop e A₀ A₁ (fun j => m j ω) L = k}
  rw [he]
  apply MeasurableSet.inter
  · exact ((MeasurableSet.const _).union (measurableSet_lt (hm k) measurable_const)).union
      (measurableSet_lt measurable_const (hm k))
  · exact MeasurableSet.iInter fun j => MeasurableSet.iInter fun _ =>
      ((MeasurableSet.const _).inter (measurableSet_le measurable_const (hm j))).inter
        (measurableSet_le (hm j) measurable_const)

theorem measurable_bandDecision {Ω : Type*} [MeasurableSpace Ω]
    (e : ℕ) (A₀ A₁ : ℕ → ℝ) (m : ℕ → Ω → ℝ) (hm : ∀ k, Measurable (m k)) (L : ℕ) :
    Measurable (fun ω => bandDecision e A₀ A₁ (fun k => m k ω) L) := by
  have hmean : Measurable (fun ω => m (bandStop e A₀ A₁ (fun k => m k ω) L) ω) :=
    (measurable_from_prod_countable_left (f := fun z : Ω × ℕ => m z.2 z.1) (fun k => hm k)).comp
      (measurable_id.prodMk (measurable_bandStop e A₀ A₁ m hm L))
  exact Measurable.ite (measurableSet_lt measurable_const hmean) measurable_const measurable_const

theorem bandStop_congr_until (e : ℕ) (A₀ A₁ : ℕ → ℝ) (m m' : ℕ → ℝ) (L : ℕ)
    (hm : ∀ k ≤ bandStop e A₀ A₁ m L, m' k = m k) :
    bandStop e A₀ A₁ m' L = bandStop e A₀ A₁ m L := by
  apply (bandStop_eq_iff e A₀ A₁ m' L _).2
  constructor
  · simpa only [hm _ le_rfl] using bandStop_spec e A₀ A₁ m L
  · intro k hk
    simpa only [hm k hk.le] using bandStop_min e A₀ A₁ m L k hk

def bandCost (e : ℕ) (A₀ A₁ : ℕ → ℝ) (L : ℕ) (ω : ℕ → Bool) : ℕ :=
  2 ^ (e+bandStop e A₀ A₁ (fun k => dyadicMean Tier2.observations (e+k) ω) L)

def bandValue (e : ℕ) (A₀ A₁ : ℕ → ℝ) (L : ℕ) (ω : ℕ → Bool) : ℝ :=
  bandDecision e A₀ A₁ (fun k => dyadicMean Tier2.observations (e+k) ω) L

theorem band_prefix_ext (e : ℕ) (A₀ A₁ : ℕ → ℝ) (L : ℕ) (ω ω' : ℕ → Bool)
    (h : Tier2.tapePrefix (bandCost e A₀ A₁ L ω) ω = Tier2.tapePrefix (bandCost e A₀ A₁ L ω) ω') :
    bandCost e A₀ A₁ L ω' = bandCost e A₀ A₁ L ω ∧ bandValue e A₀ A₁ L ω' = bandValue e A₀ A₁ L ω := by
  let m := fun k => dyadicMean Tier2.observations (e+k) ω
  let m' := fun k => dyadicMean Tier2.observations (e+k) ω'
  have hm (k : ℕ) (hk : k ≤ bandStop e A₀ A₁ m L) : m' k = m k :=
    (BlindUpper.dyadicMean_prefix_ext _ ω ω' h (e+k) (Nat.pow_le_pow_right (by omega : 0 < 2) (Nat.add_le_add_left hk e))).symm
  have he := bandStop_congr_until e A₀ A₁ m m' L hm
  constructor
  · exact congrArg (fun k : ℕ => 2^(e+k)) he
  · change bandDecision e A₀ A₁ m' L = bandDecision e A₀ A₁ m L
    unfold bandDecision
    rw [he,hm _ le_rfl]

theorem measurable_bandCost (e : ℕ) (A₀ A₁ : ℕ → ℝ) (L : ℕ) : Measurable (bandCost e A₀ A₁ L) :=
  (measurable_of_countable (fun n : ℕ => 2^(e+n))).comp
    (measurable_bandStop e A₀ A₁ (fun k => dyadicMean Tier2.observations (e+k))
      (fun _k => measurable_prefixMean Tier2.measurable_observations _) L)

theorem measurable_bandValue (e : ℕ) (A₀ A₁ : ℕ → ℝ) (L : ℕ) : Measurable (bandValue e A₀ A₁ L) :=
  measurable_bandDecision e A₀ A₁ (fun k => dyadicMean Tier2.observations (e+k))
    (fun _k => measurable_prefixMean Tier2.measurable_observations _) L

def bandProcedure (e : ℕ) (A₀ A₁ : ℕ → ℝ) (L : ℕ) : StoppedProcedure Unit ℝ :=
  BlindUpper.finiteStoppedProcedure (fun z => bandCost e A₀ A₁ L z.2) (fun z => bandValue e A₀ A₁ L z.2)
    ((measurable_bandCost e A₀ A₁ L).comp measurable_snd)
    ((measurable_bandValue e A₀ A₁ L).comp measurable_snd)
    (fun _ ω ω' h => band_prefix_ext e A₀ A₁ L ω ω' h)

theorem bandCost_pos (e : ℕ) (A₀ A₁ : ℕ → ℝ) (L : ℕ) (ω : ℕ → Bool) : 0 < bandCost e A₀ A₁ L ω :=
  Nat.two_pow_pos _

theorem bandCost_le (e : ℕ) (A₀ A₁ : ℕ → ℝ) (L : ℕ) (ω : ℕ → Bool) : bandCost e A₀ A₁ L ω ≤ 2^(e+L) :=
  Nat.pow_le_pow_right (by omega : 0 < 2) (Nat.add_le_add_left (bandStop_le e _ _ _ _) e)

end ThresholdHC.RareAboveTwo
