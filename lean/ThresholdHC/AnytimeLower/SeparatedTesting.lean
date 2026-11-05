import ThresholdHC.AnytimeLower.CrossingEvents

noncomputable section
open MeasureTheory InformationTheory Real Set Filter
open scoped ENNReal Topology
namespace ThresholdHC.AnytimeLower

def thresholdEvents {Ω : Type} (z : ℕ → Ω → ℝ) (θ : ℝ) (a : ℕ → ℝ) : ℕ → Set Ω :=
  fun k => {x | θ+a k/2 < z k x}

theorem accuracy_firstCrossing {Ω : Type} (z : ℕ → Ω → ℝ)
    (θ : ℝ) (a t : ℕ → ℝ) (ha : ∀ i, 0 < a i)
    (hsep : ∀ i k, i < k → 3*a k ≤ a i) (hw : ∀ i, t i < a i/6)
    (k : ℕ) (x : Ω) (hx : ∀ i, |z i x-(θ+a k)| ≤ t i) :
    x ∈ firstCrossing (thresholdEvents z θ a) k := by
  rw [mem_firstCrossing]
  constructor
  · have hh := (abs_le.mp (hx k)).1
    change θ+a k/2 < z k x
    linarith [ha k,hw k]
  · intro i hi
    have hh := (abs_le.mp (hx i)).2
    change ¬θ+a i/2 < z i x
    have hs := hsep i k hi
    linarith [hw i]

theorem accuracy_no_crossing {Ω : Type} (z : ℕ → Ω → ℝ)
    (θ : ℝ) (a t : ℕ → ℝ) (ha : ∀ i, 0 < a i) (hw : ∀ i, t i < a i/6)
    (x : Ω) (hx : ∀ i, |z i x-θ| ≤ t i) :
    x ∉ ⋃ k, thresholdEvents z θ a k := by
  intro hm
  obtain ⟨k,hk⟩ := Set.mem_iUnion.mp hm
  have hh := (abs_le.mp (hx k)).2
  change θ+a k/2 < z k x at hk
  linarith [hw k,ha k]

/-- One separated alternative at each scale suffices. Earlier estimates can
be reconstructed from the current observed prefix, and observations need not
be independent. The asserted information summability follows from simultaneous
accuracy and a width below one sixth of every mean displacement. -/
theorem separated_accuracy_summable {Ω : Type} [MeasurableSpace Ω]
    {X : ℕ → Type} [∀ k, MeasurableSpace (X k)]
    (Q : Measure Ω) [IsProbabilityMeasure Q]
    (P : ℕ → Measure Ω) [∀ k, IsProbabilityMeasure (P k)]
    (z : ℕ → Ω → ℝ) (hz : ∀ k, Measurable (z k))
    (obs : ∀ k, Ω → X k) (hobs : ∀ k, Measurable (obs k))
    (readback : ∀ k, ℕ → X k → ℝ) (hr : ∀ k i, Measurable (readback k i))
    (hread : ∀ k i, i ≤ k → ∀ x, readback k i (obs k x) = z i x)
    (θ : ℝ) (a t : ℕ → ℝ) (ha : ∀ i, 0 < a i)
    (hsep : ∀ i k, i < k → 3*a k ≤ a i) (hw : ∀ i, t i < a i/6)
    {δ : ℝ} (hd : 0 ≤ δ ∧ δ ≤ 1/2)
    (hbase : 1-δ ≤ Q.real {x | ∀ i, |z i x-θ| ≤ t i})
    (halt : ∀ k, 1-δ ≤ (P k).real {x | ∀ i, |z i x-(θ+a k)| ≤ t i})
    (K : ℕ → ℝ) (hK : ∀ k, 0 ≤ K k)
    (hkl : ∀ k, klDiv ((P k).map (obs k)) (Q.map (obs k)) ≤ ENNReal.ofReal (K k)) :
    Summable (fun k => exp (-K k/(1-δ))) := by
  let E := thresholdEvents z θ a
  have hE (k : ℕ) : MeasurableSet (E k) :=
    measurableSet_lt measurable_const (hz k)
  let A (k : ℕ) := firstCrossing (thresholdEvents (readback k) θ a) k
  have hA (k : ℕ) : MeasurableSet (A k) :=
    measurableSet_firstCrossing _ (fun i => measurableSet_lt measurable_const (hr k i)) k
  have hpre (k : ℕ) : obs k ⁻¹' A k = firstCrossing E k := by
    ext x
    simp only [Set.mem_preimage,A,mem_firstCrossing,E,thresholdEvents,Set.mem_ofPred_eq]
    rw [hread k k le_rfl x]
    constructor <;> rintro ⟨hk,hi⟩ <;> refine ⟨hk,?_⟩
    · intro i hik
      simpa only [hread k i hik.le x] using hi i hik
    · intro i hik
      simpa only [hread k i hik.le x] using hi i hik
  have hp (k : ℕ) : 1-δ ≤ (P k).real (firstCrossing E k) :=
    (halt k).trans (measureReal_mono (fun x hx =>
      accuracy_firstCrossing z θ a t ha hsep hw k x hx))
  have hS : MeasurableSet {x | ∀ i, |z i x-θ| ≤ t i} := by
    simp only [Set.ofPred_forall]
    exact MeasurableSet.iInter (fun i => measurableSet_le ((hz i).sub_const θ).abs measurable_const)
  have he : Q.real (⋃ k, E k) ≤ δ := by
    have hh : (⋃ k, E k) ⊆ {x | ∀ i, |z i x-θ| ≤ t i}ᶜ := by
      intro x hx hg
      exact accuracy_no_crossing z θ a t ha hw x hg hx
    have hh' := measureReal_mono (μ := Q) hh
    rw [probReal_compl_eq_one_sub hS] at hh'
    linarith
  exact firstCrossing_information_summable Q P E hE obs hobs A hA hpre hd K hK hp he hkl

end ThresholdHC.AnytimeLower
