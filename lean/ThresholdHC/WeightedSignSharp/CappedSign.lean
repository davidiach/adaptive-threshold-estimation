import ThresholdHC.WeightedSignSharp.Specification
import ThresholdHC.PsiNull.StoppedKL
import ThresholdHC.BlindUpper.FiniteProcedure

/-! The stopping time of a sign test capped at a deterministic level `N`.

The capped time `min τ N` is a legal stopped procedure on the same seed and
tape, so the exact stopped KL chain rule `PsiNull.capped_transcript_kl`
applies to it. The terminal event `{τ ≤ N, output minus}` is a measurable
event of the capped transcript. No termination is assumed under any law. -/

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace ThresholdHC.WeightedSignSharp
open ThresholdHC.CriticalEntropy

/-- Agreement of the first `k` flips fixes every event `τ ≤ n` with `n ≤ k`. -/
theorem signTest_stop_le_iff_of_prefix {R : Type} [MeasurableSpace R] (A : SignTest R)
    (r : R) (ω ω' : ℕ → Bool) {k n : ℕ} (hn : n ≤ k)
    (h : Tier2.tapePrefix k ω = Tier2.tapePrefix k ω') :
    A.stop (r, ω) ≤ n ↔ A.stop (r, ω') ≤ n := by
  have hp : Tier2.tapePrefix n ω = Tier2.tapePrefix n ω' := prefix_eq_restrict h hn
  constructor
  · intro hs
    have hm := (A.observable n (A.output (r, ω)) (r, ω)).mpr ⟨hs, rfl⟩
    change (r, Tier2.tapePrefix n ω) ∈ _ at hm
    rw [hp] at hm
    exact ((A.observable n _ (r, ω')).mp hm).1
  · intro hs
    have hm := (A.observable n (A.output (r, ω')) (r, ω')).mpr ⟨hs, rfl⟩
    change (r, Tier2.tapePrefix n ω') ∈ _ at hm
    rw [← hp] at hm
    exact ((A.observable n _ (r, ω)).mp hm).1

theorem enat_cast_min (a b : ℕ) : ((min a b : ℕ) : ℕ∞) = min (a : ℕ∞) (b : ℕ∞) :=
  Nat.mono_cast.map_min

/-- A capped extended time is fixed by its comparisons up to its own value. -/
theorem min_toNat_eq_of_le_iff (x y : ℕ∞) (N : ℕ)
    (h : ∀ n : ℕ, n ≤ (min x (N : ℕ∞)).toNat → (x ≤ n ↔ y ≤ n)) :
    (min y (N : ℕ∞)).toNat = (min x (N : ℕ∞)).toNat := by
  induction x using ENat.recTopCoe with
  | top =>
    induction y using ENat.recTopCoe with
    | top => rfl
    | coe s =>
      have h1 := h N (by simp)
      simp only [min_eq_right le_top, ENat.toNat_natCast, top_le_iff, ENat.natCast_ne_top,
        false_iff, Nat.cast_le, not_le] at h1 ⊢
      rw [← enat_cast_min, ENat.toNat_natCast]
      omega
  | coe t =>
    induction y using ENat.recTopCoe with
    | top =>
      have h1 := h (min t N) (by rw [← enat_cast_min, ENat.toNat_natCast])
      simp only [Nat.cast_le, top_le_iff, ENat.natCast_ne_top, iff_false, not_le] at h1
      rw [min_eq_right le_top, ← enat_cast_min, ENat.toNat_natCast, ENat.toNat_natCast]
      omega
    | coe s =>
      have h1 := h (min t N) (by rw [← enat_cast_min, ENat.toNat_natCast])
      have h2 := h (min s (min t N)) (by
        rw [← enat_cast_min, ENat.toNat_natCast]; exact min_le_right _ _)
      simp only [Nat.cast_le] at h1 h2
      rw [← enat_cast_min, ← enat_cast_min, ENat.toNat_natCast, ENat.toNat_natCast]
      by_cases ht : t ≤ N
      · have hk : min t N = t := min_eq_left ht
        rw [hk] at h1 h2
        have hs : s ≤ t := h1.mp le_rfl
        have hts : t ≤ s := by
          have := h2.mpr (by omega)
          omega
        omega
      · have hk : min t N = N := min_eq_right (by omega)
        rw [hk] at h1
        have hs : ¬ s ≤ N := fun hs => ht (h1.mpr hs)
        omega

/-- The stopping count capped at `N`. -/
def cappedCost {R : Type} [MeasurableSpace R] (A : SignTest R) (N : ℕ)
    (z : R × (ℕ → Bool)) : ℕ :=
  (min (A.stop z) (N : ℕ∞)).toNat

theorem measurable_cappedCost {R : Type} [MeasurableSpace R] (A : SignTest R) (N : ℕ) :
    Measurable (cappedCost A N) :=
  (measurable_of_countable (fun x : ℕ∞ => (min x (N : ℕ∞)).toNat)).comp A.measurable_stop

theorem cappedCost_le {R : Type} [MeasurableSpace R] (A : SignTest R) (N : ℕ)
    (z : R × (ℕ → Bool)) : cappedCost A N z ≤ N :=
  ENat.toNat_le_of_le_natCast (min_le_right _ _)

theorem cappedCost_cast {R : Type} [MeasurableSpace R] (A : SignTest R) (N : ℕ)
    (z : R × (ℕ → Bool)) : (cappedCost A N z : ℕ∞) = min (A.stop z) (N : ℕ∞) :=
  ENat.natCast_toNat (ne_top_of_le_ne_top (ENat.natCast_ne_top N) (min_le_right _ _))

theorem cappedCost_ext {R : Type} [MeasurableSpace R] (A : SignTest R) (N : ℕ)
    (r : R) (ω ω' : ℕ → Bool)
    (h : Tier2.tapePrefix (cappedCost A N (r, ω)) ω =
      Tier2.tapePrefix (cappedCost A N (r, ω)) ω') :
    cappedCost A N (r, ω') = cappedCost A N (r, ω) :=
  min_toNat_eq_of_le_iff _ _ N (fun _ hn => signTest_stop_le_iff_of_prefix A r ω ω' hn h)

/-- The sign test stopped at `min τ N`, as a legal stopped procedure. -/
def cappedSignProcedure {R : Type} [MeasurableSpace R] (A : SignTest R) (N : ℕ) :
    StoppedProcedure R Unit :=
  BlindUpper.finiteStoppedProcedure (cappedCost A N) (fun _ => ())
    (measurable_cappedCost A N) measurable_const
    (fun r ω ω' h => ⟨cappedCost_ext A N r ω ω' h, rfl⟩)

theorem cappedSignProcedure_cap {R : Type} [MeasurableSpace R] (A : SignTest R) (N : ℕ)
    (z : R × (ℕ → Bool)) : (cappedSignProcedure A N).stop z ≤ N := by
  change ((cappedCost A N z : ℕ) : ℕ∞) ≤ (N : ℕ∞)
  exact Nat.cast_le.mpr (cappedCost_le A N z)

theorem cappedSign_work_le {R : Type} [MeasurableSpace R] (ν : Measure R)
    (p : unitInterval) (A : SignTest R) (N : ℕ) :
    expectedStoppedProcedureWork ν p (cappedSignProcedure A N) ≤
      expectedSignTestWork ν p A := by
  apply lintegral_mono
  intro z
  change (((cappedCost A N z : ℕ) : ℕ∞) : ℝ≥0∞) ≤ ((A.stop z : ℕ∞) : ℝ≥0∞)
  apply ENat.toENNReal_le.mpr
  rw [cappedCost_cast]
  exact min_le_left _ _

/-- Capped words whose stopped prefix lies in the minus-decision event. -/
def cappedFalseEvent {R : Type} [MeasurableSpace R] (A : SignTest R) (N : ℕ) :
    Set (R × CappedWord N) :=
  {x | (x.1, x.2.2) ∈ A.prefixEvent x.2.1.val false}

theorem measurable_cappedFalseEvent {R : Type} [MeasurableSpace R] (A : SignTest R)
    (N : ℕ) : MeasurableSet (cappedFalseEvent A N) := by
  have he : cappedFalseEvent A N = ⋃ w : CappedWord N,
      {r : R | (r, w.2) ∈ A.prefixEvent w.1.val false} ×ˢ {w} := by
    ext ⟨r, w⟩
    simp only [cappedFalseEvent, Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_prod,
      Set.mem_singleton_iff]
    constructor
    · intro h
      exact ⟨w, h, rfl⟩
    · rintro ⟨v, hv, rfl⟩
      exact hv
  rw [he]
  exact MeasurableSet.iUnion (fun w =>
    ((measurable_id.prodMk measurable_const) (A.measurable_prefixEvent _ _)).prod
      (measurableSet_singleton w))

theorem cappedTranscript_preimage_false {R : Type} [MeasurableSpace R] (A : SignTest R)
    (N : ℕ) :
    cappedTranscript (cappedSignProcedure A N) N ⁻¹' cappedFalseEvent A N =
      {z | A.stop z ≤ N ∧ A.output z = false} := by
  ext z
  rw [Set.mem_preimage, cappedTranscript_of_stop (cappedSignProcedure A N) N
    (cappedCost A N z) (cappedCost_le A N z) z rfl]
  change (z.1, Tier2.tapePrefix (cappedCost A N z) z.2) ∈
    A.prefixEvent (cappedCost A N z) false ↔ _
  rw [A.observable, Set.mem_ofPred_eq, cappedCost_cast, le_min_iff]
  simp only [le_refl, true_and]

end ThresholdHC.WeightedSignSharp
