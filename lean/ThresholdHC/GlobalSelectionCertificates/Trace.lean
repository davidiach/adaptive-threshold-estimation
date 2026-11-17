import ThresholdHC.GlobalSelectionCertificates.Menu
import ThresholdHC.BandCostSelection.Comparison
import ThresholdHC.FiniteSelectionApproximation.Bins

namespace ThresholdHC.GlobalSelectionCertificates
open ThresholdHC.FiniteLawCertificates

def savingPositiveQ (x y B : ℚ) : Prop :=
  if x = 0 then 0 < y else if y = 0 then 0 < x
  else if (0 < x ↔ 0 < y) then 0 < x
  else if 0 < x then 0 < B*x*x-y*y else B*x*x-y*y < 0

instance instDecidableSavingPositiveQ (x y B : ℚ) : Decidable (savingPositiveQ x y B) := by
  unfold savingPositiveQ; infer_instance

def savingLE (f s g t B : ℚ) : Bool := decide (¬savingPositiveQ (f-g) (s-t) B)

theorem savingLE_sound {f s g t B : ℚ} (hB : 0 < B) (h : savingLE f s g t B = true) :
    (f:ℝ)+(s:ℝ)/Real.sqrt (B:ℝ) ≤ (g:ℝ)+(t:ℝ)/Real.sqrt (B:ℝ) := by
  have he (x y : ℚ) : savingPositiveQ x y B ↔
      ThresholdHC.BandCostSelection.savingPositive (x:ℝ) (y:ℝ) (B:ℝ) := by
    unfold savingPositiveQ ThresholdHC.BandCostSelection.savingPositive
    norm_cast
  simp only [savingLE, decide_eq_true_eq] at h
  rw [he, ThresholdHC.BandCostSelection.savingPositive_iff _ _ (by exact_mod_cast hB)] at h
  push_cast at h
  rw [sub_div] at h
  linarith

def mergeMask {n : ℕ} (s t : Fin n → Bool) : Fin n → Bool := fun i => s i || t i

def extendMasks {n : ℕ} (previous options : List (Fin n → Bool)) : List (Fin n → Bool) :=
  previous.flatMap (fun s => options.map (mergeMask s))

def fixedSaving {n : ℕ} (g w : Fin n → ℚ) (B : ℚ) (s : Fin n → Bool) : ℚ :=
  ∑ i, if s i && decide (B*(g i)^2 ≤ 1) then w i else 0

def scaledSaving {n : ℕ} (g w : Fin n → ℚ) (B : ℚ) (s : Fin n → Bool) : ℚ :=
  ∑ i, if s i && decide (1 < B*(g i)^2) then w i/g i else 0

/-- All kept states are candidates, and every candidate has a same-key representative
with at least as much exact saved ordinary cost. Keys are unique in the retained list. -/
def stageCheck {n : ℕ} {κ : Type*} [DecidableEq κ]
    (key : (Fin n → Bool) → κ) (f t : (Fin n → Bool) → ℚ) (B : ℚ)
    (previous options kept : List (Fin n → Bool)) : Bool :=
  decide (kept.Nodup ∧ (kept.map key).Nodup ∧
    (∀ s ∈ kept, s ∈ extendMasks previous options) ∧
    ∀ s ∈ extendMasks previous options, ∃ u ∈ kept,
      key s = key u ∧ savingLE (f s) (t s) (f u) (t u) B = true)

theorem stageCheck_sound {n : ℕ} {κ : Type*} [DecidableEq κ]
    (key : (Fin n → Bool) → κ) (f t : (Fin n → Bool) → ℚ) (B : ℚ) (hB : 0 < B)
    (previous options kept : List (Fin n → Bool))
    (h : stageCheck key f t B previous options kept = true) :
    kept.Nodup ∧ (kept.map key).Nodup ∧
    (∀ s ∈ kept, s ∈ extendMasks previous options) ∧
    ∀ s ∈ extendMasks previous options, ∃ u ∈ kept,
      key s = key u ∧ (f s:ℝ)+(t s:ℝ)/Real.sqrt (B:ℝ) ≤
        (f u:ℝ)+(t u:ℝ)/Real.sqrt (B:ℝ) := by
  simp only [stageCheck, decide_eq_true_eq] at h
  refine ⟨h.1,h.2.1,h.2.2.1,?_⟩
  intro s hs
  obtain ⟨u,hu,hkey,hle⟩ := h.2.2.2 s hs
  exact ⟨u,hu,hkey,savingLE_sound hB hle⟩

def runCheck {n : ℕ} {κ : Type*} [DecidableEq κ]
    (key : (Fin n → Bool) → κ) (f t : (Fin n → Bool) → ℚ) (B : ℚ) :
    List (Fin n → Bool) → List (List (Fin n → Bool)) → List (List (Fin n → Bool)) → Bool
  | _, [], [] => true
  | previous, options::menus, kept::stages =>
      stageCheck key f t B previous options kept && runCheck key f t B kept menus stages
  | _, _, _ => false

/-- The transcript's exact candidate-extension count, before each trimming step. -/
def transitionCount {α : Type*} : List α → List (List α) → List (List α) → ℕ
  | _, [], _ => 0
  | _, _, [] => 0
  | previous, options::menus, kept::stages =>
      previous.length*options.length + transitionCount kept menus stages

def peakCount {α : Type*} (initial : List α) (stages : List (List α)) : ℕ :=
  (initial.length::stages.map List.length).foldl max 0

theorem runCheck_lengths {n : ℕ} {κ : Type*} [DecidableEq κ]
    (key : (Fin n → Bool) → κ) (f t : (Fin n → Bool) → ℚ) (B : ℚ)
    (previous : List (Fin n → Bool)) (menus stages : List (List (Fin n → Bool)))
    (h : runCheck key f t B previous menus stages = true) : menus.length = stages.length := by
  induction menus generalizing previous stages with
  | nil => cases stages <;> simp_all [runCheck]
  | cons options menus ih =>
    cases stages with
    | nil => simp [runCheck] at h
    | cons kept stages =>
      simp only [runCheck, Bool.and_eq_true] at h
      simpa using ih kept stages h.2

theorem rational_same_cell {r x y : ℚ} {M : ℕ} (hr : 0 < r) (hM : 0 < M)
    (hx : 0 ≤ x) (hy : 0 ≤ y)
    (he : ThresholdHC.FiniteSelectionApproximation.rationalKey r M x =
      ThresholdHC.FiniteSelectionApproximation.rationalKey r M y) :
    ThresholdHC.SelectionApproximation.Close (1+1/(M:ℝ)) (x:ℝ) (y:ℝ) := by
  rw [ThresholdHC.FiniteSelectionApproximation.rationalKey_cast,
    ThresholdHC.FiniteSelectionApproximation.rationalKey_cast] at he
  exact ThresholdHC.FiniteSelectionApproximation.binKey_valid (by exact_mod_cast hr) hM
    _ _ (by exact_mod_cast hx) (by exact_mod_cast hy) he

end ThresholdHC.GlobalSelectionCertificates
