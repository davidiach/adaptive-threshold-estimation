import ThresholdHC.GlobalSelectionCertificates.Trace
open ThresholdHC.GlobalSelectionCertificates
open MeasureTheory
open scoped ENNReal BigOperators
open ThresholdHC.Tier6 ThresholdHC.FiniteLawCertificates
open ThresholdHC.DeterministicCertificates ThresholdHC.EntropyTail

example {n : ℕ} (d : Fin n → Gap) (w : Fin n → ℚ)
    (hw : ∀ i, 0 < w i) : (atomicMeasure d w).support = Set.range d :=
  atomic_support d w hw

example {n : ℕ} (s : Fin n → Bool) :
    ∀ i, 0 ≤ fractions s i ∧ fractions s i ≤ 1 :=
  fractions_valid s

example {n m : ℕ} (g w : Fin n → ℚ) (labels : Fin m → ℕ)
    (bands : Fin n → ℕ) (ρ B : ℚ) (hg : ∀ i, 0 < g i ∧ g i ≤ 1/2)
    (hw : ∀ i, 0 < w i) (hsum : ∑ i, w i = 1)
    (hl : Function.Injective labels) (hc : ∀ i, ∃ j, inBand (g i) (labels j) = true)
    (hb : ∀ i, inBand (g i) (bands i) = true)
    (hρ : 0 < ρ) (hρ1 : ρ ≤ 1/4) (hB : 0 < B) :
    ∃ s : Fin n → Bool, suffixCheck g bands s = true ∧
      (selection (atomicMeasure (points g hg) w) (ρ:ℝ) (B:ℝ)).toReal =
        (objectiveExpr g w (fractions s) labels ρ B).eval :=
  suffix_attains g w labels bands ρ B hg hw hsum hl hc hb hρ hρ1 hB

example {n m : ℕ} (g w s : Fin n → ℚ) (labels : Fin m → ℕ)
    (ρ B : ℚ) (hg : ∀ i, 0 < g i ∧ g i ≤ 1/2) (hw : ∀ i, 0 ≤ w i)
    (hs : ∀ i, 0 ≤ s i ∧ s i ≤ 1) (hρ : 0 ≤ ρ) (hB : 0 < B)
    (hl : Function.Injective labels) (hc : ∀ i, ∃ j, inBand (g i) (labels j) = true) :
    (selection (atomicMeasure (points g hg) w) (ρ:ℝ) (B:ℝ)).toReal ≤
      (objectiveExpr g w s labels ρ B).eval :=
  selection_le_expr g w s labels ρ B hg hw hs hρ hB hl hc

example {α : Type*} (valid : α → Prop) (J : α → ℝ) (K : ℝ)
    (candidates : List α) (witness : α) (lower upper : ℚ)
    (hattains : ∃ s, valid s ∧ K = J s)
    (hcomplete : ∀ s, valid s → s ∈ candidates)
    (hlower : ∀ s ∈ candidates, (lower:ℝ) ≤ J s)
    (hfeasible : K ≤ J witness) (hupper : J witness ≤ (upper:ℝ)) :
    (lower:ℝ) ≤ K ∧ K ≤ J witness ∧ J witness ≤ (upper:ℝ) :=
  global_enclosure valid J K candidates witness lower upper hattains hcomplete hlower hfeasible hupper

example {α : Type*} (valid : α → Prop) (J : α → ℝ) (K : ℝ)
    (candidates : List α) (witness : α)
    (hattains : ∃ s, valid s ∧ K = J s)
    (hcomplete : ∀ s, valid s → s ∈ candidates)
    (hminimal : ∀ s ∈ candidates, J witness ≤ J s) (hfeasible : K ≤ J witness) :
    J witness = K :=
  global_optimality valid J K candidates witness hattains hcomplete hminimal hfeasible

example {K J : ℝ} {lo hi ε : ℚ}
    (hε : 0 ≤ ε) (h : (lo:ℝ) ≤ K ∧ K ≤ J ∧ J ≤ (hi:ℝ))
    (hstop : hi ≤ (1+ε)*lo) : J ≤ (1+(ε:ℝ))*K :=
  relative_certificate hε h hstop

example {f s g t B : ℚ} (hB : 0 < B) (h : savingLE f s g t B = true) :
    (f:ℝ)+(s:ℝ)/Real.sqrt (B:ℝ) ≤ (g:ℝ)+(t:ℝ)/Real.sqrt (B:ℝ) :=
  savingLE_sound hB h

example {n : ℕ} {κ : Type*} [DecidableEq κ]
    (key : (Fin n → Bool) → κ) (f t : (Fin n → Bool) → ℚ) (B : ℚ) (hB : 0 < B)
    (previous options kept : List (Fin n → Bool))
    (h : stageCheck key f t B previous options kept = true) :
    kept.Nodup ∧ (kept.map key).Nodup ∧
    (∀ s ∈ kept, s ∈ extendMasks previous options) ∧
    ∀ s ∈ extendMasks previous options, ∃ u ∈ kept,
      key s = key u ∧ (f s:ℝ)+(t s:ℝ)/Real.sqrt (B:ℝ) ≤
        (f u:ℝ)+(t u:ℝ)/Real.sqrt (B:ℝ) :=
  stageCheck_sound key f t B hB previous options kept h

example {n : ℕ} {κ : Type*} [DecidableEq κ]
    (key : (Fin n → Bool) → κ) (f t : (Fin n → Bool) → ℚ) (B : ℚ)
    (previous : List (Fin n → Bool)) (menus stages : List (List (Fin n → Bool)))
    (h : runCheck key f t B previous menus stages = true) : menus.length = stages.length :=
  runCheck_lengths key f t B previous menus stages h

example {r x y : ℚ} {M : ℕ} (hr : 0 < r) (hM : 0 < M)
    (hx : 0 ≤ x) (hy : 0 ≤ y)
    (he : ThresholdHC.FiniteSelectionApproximation.rationalKey r M x =
      ThresholdHC.FiniteSelectionApproximation.rationalKey r M y) :
    ThresholdHC.SelectionApproximation.Close (1+1/(M:ℝ)) (x:ℝ) (y:ℝ) :=
  rational_same_cell hr hM hx hy he
#print axioms ThresholdHC.GlobalSelectionCertificates.atomic_support
#print axioms ThresholdHC.GlobalSelectionCertificates.extendMasks
#print axioms ThresholdHC.GlobalSelectionCertificates.fixedSaving
#print axioms ThresholdHC.GlobalSelectionCertificates.fractions
#print axioms ThresholdHC.GlobalSelectionCertificates.fractions_valid
#print axioms ThresholdHC.GlobalSelectionCertificates.global_enclosure
#print axioms ThresholdHC.GlobalSelectionCertificates.global_optimality
#print axioms ThresholdHC.GlobalSelectionCertificates.instDecidableSavingPositiveQ
#print axioms ThresholdHC.GlobalSelectionCertificates.mergeMask
#print axioms ThresholdHC.GlobalSelectionCertificates.peakCount
#print axioms ThresholdHC.GlobalSelectionCertificates.rational_same_cell
#print axioms ThresholdHC.GlobalSelectionCertificates.relative_certificate
#print axioms ThresholdHC.GlobalSelectionCertificates.runCheck
#print axioms ThresholdHC.GlobalSelectionCertificates.runCheck_lengths
#print axioms ThresholdHC.GlobalSelectionCertificates.savingLE
#print axioms ThresholdHC.GlobalSelectionCertificates.savingLE_sound
#print axioms ThresholdHC.GlobalSelectionCertificates.savingPositiveQ
#print axioms ThresholdHC.GlobalSelectionCertificates.scaledSaving
#print axioms ThresholdHC.GlobalSelectionCertificates.selection_le_expr
#print axioms ThresholdHC.GlobalSelectionCertificates.stageCheck
#print axioms ThresholdHC.GlobalSelectionCertificates.stageCheck_sound
#print axioms ThresholdHC.GlobalSelectionCertificates.suffixCheck
#print axioms ThresholdHC.GlobalSelectionCertificates.suffix_attains
#print axioms ThresholdHC.GlobalSelectionCertificates.transitionCount
