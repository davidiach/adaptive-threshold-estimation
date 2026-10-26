import ThresholdHC.Statements2
import ThresholdHC.Uniform713.Classifier

noncomputable section

namespace ThresholdHC.Tier2

open ThresholdHC Uniform713

def finiteMean {M : ℕ} (x : Fin M → Bool) (j : ℕ) : ℝ :=
  (succCount x (2 ^ j) : ℝ) / (2 ^ j : ℝ)

def finiteBoundary (k1 k2 : ℝ) (j L : ℕ) : ℝ := thrK k1 k2 (2 ^ j) (2 ^ L)

def boundary : ℕ → ℕ → ℝ := finiteBoundary 1 1

theorem finiteBoundary_nonneg (k1 k2 : ℝ) (j L : ℕ) :
    0 ≤ finiteBoundary k1 k2 j L := Real.sqrt_nonneg _

theorem findSome_range_first {α : Type*} (f : ℕ → Option α) (s L : ℕ) (a : α)
    (hsL : s ≤ L) (hs : f s = some a) (hprior : ∀ j < s, f j = none) :
    (List.range (L + 1)).findSome? f = some a := by
  have hn : (List.range s).findSome? f = none := by
    rw [List.findSome?_eq_none_iff]
    intro j hj
    exact hprior j (List.mem_range.mp hj)
  have hh : (List.range (s + 1)).findSome? f = some a := by
    rw [List.range_succ, List.findSome?_append]
    simp [hn, hs]
  have hp : List.range (s + 1) <+: List.range (L + 1) := by
    simpa only [List.take_range, Nat.min_eq_left (Nat.add_le_add_right hsL 1)] using
      List.take_prefix (s + 1) (List.range (L + 1))
  exact hp.findSome?_eq_some hh

theorem checkpoint_before_firstStop (k1 k2 : ℝ) (L : ℕ) {M : ℕ}
    (x : Fin M → Bool) (j : ℕ)
    (hj : j < firstStop (finiteBoundary k1 k2) (finiteMean x) L) :
    checkpointK k1 k2 L j x = none := by
  have h := firstStop_min (finiteBoundary k1 k2) (finiteMean x) L j hj
  have hab := abs_le.mp h.2
  have hpos : ¬ finiteMean x j - 1 / 2 > finiteBoundary k1 k2 j L :=
    not_lt_of_ge hab.2
  have hneg : ¬ 1 / 2 - finiteMean x j > finiteBoundary k1 k2 j L := by
    linarith [hab.1]
  simp only [checkpointK, h.1, ↓reduceIte]
  change (if finiteMean x j - 1 / 2 > finiteBoundary k1 k2 j L then some true
    else if 1 / 2 - finiteMean x j > finiteBoundary k1 k2 j L then some false else none) =
    (none : Option Bool)
  rw [ite_eq_right hpos, ite_eq_right hneg]

theorem checkpoint_at_firstStop (k1 k2 : ℝ) (L : ℕ) {M : ℕ} (x : Fin M → Bool) :
    checkpointK k1 k2 L (firstStop (finiteBoundary k1 k2) (finiteMean x) L) x =
      some (decide (1 / 2 < finiteMean x (firstStop (finiteBoundary k1 k2) (finiteMean x) L))) := by
  classical
  let s := firstStop (finiteBoundary k1 k2) (finiteMean x) L
  have hsL : s ≤ L := firstStop_le _ _ _
  have hb : 0 ≤ finiteBoundary k1 k2 s L := finiteBoundary_nonneg _ _ _ _
  change checkpointK k1 k2 L s x = some (decide (1 / 2 < finiteMean x s))
  by_cases hs : s = L
  · rw [hs]
    simp only [checkpointK, lt_self_iff_false, ↓reduceIte]
    change (if 1 / 2 < finiteMean x L then some true else some false) =
      some (decide (1 / 2 < finiteMean x L))
    by_cases hm : 1 / 2 < finiteMean x L <;>
      simp only [hm, ↓reduceIte, decide_true, decide_false]
  · have hlt : s < L := lt_of_le_of_ne hsL hs
    have hc : finiteBoundary k1 k2 s L < |finiteMean x s - 1 / 2| :=
      (firstStop_spec (finiteBoundary k1 k2) (finiteMean x) L).resolve_left (by omega)
    by_cases hm : 1 / 2 < finiteMean x s
    · rw [abs_of_pos (by linarith)] at hc
      have hp : finiteMean x s - 1 / 2 > finiteBoundary k1 k2 s L := hc
      simp only [checkpointK, hlt, ↓reduceIte]
      change (if finiteMean x s - 1 / 2 > finiteBoundary k1 k2 s L then some true
        else if 1 / 2 - finiteMean x s > finiteBoundary k1 k2 s L then some false else none) =
        some (decide (1 / 2 < finiteMean x s))
      simp only [hp, hm, ↓reduceIte, decide_true]
    · rw [abs_of_nonpos (by linarith)] at hc
      have hp : ¬ finiteMean x s - 1 / 2 > finiteBoundary k1 k2 s L := by linarith
      have hn : 1 / 2 - finiteMean x s > finiteBoundary k1 k2 s L := by linarith
      simp only [checkpointK, hlt, ↓reduceIte]
      change (if finiteMean x s - 1 / 2 > finiteBoundary k1 k2 s L then some true
        else if 1 / 2 - finiteMean x s > finiteBoundary k1 k2 s L then some false else none) =
        some (decide (1 / 2 < finiteMean x s))
      simp only [hp, hn, hm, ↓reduceIte, decide_false]

theorem classifyK_eq_firstStop (k1 k2 : ℝ) (L : ℕ) {M : ℕ} (x : Fin M → Bool) :
    classifyK k1 k2 L x =
      (decide (1 / 2 < finiteMean x (firstStop (finiteBoundary k1 k2) (finiteMean x) L)),
        2 ^ firstStop (finiteBoundary k1 k2) (finiteMean x) L) := by
  classical
  let s := firstStop (finiteBoundary k1 k2) (finiteMean x) L
  have heq := findSome_range_first
    (fun j => (checkpointK k1 k2 L j x).map (fun b => (b, 2 ^ j))) s L
    (decide (1 / 2 < finiteMean x s), 2 ^ s) (firstStop_le _ _ _)
    (by simp [s, checkpoint_at_firstStop])
    (fun j hj => by simp [checkpoint_before_firstStop k1 k2 L x j hj])
  unfold classifyK
  rw [heq]

theorem zK_eq_firstDecision (k1 k2 : ℝ) (L : ℕ) {M : ℕ} (x : Fin M → Bool) :
    zK k1 k2 L x = firstDecision (finiteBoundary k1 k2) (finiteMean x) L := by
  classical
  simp only [zK, classifyK_eq_firstStop, firstDecision, decide_eq_true_eq]

theorem classifyK_work_eq_cap (k1 k2 : ℝ) (L : ℕ) {M : ℕ} (x : Fin M → Bool) :
    ((classifyK k1 k2 L x).2 : ℝ) =
      cap (firstStop (finiteBoundary k1 k2) (finiteMean x) L) := by
  rw [classifyK_eq_firstStop]
  simp [cap]

end ThresholdHC.Tier2

