import ThresholdHC.ContinuousObserved.QueryPrefix
import ThresholdHC.Tier5.CreationBase

noncomputable section
namespace ThresholdHC.ContinuousObserved
open ThresholdHC ThresholdHC.Tier3 ThresholdHC.Tier5

theorem deterministic_sign_weight {N : ℕ} (s t : Fin N → Bool) :
    (∏ i, if t i then (if s i then (1 : ℝ) else 0) else 1 - (if s i then 1 else 0)) =
      if t = s then 1 else 0 := by
  have he (i : Fin N) :
      (if t i then (if s i then (1 : ℝ) else 0) else 1 - (if s i then 1 else 0)) =
        if t i = s i then 1 else 0 := by
    cases t i <;> cases s i <;> norm_num
  simp_rw [he]
  rw [Fintype.prod_boole]
  simp only [show (∀ i, t i = s i) ↔ t = s from funext_iff.symm]

theorem deterministic_transcript {N n : ℕ} (pol : List Bool → Option (Fin N))
    (d : Fin N → ℝ) (s : Fin N → Bool) (w : Prefix n) :
    transcriptLaw pol d (fun i => if s i then 1 else 0) w =
      pathProb pol (fun i => 1 / 2 + (if s i then d i else -d i)) w := by
  unfold transcriptLaw
  simp_rw [deterministic_sign_weight]
  simp

def countableStep (pol : List Bool → Option ℕ) (p : ℕ → ℝ)
    (xs : List Bool) (o : Option Bool) : ℝ :=
  match pol xs,o with
  | none,none => 1
  | some i,some true => p i
  | some i,some false => 1 - p i
  | _,_ => 0

def countablePath {n : ℕ} (pol : List Bool → Option ℕ) (p : ℕ → ℝ) (w : Prefix n) : ℝ :=
  ∏ t, countableStep pol p (histBefore w t) (w t)

theorem capped_path {n : ℕ} (pol : List Bool → Option ℕ) (p : ℕ → ℝ) (w : Prefix n) :
    pathProb (capPolicy (coinCap n pol) pol) (fun i => p i.val) w = countablePath pol p w := by
  unfold pathProb countablePath
  apply Finset.prod_congr rfl
  intro t _
  cases hi : pol (histBefore w t) with
  | none => cases w t <;> simp [capPolicy,countableStep,hi]
  | some i =>
    have hb := selected_lt_coinCap pol w t i hi
    cases w t with
    | none => simp [capPolicy,countableStep,hi,hb]
    | some b => cases b <;> simp [capPolicy,countableStep,hi,hb]

theorem deterministic_creation {n : ℕ} (pol : List Bool → Option ℕ)
    (d : ℕ → ℝ) (s : ℕ → Bool) (w : Prefix n) :
    creationLaw pol d (fun i => if s i then 1 else 0) w =
      countablePath pol (fun i => 1 / 2 + (if s i then d i else -d i)) w := by
  rw [creationLaw,deterministic_transcript]
  exact capped_path pol (fun i => 1 / 2 + (if s i then d i else -d i)) w

theorem countablePath_cons {n : ℕ} (pol : List Bool → Option ℕ)
    (p : ℕ → ℝ) (o : Option Bool) (w : Prefix n) :
    countablePath pol p (Fin.cons o w) =
      countableStep pol p [] o * countablePath (fun xs => pol (o.toList ++ xs)) p w := by
  unfold countablePath
  rw [Fin.prod_univ_succ]
  simp only [CriticalEntropy.histBefore_cons_zero,CriticalEntropy.histBefore_cons_succ,
    Fin.cons_zero,Fin.cons_succ]
  rfl

end ThresholdHC.ContinuousObserved
