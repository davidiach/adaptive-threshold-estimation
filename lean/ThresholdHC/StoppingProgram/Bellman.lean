import Mathlib

/-! Finite stopping-tree optimization. Rewards and charges depend only on
depth and head count, but competing policies may depend on the ordered path.
The connection of these coefficients to statistical likelihoods is separate. -/

noncomputable section
open scoped BigOperators

namespace ThresholdHC.StoppingProgram

def StopTree : ℕ → Type
  | 0 => Unit
  | d+1 => Option (StopTree d × StopTree d)

instance stopTree_fintype (d : ℕ) : Fintype (StopTree d) := by
  induction d with
  | zero => exact inferInstanceAs (Fintype Unit)
  | succ d ih => exact inferInstanceAs (Fintype (Option (StopTree d × StopTree d)))

instance stopTree_nonempty (d : ℕ) : Nonempty (StopTree d) := by
  cases d
  · exact ⟨()⟩
  · exact ⟨none⟩

def treeScore (r w : ℕ → ℕ → ℝ) (κ : ℝ) : (d : ℕ) → ℕ → ℕ → StopTree d → ℝ
  | 0,n,k,_ => r n k
  | _d+1,n,k,none => r n k
  | d+1,n,k,some (a,b) => treeScore r w κ d (n+1) k a+treeScore r w κ d (n+1) (k+1) b-κ*w n k

def bellman (r w : ℕ → ℕ → ℝ) (κ : ℝ) : ℕ → ℕ → ℕ → ℝ
  | 0,n,k => r n k
  | d+1,n,k => max (r n k) (bellman r w κ d (n+1) k+bellman r w κ d (n+1) (k+1)-κ*w n k)

def optimalTree (r w : ℕ → ℕ → ℝ) (κ : ℝ) : (d : ℕ) → ℕ → ℕ → StopTree d
  | 0,_,_ => ()
  | d+1,n,k =>
    if bellman r w κ d (n+1) k+bellman r w κ d (n+1) (k+1)-κ*w n k ≤ r n k
    then none else some (optimalTree r w κ d (n+1) k, optimalTree r w κ d (n+1) (k+1))

theorem treeScore_le_bellman (r w : ℕ → ℕ → ℝ) (κ : ℝ) (d n k : ℕ) (a : StopTree d) :
    treeScore r w κ d n k a ≤ bellman r w κ d n k := by
  induction d generalizing n k with
  | zero => exact le_refl _
  | succ d ih =>
    cases a with
    | none => exact le_max_left _ _
    | some a =>
      exact (sub_le_sub_right (add_le_add (ih (n+1) k a.1) (ih (n+1) (k+1) a.2)) _).trans
        (le_max_right _ _)

theorem optimalTree_score (r w : ℕ → ℕ → ℝ) (κ : ℝ) (d n k : ℕ) :
    treeScore r w κ d n k (optimalTree r w κ d n k) = bellman r w κ d n k := by
  induction d generalizing n k with
  | zero => rfl
  | succ d ih =>
    by_cases h : bellman r w κ d (n+1) k+bellman r w κ d (n+1) (k+1)-κ*w n k ≤ r n k
    · have he : optimalTree r w κ (d+1) n k = (none : Option (StopTree d × StopTree d)) :=
        ite_eq_left h
      rw [he]
      exact (max_eq_left h).symm
    · have he : optimalTree r w κ (d+1) n k =
          some (optimalTree r w κ d (n+1) k, optimalTree r w κ d (n+1) (k+1)) := ite_eq_right h
      rw [he]
      simp only [treeScore, ih, bellman]
      exact (max_eq_right (le_of_not_ge h)).symm

def treeInformation (r : ℕ → ℕ → ℝ) : (d : ℕ) → ℕ → ℕ → StopTree d → ℝ
  | 0,n,k,_ => r n k
  | _d+1,n,k,none => r n k
  | d+1,n,k,some (a,b) => treeInformation r d (n+1) k a+treeInformation r d (n+1) (k+1) b

def treeWork (w : ℕ → ℕ → ℝ) : (d : ℕ) → ℕ → ℕ → StopTree d → ℝ
  | 0,_,_,_ => 0
  | _d+1,_,_,none => 0
  | d+1,n,k,some (a,b) => w n k+treeWork w d (n+1) k a+treeWork w d (n+1) (k+1) b

theorem treeScore_eq (r w : ℕ → ℕ → ℝ) (κ : ℝ) (d n k : ℕ) (a : StopTree d) :
    treeScore r w κ d n k a = treeInformation r d n k a-κ*treeWork w d n k a := by
  induction d generalizing n k with
  | zero => simp [treeScore,treeInformation,treeWork]
  | succ d ih =>
    cases a with
    | none => simp [treeScore,treeInformation,treeWork]
    | some a => simp only [treeScore,treeInformation,treeWork,ih]; ring

theorem treeWork_nonneg (w : ℕ → ℕ → ℝ) (hw : ∀ n k, 0 ≤ w n k)
    (d n k : ℕ) (a : StopTree d) : 0 ≤ treeWork w d n k a := by
  induction d generalizing n k with
  | zero => exact le_refl _
  | succ d ih =>
    cases a with
    | none => exact le_refl _
    | some a => exact add_nonneg (add_nonneg (hw n k) (ih (n+1) k a.1)) (ih (n+1) (k+1) a.2)

theorem treeWork_le (w : ℕ → ℕ → ℝ) (hw : ∀ n k, 0 ≤ w n k)
    (hadd : ∀ n k, k ≤ n → w (n+1) k+w (n+1) (k+1) = w n k)
    (d n k : ℕ) (hk : k ≤ n) (a : StopTree d) : treeWork w d n k a ≤ d*w n k := by
  induction d generalizing n k with
  | zero => simp [treeWork]
  | succ d ih =>
    cases a with
    | none => change 0 ≤ (d+1:ℕ)*w n k; positivity [hw n k]
    | some a =>
      have h := add_le_add (ih (n+1) k (by omega) a.1) (ih (n+1) (k+1) (by omega) a.2)
      rw [← mul_add, hadd n k hk] at h
      dsimp only [treeWork]
      push_cast
      linarith

def rootInformation (r : ℕ → ℕ → ℝ) (d : ℕ) (a : StopTree d × StopTree d) : ℝ :=
  treeInformation r d 1 0 a.1+treeInformation r d 1 1 a.2

def rootWork (w : ℕ → ℕ → ℝ) (d : ℕ) (a : StopTree d × StopTree d) : ℝ :=
  1+treeWork w d 1 0 a.1+treeWork w d 1 1 a.2

def rootBellman (r w : ℕ → ℕ → ℝ) (κ : ℝ) (d : ℕ) : ℝ :=
  bellman r w κ d 1 0+bellman r w κ d 1 1-κ

theorem rootWork_bounds (w : ℕ → ℕ → ℝ) (hw : ∀ n k, 0 ≤ w n k)
    (hadd : ∀ n k, k ≤ n → w (n+1) k+w (n+1) (k+1) = w n k) (hroot : w 0 0 = 1)
    (d : ℕ) (a : StopTree d × StopTree d) : 1 ≤ rootWork w d a ∧ rootWork w d a ≤ d+1 := by
  have hl := treeWork_nonneg w hw d 1 0 a.1
  have hr := treeWork_nonneg w hw d 1 1 a.2
  have hu := add_le_add (treeWork_le w hw hadd d 1 0 (by norm_num) a.1)
    (treeWork_le w hw hadd d 1 1 (by norm_num) a.2)
  rw [← mul_add, hadd 0 0 (by norm_num), hroot, mul_one] at hu
  unfold rootWork
  constructor <;> linarith

theorem rootBellman_maximum (r w : ℕ → ℕ → ℝ) (κ : ℝ) (d : ℕ) :
    (∀ a : StopTree d × StopTree d, rootInformation r d a-κ*rootWork w d a ≤ rootBellman r w κ d) ∧
    ∃ a : StopTree d × StopTree d, rootInformation r d a-κ*rootWork w d a = rootBellman r w κ d := by
  have he (a : StopTree d × StopTree d) : rootInformation r d a-κ*rootWork w d a =
      treeScore r w κ d 1 0 a.1+treeScore r w κ d 1 1 a.2-κ := by
    rw [treeScore_eq,treeScore_eq]
    unfold rootInformation rootWork
    ring
  refine ⟨fun a => ?_, ⟨(optimalTree r w κ d 1 0,optimalTree r w κ d 1 1), ?_⟩⟩
  · rw [he]
    exact sub_le_sub_right (add_le_add (treeScore_le_bellman r w κ d 1 0 a.1)
      (treeScore_le_bellman r w κ d 1 1 a.2)) κ
  · rw [he,optimalTree_score,optimalTree_score]
    rfl

theorem continuous_bellman (r w : ℕ → ℕ → ℝ) (d n k : ℕ) :
    Continuous (fun κ => bellman r w κ d n k) := by
  induction d generalizing n k with
  | zero => exact continuous_const
  | succ d ih =>
    exact continuous_const.max (((ih (n+1) k).add (ih (n+1) (k+1))).sub (continuous_id.mul continuous_const))

theorem continuous_rootBellman (r w : ℕ → ℕ → ℝ) (d : ℕ) : Continuous (fun κ => rootBellman r w κ d) :=
  ((continuous_bellman r w d 1 0).add (continuous_bellman r w d 1 1)).sub continuous_id

end ThresholdHC.StoppingProgram
