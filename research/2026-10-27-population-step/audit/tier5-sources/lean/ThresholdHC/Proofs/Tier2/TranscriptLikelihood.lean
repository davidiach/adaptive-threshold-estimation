import ThresholdHC.Proofs.Tier2.TranscriptBase

/-!
Finite likelihoods for adaptive, padded transcripts.

The sign mixture factors into one likelihood per coin. This yields the exact
next-observation distribution, common support for interior sign priors, and the
recurrence for expected query work.
-/

noncomputable section
namespace ThresholdHC.Proofs
open ThresholdHC Real
def obsProb (p : ℝ) (o : Option Bool) : ℝ := match o with
  | none => 0
  | some true => p
  | some false => 1-p

def pathValidity {m n : ℕ} (pol : List Bool → Option (Fin m)) (ω : Fin n → Option Bool) : ℝ :=
  ∏ t, if pol (histBefore ω t) = none then (if ω t = none then 1 else 0) else 1

def coinLike {m n : ℕ} (pol : List Bool → Option (Fin m)) (ω : Fin n → Option Bool)
    (i : Fin m) (p : ℝ) : ℝ :=
  ∏ t, if pol (histBefore ω t) = some i then obsProb p (ω t) else 1

theorem stepProb_factor {m : ℕ} (pol : List Bool → Option (Fin m)) (p : Fin m → ℝ)
    (h : List Bool) (o : Option Bool) :
    stepProb pol p h o =
      (if pol h = none then (if o = none then 1 else 0) else 1) *
        ∏ i, if pol h = some i then obsProb (p i) o else 1 := by
  classical
  cases he : pol h with
  | none => cases o <;> simp [stepProb, he]
  | some i =>
    simp only [he, Option.some_ne_none, ↓reduceIte, one_mul, Option.some.injEq]
    rw [Finset.prod_ite_eq]
    simp only [Finset.mem_univ, ↓reduceIte]
    cases o with
    | none => simp [stepProb, he, obsProb]
    | some b => cases b <;> simp [stepProb, he, obsProb]

theorem pathProb_factor {m n : ℕ} (pol : List Bool → Option (Fin m)) (p : Fin m → ℝ)
    (ω : Fin n → Option Bool) :
    pathProb pol p ω = pathValidity pol ω * ∏ i, coinLike pol ω i (p i) := by
  change (∏ t, stepProb pol p (histBefore ω t) (ω t)) = _
  simp_rw [stepProb_factor]
  rw [Finset.prod_mul_distrib, Finset.prod_comm]
  rfl

theorem coinLike_nonneg {m n : ℕ} (pol : List Bool → Option (Fin m)) (ω : Fin n → Option Bool)
    (i : Fin m) {p : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1) : 0 ≤ coinLike pol ω i p := by
  apply Finset.prod_nonneg
  intro t ht
  split_ifs
  · cases ω t with
    | none => simp [obsProb]
    | some b => cases b <;> simp [obsProb] <;> linarith
  · positivity

theorem pathValidity_nonneg {m n : ℕ} (pol : List Bool → Option (Fin m)) (ω : Fin n → Option Bool) :
    0 ≤ pathValidity pol ω := by
  apply Finset.prod_nonneg
  intro t ht
  split_ifs <;> norm_num

theorem transcriptLaw_factor {m n : ℕ} (pol : List Bool → Option (Fin m)) (d q : Fin m → ℝ)
    (ω : Fin n → Option Bool) :
    transcriptLaw pol d q ω = pathValidity pol ω * ∏ i,
      (q i * coinLike pol ω i (1/2+d i) + (1-q i)*coinLike pol ω i (1/2-d i)) := by
  unfold transcriptLaw
  simp_rw [pathProb_factor]
  calc
    _ = pathValidity pol ω * ∑ s : Fin m → Bool,
        ∏ i, (if s i then q i else 1-q i) *
          coinLike pol ω i (1/2+(if s i then d i else -d i)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro s hs
      rw [Finset.prod_mul_distrib]
      ring
    _ = _ := by
      congr 1
      rw [← Fintype.prod_sum (fun i : Fin m => fun b : Bool => (if b then q i else 1-q i) * coinLike pol ω i (1/2+(if b then d i else -d i)))]
      congr 1
      ext i
      simp [sub_eq_add_neg]

theorem sum_prod_coordinate {m : ℕ} (f : Fin m → Bool → ℝ) (g : Bool → ℝ) (i : Fin m) :
    (∑ s : Fin m → Bool, (∏ j, f j (s j))*g (s i)) =
      (∏ j ∈ Finset.univ.erase i, ∑ b : Bool, f j b) * (∑ b : Bool, f i b * g b) := by
  classical
  let f' : Fin m → Bool → ℝ := fun j b => f j b * (if j=i then g b else 1)
  have hprod (s : Fin m → Bool) : (∏ j, f' j (s j)) = (∏ j, f j (s j))*g (s i) := by
    dsimp [f']
    rw [Finset.prod_mul_distrib]
    simp
  rw [← show (∑ s, ∏ j, f' j (s j)) = _ from Finset.sum_congr rfl (fun s _ => hprod s)]
  rw [← Fintype.prod_sum, ← Finset.prod_erase_mul _ _ (Finset.mem_univ i)]
  congr 1
  · apply Finset.prod_congr rfl
    intro j hj
    simp [f', (Finset.mem_erase.mp hj).1]
  · simp [f']


def coinMix {m n : ℕ} (pol : List Bool → Option (Fin m)) (d q : Fin m → ℝ)
    (ω : Fin n → Option Bool) (i : Fin m) : ℝ :=
  q i * coinLike pol ω i (1/2+d i) + (1-q i)*coinLike pol ω i (1/2-d i)

def otherMass {m n : ℕ} (pol : List Bool → Option (Fin m)) (d q : Fin m → ℝ)
    (ω : Fin n → Option Bool) (i : Fin m) : ℝ :=
  pathValidity pol ω * ∏ j ∈ Finset.univ.erase i, coinMix pol d q ω j

theorem transcriptLaw_split {m n : ℕ} (pol : List Bool → Option (Fin m)) (d q : Fin m → ℝ)
    (ω : Fin n → Option Bool) (i : Fin m) :
    transcriptLaw pol d q ω = otherMass pol d q ω i * coinMix pol d q ω i := by
  rw [transcriptLaw_factor]
  change pathValidity pol ω * (∏ j, coinMix pol d q ω j) = _
  rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ i)]
  simp only [otherMass, mul_assoc]

theorem transcriptLaw_query {m n : ℕ} (pol : List Bool → Option (Fin m)) (d q : Fin m → ℝ)
    (ω : Fin n → Option Bool) (i : Fin m) (hi : pol (fullHist ω) = some i) (o : Option Bool) :
    transcriptLaw pol d q (Fin.snoc ω o) = otherMass pol d q ω i *
      (q i*coinLike pol ω i (1/2+d i)*obsProb (1/2+d i) o +
       (1-q i)*coinLike pol ω i (1/2-d i)*obsProb (1/2-d i) o) := by
  classical
  let f : Fin m → Bool → ℝ := fun j b => (if b then q j else 1-q j) *
    coinLike pol ω j (1/2+(if b then d j else -d j))
  let g : Bool → ℝ := fun b => obsProb (1/2+(if b then d i else -d i)) o
  have hs (s : Fin m → Bool) :
      stepProb pol (fun j => 1/2+(if s j then d j else -d j)) (fullHist ω) o = g (s i) := by
    cases o with
    | none => simp [stepProb, hi, g, obsProb]
    | some b => cases b <;> simp [stepProb, hi, g, obsProb]
  unfold transcriptLaw
  simp_rw [pathProb_snoc, hs, pathProb_factor]
  calc
    _ = pathValidity pol ω * ∑ s : Fin m → Bool, (∏ j, f j (s j))*g (s i) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro s hs
      dsimp [f]
      rw [Finset.prod_mul_distrib]
      ring
    _ = _ := by
      rw [sum_prod_coordinate]
      simp only [f, g, Fintype.sum_bool, Bool.false_eq_true, ↓reduceIte, ← sub_eq_add_neg]
      dsimp [otherMass, coinMix]
      ring

theorem transcriptLaw_stop {m n : ℕ} (pol : List Bool → Option (Fin m)) (d q : Fin m → ℝ)
    (ω : Fin n → Option Bool) (hi : pol (fullHist ω) = none) (o : Option Bool) :
    transcriptLaw pol d q (Fin.snoc ω o) = if o=none then transcriptLaw pol d q ω else 0 := by
  unfold transcriptLaw
  simp_rw [pathProb_snoc]
  cases o <;> simp [stepProb, hi]

theorem transcriptLaw_sum_extensions {m n : ℕ} (pol : List Bool → Option (Fin m)) (d q : Fin m → ℝ)
    (ω : Fin n → Option Bool) :
    (∑ o : Option Bool, transcriptLaw pol d q (Fin.snoc ω o)) = transcriptLaw pol d q ω := by
  unfold transcriptLaw
  rw [Finset.sum_comm]
  simp_rw [pathProb_snoc, ← mul_assoc, ← Finset.mul_sum, stepProb_total, mul_one]

theorem transcriptLaw_zero_iff {m n : ℕ} (pol : List Bool → Option (Fin m)) (d q : Fin m → ℝ)
    (hd : ∀ i, 0 ≤ d i ∧ d i ≤ 1/2) (hq : ∀ i, 0 < q i ∧ q i < 1)
    (ω : Fin n → Option Bool) :
    transcriptLaw pol d q ω = 0 ↔
      ∀ s : Fin m → Bool, pathProb pol (fun i => 1/2+(if s i then d i else -d i)) ω = 0 := by
  have hw (s : Fin m → Bool) : 0 < ∏ i, (if s i then q i else 1-q i) := by
    apply Finset.prod_pos
    intro i hi
    split_ifs <;> linarith [(hq i).1, (hq i).2]
  have hp (s : Fin m → Bool) :
      0 ≤ pathProb pol (fun i => 1/2+(if s i then d i else -d i)) ω := by
    apply pathProb_nonneg
    intro i
    split_ifs <;> constructor <;> linarith [(hd i).1, (hd i).2]
  unfold transcriptLaw
  rw [Finset.sum_eq_zero_iff_of_nonneg (fun s _ => mul_nonneg (hw s).le (hp s))]
  simp only [Finset.mem_univ, forall_true_left, mul_eq_zero, (hw _).ne', false_or]


theorem workOf_eq_sum {n : ℕ} (ω : Fin n → Option Bool) :
    workOf ω = ∑ t, (if (ω t).isSome then (1 : ℝ) else 0) := by
  simp [workOf]

theorem workOf_snoc {n : ℕ} (ω : Fin n → Option Bool) (o : Option Bool) :
    workOf (Fin.snoc ω o) = workOf ω + (if o.isSome then 1 else 0) := by
  simp only [workOf_eq_sum]
  rw [Fin.sum_univ_castSucc]
  simp only [Fin.snoc_castSucc, Fin.snoc_last]

theorem transcriptLaw_query_none {m n : ℕ} (pol : List Bool → Option (Fin m)) (d q : Fin m → ℝ)
    (ω : Fin n → Option Bool) (i : Fin m) (hi : pol (fullHist ω) = some i) :
    transcriptLaw pol d q (Fin.snoc ω none) = 0 := by
  simp [transcriptLaw_query pol d q ω i hi, obsProb]

theorem transcriptLaw_some_total {m n : ℕ} (pol : List Bool → Option (Fin m)) (d q : Fin m → ℝ)
    (ω : Fin n → Option Bool) :
    (∑ o : Option Bool, transcriptLaw pol d q (Fin.snoc ω o) * (if o.isSome then 1 else 0)) =
      transcriptLaw pol d q ω * (if (pol (fullHist ω)).isSome then 1 else 0) := by
  have ht := transcriptLaw_sum_extensions pol d q ω
  cases hi : pol (fullHist ω) with
  | none => simp [transcriptLaw_stop pol d q ω hi]
  | some i =>
    simp only [Fintype.sum_option, Fintype.sum_bool, Option.isSome_none, Bool.false_eq_true,
      ↓reduceIte, mul_zero, Option.isSome_some, mul_one, zero_add]
    simpa [Fintype.sum_option, transcriptLaw_query_none pol d q ω i hi] using ht

theorem transcriptLaw_work_step {m n : ℕ} (pol : List Bool → Option (Fin m)) (d q : Fin m → ℝ)
    (ω : Fin n → Option Bool) :
    (∑ o : Option Bool, transcriptLaw pol d q (Fin.snoc ω o) * workOf (Fin.snoc ω o)) =
      transcriptLaw pol d q ω * workOf ω +
        transcriptLaw pol d q ω * (if (pol (fullHist ω)).isSome then 1 else 0) := by
  simp_rw [workOf_snoc, mul_add, Finset.sum_add_distrib]
  rw [← Finset.sum_mul, transcriptLaw_sum_extensions, transcriptLaw_some_total]

theorem transcriptLaw_work_succ {m n : ℕ} (pol : List Bool → Option (Fin m)) (d q : Fin m → ℝ) :
    (∑ ω : Fin (n+1) → Option Bool, transcriptLaw pol d q ω * workOf ω) =
      (∑ ω : Fin n → Option Bool, transcriptLaw pol d q ω * workOf ω) +
        ∑ ω : Fin n → Option Bool, transcriptLaw pol d q ω *
          (if (pol (fullHist ω)).isSome then 1 else 0) := by
  rw [sum_snoc]
  simp_rw [transcriptLaw_work_step]
  rw [Finset.sum_add_distrib]


end ThresholdHC.Proofs
