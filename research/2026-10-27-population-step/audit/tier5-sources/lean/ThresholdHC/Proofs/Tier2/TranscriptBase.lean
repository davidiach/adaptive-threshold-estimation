import ThresholdHC.Statements2

noncomputable section
namespace ThresholdHC.Proofs
open ThresholdHC Real MeasureTheory

def fullHist {n : ℕ} (ω : Fin n → Option Bool) : List Bool :=
  (List.ofFn ω).filterMap id

def stepProb {m : ℕ} (pol : List Bool → Option (Fin m)) (p : Fin m → ℝ)
    (h : List Bool) (o : Option Bool) : ℝ :=
  match pol h, o with
  | none, none => 1
  | some i, some true => p i
  | some i, some false => 1 - p i
  | _, _ => 0

theorem histBefore_snoc_castSucc {n : ℕ} (ω : Fin n → Option Bool) (o : Option Bool)
    (t : Fin n) : histBefore (Fin.snoc ω o) t.castSucc = histBefore ω t := by
  unfold histBefore
  congr 2
  funext j
  change @Fin.snoc n (fun _ => Option Bool) ω o (Fin.castSucc (Fin.castLE t.isLt.le j)) = _
  exact Fin.snoc_castSucc _ _ _

theorem histBefore_snoc_last {n : ℕ} (ω : Fin n → Option Bool) (o : Option Bool) :
    histBefore (Fin.snoc ω o) (Fin.last n) = fullHist ω := by
  unfold histBefore fullHist
  congr 2
  funext j
  change @Fin.snoc n (fun _ => Option Bool) ω o j.castSucc = ω j
  exact Fin.snoc_castSucc _ _ _

theorem pathProb_snoc {m n : ℕ} (pol : List Bool → Option (Fin m)) (p : Fin m → ℝ)
    (ω : Fin n → Option Bool) (o : Option Bool) :
    pathProb pol p (Fin.snoc ω o) = pathProb pol p ω * stepProb pol p (fullHist ω) o := by
  unfold pathProb
  rw [Fin.prod_univ_castSucc]
  simp only [histBefore_snoc_castSucc, histBefore_snoc_last, Fin.snoc_castSucc,
    Fin.snoc_last, stepProb]
  rfl

theorem stepProb_nonneg {m : ℕ} (pol : List Bool → Option (Fin m)) (p : Fin m → ℝ)
    (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1) (h : List Bool) (o : Option Bool) :
    0 ≤ stepProb pol p h o := by
  unfold stepProb
  cases he : pol h with
  | none => cases o <;> norm_num
  | some i => cases o with
    | none => norm_num
    | some b => cases b <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> linarith [(hp i).1,(hp i).2]

theorem stepProb_total {m : ℕ} (pol : List Bool → Option (Fin m)) (p : Fin m → ℝ)
    (h : List Bool) : ∑ o : Option Bool, stepProb pol p h o = 1 := by
  cases he : pol h <;> simp [stepProb, he, Fintype.sum_option] <;> ring

theorem pathProb_nonneg {m n : ℕ} (pol : List Bool → Option (Fin m)) (p : Fin m → ℝ)
    (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1) (ω : Fin n → Option Bool) :
    0 ≤ pathProb pol p ω := by
  apply Finset.prod_nonneg
  intro t ht
  exact stepProb_nonneg pol p hp (histBefore ω t) (ω t)

theorem sum_snoc {n : ℕ} (f : (Fin (n+1) → Option Bool) → ℝ) :
    (∑ ω, f ω) = ∑ ω : Fin n → Option Bool, ∑ o : Option Bool, f (Fin.snoc ω o) := by
  rw [← (Fin.snocEquiv (fun _ : Fin (n+1) => Option Bool)).sum_comp]
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  rfl

theorem pathProb_total {m : ℕ} (pol : List Bool → Option (Fin m)) (p : Fin m → ℝ)
    (n : ℕ) : ∑ ω : Fin n → Option Bool, pathProb pol p ω = 1 := by
  induction n with
  | zero => simp [pathProb]
  | succ n ih =>
    rw [sum_snoc]
    simp_rw [pathProb_snoc, ← Finset.mul_sum, stepProb_total, mul_one]
    exact ih

theorem signPrior_total {m : ℕ} (q : Fin m → ℝ) :
    ∑ s : Fin m → Bool, (∏ i, if s i then q i else 1-q i) = 1 := by
  have h := Fintype.prod_sum (fun i : Fin m => fun b : Bool => if b then q i else 1-q i)
  rw [← h]
  simp

theorem transcript_law_total : ThresholdHC.Targets.transcript_law_total := by
  intro m n pol d q hd hq
  have hp (s : Fin m → Bool) (i : Fin m) :
      0 ≤ (1/2 : ℝ) + (if s i then d i else -d i) ∧
        (1/2 : ℝ) + (if s i then d i else -d i) ≤ 1 := by
    split_ifs <;> constructor <;> linarith [(hd i).1, (hd i).2]
  constructor
  · intro ω
    unfold transcriptLaw
    apply Finset.sum_nonneg
    intro s hs
    apply mul_nonneg
    · apply Finset.prod_nonneg
      intro i hi
      split_ifs <;> linarith [(hq i).1, (hq i).2]
    · exact pathProb_nonneg pol _ (hp s) ω
  · unfold transcriptLaw
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum, pathProb_total, mul_one]
    exact signPrior_total q

end ThresholdHC.Proofs


