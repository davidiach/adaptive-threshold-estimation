import ThresholdHC.ContinuousObserved.DeterministicSigns

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace ThresholdHC.ContinuousObserved
open ThresholdHC ThresholdHC.Tier3 ThresholdHC.CriticalEntropy

theorem countablePath_nonneg {n : ℕ} (pol : List Bool → Option ℕ)
    (p : ℕ → unitInterval) (w : Prefix n) : 0 ≤ countablePath pol (fun i => (p i : ℝ)) w := by
  apply Finset.prod_nonneg
  intro t _
  unfold countableStep
  cases pol (histBefore w t) with
  | none => cases w t <;> norm_num
  | some i =>
    cases w t with
    | none => norm_num
    | some b =>
      cases b <;> simp only
      · exact sub_nonneg.mpr (p i).property.2
      · exact (p i).property.1

theorem countablePath_initial_stop {n : ℕ} (pol : List Bool → Option ℕ) (p : ℕ → ℝ)
    (hp : pol [] = none) (w : Prefix n) :
    countablePath pol p w = if w = (fun _ => none) then 1 else 0 := by
  classical
  induction n with
  | zero => simp [countablePath,Subsingleton.elim w (fun _ => none)]
  | succ n ih =>
    obtain ⟨o,v,rfl⟩ := Fin.exists_cons w
    rw [countablePath_cons]
    cases o with
    | none =>
      have he : (Fin.cons none v = (fun _ => (none : Option Bool))) ↔ v = (fun _ => none) := by
        constructor
        · intro h; funext t; exact congrFun h t.succ
        · intro h; subst v; funext t; exact Fin.cases rfl (fun _ => rfl) t
      simpa only [countableStep,hp,Option.toList_none,List.nil_append,one_mul,he] using ih v
    | some b =>
      have hne : Fin.cons (some b) v ≠ (fun _ => (none : Option Bool)) := by
        intro h
        exact Option.some_ne_none b (congrFun h 0)
      simp [countableStep,hp,hne]

def countableExpectation (pol : List Bool → Option ℕ) (p : ℕ → unitInterval) :
    (n : ℕ) → (Prefix n → ℝ≥0∞) → ℝ≥0∞
  | 0, F => F Fin.elim0
  | n + 1, F => match pol [] with
    | none => F (fun _ => none)
    | some i => ∫⁻ b : Bool, countableExpectation (fun xs => pol (b :: xs)) p n
        (fun w => F (Fin.cons (some b) w)) ∂bernoulliMeasure true false (p i)

theorem countableExpectation_sum (pol : List Bool → Option ℕ) (p : ℕ → unitInterval)
    (n : ℕ) (F : Prefix n → ℝ≥0∞) :
    countableExpectation pol p n F =
      ∑ w, ENNReal.ofReal (countablePath pol (fun i => (p i : ℝ)) w) * F w := by
  induction n generalizing pol with
  | zero =>
    simp [countableExpectation,countablePath]
    exact congrArg F (Subsingleton.elim _ _)
  | succ n ih =>
    cases hp : pol [] with
    | none =>
      simp only [countableExpectation,hp]
      simp_rw [countablePath_initial_stop pol _ hp]
      simp [apply_ite]
    | some i =>
      have hzero (w : Prefix n) : countablePath pol (fun i => (p i : ℝ)) (Fin.cons none w) = 0 := by
        rw [countablePath_cons]
        simp [countableStep,hp]
      have hcons (b : Bool) (w : Prefix n) :
          ENNReal.ofReal (countablePath pol (fun i => (p i : ℝ)) (Fin.cons (some b) w)) =
            (bernoulliMeasure true false (p i)) {b} *
              ENNReal.ofReal (countablePath (fun xs => pol (b :: xs)) (fun i => (p i : ℝ)) w) := by
        rw [countablePath_cons,bernoulli_singleton_ofReal]
        cases b <;> simp only [countableStep,hp,Option.toList_some,List.singleton_append,
          Bool.false_eq_true,ite_false,ite_true]
        · rw [ENNReal.ofReal_mul (sub_nonneg.mpr (p i).property.2)]
        · rw [ENNReal.ofReal_mul (p i).property.1]
      simp only [countableExpectation,hp]
      rw [lintegral_fintype]
      simp_rw [ih]
      rw [sum_cons_word,Fintype.sum_option]
      simp_rw [hzero,ENNReal.ofReal_zero,zero_mul,Finset.sum_const_zero,zero_add,hcons,
        mul_assoc,← Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro b _
      exact mul_comm _ _

end ThresholdHC.ContinuousObserved
