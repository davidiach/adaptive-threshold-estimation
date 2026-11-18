import ThresholdHC.LargeBudgetRMS.PilotExperiment
import ThresholdHC.LargeBudgetRMS.RevisitPolynomial

/-! Integer likelihood recursion for adaptive binary trees. A reused pilot
observation is removed from the remaining pilot likelihood and replaced by
the joint likelihood of the two flips. This keeps every coefficient integral. -/
namespace ThresholdHC.SharpRMS.Pilot
open LargeBudget Revisit Revisit.IntPoly

def up : Coeffs := [3,4]
def down : Coeffs := [7,-4]
def hh : Coeffs := [9,40]
def mix : Coeffs := [21]
def tt : Coeffs := [49,-40]

def treePoly (A : Choices) (E : ℕ → ℕ → ℕ) (j : ℕ) : ℕ → ℕ → ℕ → ℕ → ℕ → Coeffs
  | 0, _, i, h, t => mul (mul (power up h) (power down t)) (power [E j i,-100000] 2)
  | n+1, k, i, h, t =>
    let children := fun (a b : Coeffs) (H T : ℕ) =>
      add (mul a (treePoly A E j n (k+1) (2*i) H T))
          (mul b (treePoly A E j n (k+1) (2*i+1) H T))
    match choice A j k i with
    | none => children down up h t
    | some true => children mix hh (h-1) t
    | some false => children tt mix h (t-1)

noncomputable def loss (E : ℕ → ℕ → ℕ) (p : ℝ) (j i : ℕ) := ((E j i : ℝ)/100000-p)^2

private theorem values (p : ℝ) (hp : p∈Set.Icc 0 1) :
    value up p=10*headProb p ∧ value down p=10*(1-headProb p) ∧
    value mix p=100*headProb p*(1-nextHead p (some true)) ∧
    value hh p=100*headProb p*nextHead p (some true) ∧
    value tt p=100*(1-headProb p)*(1-nextHead p (some false)) ∧
    value mix p=100*(1-headProb p)*nextHead p (some false) := by
  have pos : headProb p≠0 := by unfold headProb; linarith [hp.1]
  have lt : 1-headProb p≠0 := by unfold headProb; linarith [hp.2]
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  all_goals norm_num [up,down,mix,hh,tt,value,nextHead]
  all_goals field_simp [pos,lt]
  all_goals unfold headProb
  all_goals ring

theorem tree_value (A : Choices) (E : ℕ → ℕ → ℕ) (p : ℝ) (hp : p∈Set.Icc 0 1)
    (j n k i h t : ℕ) (heads : j≤h+k) (tails : 18-j≤t+k) :
    value (treePoly A E j n k i h t) p =
      10^n*(10*headProb p)^h*(10*(1-headProb p))^t*10^10*
        tailAverage A (loss E p) p j n k i := by
  obtain ⟨U,D,MH,HH,TT,MT⟩ := values p hp
  induction n generalizing k i h t with
  | zero =>
    simp only [treePoly,value_mul,value_power,U,D,tailAverage,loss,pow_zero,one_mul]
    simp [value]; ring
  | succ n ih =>
    cases e : choice A j k i with
    | none =>
      simp only [treePoly,tailAverage,e,value_add,value_mul,D,U,nextHead]
      rw [ih _ _ _ _ (by omega) (by omega),ih _ _ _ _ (by omega) (by omega),pow_succ]
      ring
    | some b =>
      have ha := choice_available A e
      cases b with
      | false =>
        simp only [available,Bool.false_eq_true,ite_false] at ha
        obtain ⟨t,rfl⟩ : ∃ v, t=v+1 := ⟨t-1,by omega⟩
        simp only [treePoly,tailAverage,e,value_add,value_mul,TT,MT,Nat.add_sub_cancel]
        rw [ih _ _ _ _ (by omega) (by omega),ih _ _ _ _ (by omega) (by omega),pow_succ,pow_succ (10*(1-headProb p)) t]
        ring
      | true =>
        simp only [available,ite_true] at ha
        obtain ⟨h,rfl⟩ : ∃ v, h=v+1 := ⟨h-1,by omega⟩
        simp only [treePoly,tailAverage,e,value_add,value_mul,MH,HH,Nat.add_sub_cancel]
        rw [ih _ _ _ _ (by omega) (by omega),ih _ _ _ _ (by omega) (by omega),pow_succ,pow_succ (10*headProb p) h]
        ring

def row (A : Choices) (E : ℕ → ℕ → ℕ) (j : ℕ) :=
  scale ((18:ℕ).choose j) (treePoly A E j 7 0 1 j (18-j))

def riskPoly (A : Choices) (E : ℕ → ℕ → ℕ) := sumTo (row A E) 19

theorem risk_value (A : Choices) (E : ℕ → ℕ → ℕ) (p : ℝ) (hp : p∈Set.Icc 0 1) :
    value (riskPoly A E) p=(10:ℝ)^35*binomialAverage (headProb p) (finish A (loss E p) p) 18 0 := by
  rw [riskPoly,value_sumTo,binomial_sum,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  have le : j≤18 := by have := Finset.mem_range.mp hj; omega
  simp only [row,value_scale,Int.cast_natCast,tree_value A E p hp j 7 0 1 j (18-j) (by omega) (by omega),finish,zero_add]
  rw [mul_pow,mul_pow]
  have z : (10:ℝ)^j*10^(18-j)=10^18 := by rw [←pow_add,show j+(18-j)=18 by omega]
  linear_combination ((18:ℕ).choose j:ℝ)*10^17*(headProb p)^j*(1-headProb p)^(18-j)*
    tailAverage A (loss E p) p j 7 0 1*z

end ThresholdHC.SharpRMS.Pilot
