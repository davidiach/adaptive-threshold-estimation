import ThresholdHC.StoppingProgram.DecisionMixture

/-! Independent decision coordinates factor against any function of the
other coordinates. This applies to arrivals determined by earlier depths. -/

noncomputable section
open scoped BigOperators

namespace ThresholdHC.StoppingProgram
variable {I : Type*} [Fintype I] [DecidableEq I]

def joinDecision (i : I) (b : Bool) (r : {j : I // j ≠ i} → Bool) : I → Bool :=
  (Equiv.funSplitAt i Bool).symm (b,r)

theorem joinDecision_self (i : I) (b : Bool) (r : {j : I // j ≠ i} → Bool) :
    joinDecision i b r i = b := by simp [joinDecision,Equiv.funSplitAt,Equiv.piSplitAt]

theorem joinDecision_other (i : I) (b : Bool) (r : {j : I // j ≠ i} → Bool) (j : {j : I // j ≠ i}) :
    joinDecision i b r j.val = r j := by simp [joinDecision,Equiv.funSplitAt,Equiv.piSplitAt,j.property]

theorem decisionWeight_join (p : I → ℝ) (i : I) (b : Bool) (r : {j : I // j ≠ i} → Bool) :
    decisionWeight p (joinDecision i b r) = decisionFactor (p i) b*decisionWeight (fun j : {j : I // j ≠ i} => p j) r := by
  unfold decisionWeight
  rw [Fintype.prod_eq_mul_prod_subtype_ne _ i]
  simp only [joinDecision_self,joinDecision_other]

theorem decisionWeight_sum_split (p : I → ℝ) (i : I) (g : (I → Bool) → ℝ) :
    (∑ b : I → Bool, decisionWeight p b*g b) =
      ∑ r : {j : I // j ≠ i} → Bool, decisionWeight (fun j : {j : I // j ≠ i} => p j) r*
        ((1-p i)*g (joinDecision i false r)+p i*g (joinDecision i true r)) := by
  have he := (Equiv.funSplitAt i Bool).symm.sum_comp (fun b => decisionWeight p b*g b)
  rw [← he,Fintype.sum_prod_type,Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r _
  change (∑ b : Bool, decisionWeight p (joinDecision i b r)*g (joinDecision i b r)) = _
  simp only [decisionWeight_join,Fintype.sum_bool,decisionFactor,ite_true,Bool.false_eq_true,ite_false]
  ring

theorem joinDecision_update (i : I) (b : Bool) (r : {j : I // j ≠ i} → Bool) :
    Function.update (joinDecision i false r) i b = joinDecision i b r := by
  funext j
  by_cases hj : j = i
  · subst j
    simp only [Function.update_self,joinDecision_self]
  · simp [Function.update_of_ne hj,joinDecision,Equiv.funSplitAt,Equiv.piSplitAt,hj]

theorem independent_decision_factor (p : I → ℝ) (i : I) (g : (I → Bool) → ℝ)
    (hg : ∀ b t, g (Function.update b i t) = g b) (a : Bool → ℝ) :
    (∑ b : I → Bool, decisionWeight p b*(g b*a (b i))) =
      ((1-p i)*a false+p i*a true)*(∑ b : I → Bool, decisionWeight p b*g b) := by
  have hg' (r : {j : I // j ≠ i} → Bool) : g (joinDecision i true r) = g (joinDecision i false r) := by
    rw [← joinDecision_update]
    exact hg _ _
  rw [decisionWeight_sum_split p i,decisionWeight_sum_split p i,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r _
  simp only [joinDecision_self,hg']
  ring

end ThresholdHC.StoppingProgram
