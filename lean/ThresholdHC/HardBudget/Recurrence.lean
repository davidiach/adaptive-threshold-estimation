import ThresholdHC.HardBudget.StageMoments
import Mathlib.Probability.Independence.Integration

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace ThresholdHC.HardBudget

def retained (M : ℝ) (v : ℕ → Outcome) : ℕ → ℝ
  | 0 => M/2
  | j+1 => if (v j).1 then retained M v j else (v j).2

theorem measurable_retained (M : ℝ) (j : ℕ) : Measurable (fun v => retained M v j) := by
  induction j with
  | zero => exact measurable_const
  | succ j ih =>
    have hm : Measurable (fun v : ℕ → Outcome => v j) := measurable_pi_apply j
    exact Measurable.ite (measurableSet_eq_fun hm.fst measurable_const) ih hm.snd

theorem retained_congr (M : ℝ) {v w : ℕ → Outcome} (j : ℕ) (h : ∀ i < j, v i = w i) :
    retained M v j = retained M w j := by
  induction j with
  | zero => rfl
  | succ j ih =>
    have hj := h j (by omega)
    have hp := ih (fun i hi => h i (by omega))
    simp only [retained,hj,hp]

private theorem timeout_indep_previous {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (X : ℕ → Ω → Outcome) (hm : ∀ i, Measurable (X i)) (hi : iIndepFun X P)
    (M θ : ℝ) (j : ℕ) :
    IndepFun (fun u => timedOut (X j u)) (fun u => loss θ (retained M (fun i => X i u) j)) P := by
  let S := Finset.range j
  let T : Finset ℕ := {j}
  have hd : Disjoint T S := by simp [T,S]
  have h := hi.indepFun_finset T S hd hm
  let fill (y : S → Outcome) (i : ℕ) : Outcome := if hi : i ∈ S then y ⟨i,hi⟩ else (true,0)
  have hf : Measurable fill := by
    apply Measurable.of_eval; intro i
    by_cases h : i ∈ S
    · simpa only [fill,dite_eq_left h] using (measurable_pi_apply (⟨i,h⟩ : S))
    · simpa only [fill,dite_eq_right h] using (measurable_const : Measurable (fun _ : S → Outcome => (true,(0:ℝ))))
  let t : T := ⟨j,by simp [T]⟩
  let g (y : S → Outcome) := loss θ (retained M (fill y) j)
  have hg : Measurable g := (measurable_loss θ).comp ((measurable_retained M j).comp hf)
  have hh := h.comp (measurable_timedOut.comp (measurable_pi_apply t)) hg
  have hsame (u : Ω) : g (fun i : S => X i u) = loss θ (retained M (fun i => X i u) j) := by
    apply congrArg (loss θ); apply retained_congr; intro i hi
    simp [fill,S,hi]
  change IndepFun (fun u => timedOut (X j u)) (fun u => g (fun i : S => X i u)) P at hh
  simpa only [hsame] using hh

/-- No assumption couples a stage's success flag and error. Only earlier
stages are independent of the present timeout. -/
theorem expected_loss_step {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (X : ℕ → Ω → Outcome) (hm : ∀ i, Measurable (X i)) (hi : iIndepFun X P)
    (M θ : ℝ) (j : ℕ) :
    (∫⁻ u, loss θ (retained M (fun i => X i u) (j+1)) ∂P) ≤
      (∫⁻ u, loss θ (X j u).2 ∂P) +
      (∫⁻ u, timedOut (X j u) ∂P)*(∫⁻ u, loss θ (retained M (fun i => X i u) j) ∂P) := by
  let V (u : Ω) := loss θ (retained M (fun i => X i u) j)
  have hV : Measurable V := (measurable_loss θ).comp
    ((measurable_retained M j).comp (Measurable.of_eval hm))
  have hcur : Measurable (fun u => loss θ (X j u).2) := (measurable_loss θ).comp (hm j).snd
  have ht := measurable_timedOut.comp (hm j)
  have he := lintegral_mul_eq_lintegral_mul_lintegral_of_indepFun ht hV
    (timeout_indep_previous P X hm hi M θ j)
  simp only [Function.comp_apply,Pi.mul_apply] at he
  change _ ≤ _ + _*(∫⁻ u, V u ∂P)
  rw [← he,← lintegral_add_left hcur]
  apply lintegral_mono
  intro u
  cases hx : (X j u).1 <;> simp [retained,timedOut,hx,V]

end ThresholdHC.HardBudget
