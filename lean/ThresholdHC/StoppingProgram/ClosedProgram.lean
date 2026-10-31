import ThresholdHC.StoppingProgram.RobustConstraints

/-! Closedness of the actual normalized cone and robust feasible set in
the finite-dimensional certificate space. -/

noncomputable section
open MeasureTheory Set

namespace ThresholdHC.StoppingProgram
open ThresholdHC.Tier6 (Gap)

@[fun_prop] theorem arrayAt_continuous (N n k : ℕ) : Continuous (fun u : CountState N → ℝ => arrayAt u n k) := by
  unfold arrayAt
  split_ifs <;> fun_prop

theorem pointFlow_cone_iff {N : ℕ} (x : ProgramPoint N) : FlowCone (pointFlow x) ↔
    (∀ s, 0 ≤ x.2 0 s) ∧ (∀ s, 0 ≤ x.2 1 s) ∧ (∀ s, 0 ≤ x.2 3 s) ∧
    x.2 0 (rootState N) = 0 ∧ x.2 2 (rootState N) = 0 ∧ x.2 3 (rootState N) = 0 ∧
    (∀ s, s.1.val = N → x.2 1 s = 0) ∧
    (∀ s, 0 < s.1.val → x.2 0 s+x.2 1 s =
      ((s.1.val-s.2.val:ℕ):ℝ)/s.1.val*arrayAt (x.2 1) (s.1.val-1) s.2.val+
      (s.2.val:ℝ)/s.1.val*arrayAt (x.2 1) (s.1.val-1) (s.2.val-1)) ∧
    (∀ s, (x.2 2 s)^2 ≤ x.2 0 s*x.2 3 s) := by
  constructor
  · intro h
    exact ⟨h.stop_nonneg,h.continue_nonneg,h.moment_nonneg,h.root_stop,h.root_output,h.root_moment,
      h.terminal,h.recursion,h.perspective⟩
  · rintro ⟨ha,hc,ht,har,hzr,htr,hterm,hrec,hpersp⟩
    exact ⟨ha,hc,ht,har,hzr,htr,hterm,hrec,hpersp⟩

theorem pointFlow_cone_closed (N : ℕ) : IsClosed {x : ProgramPoint N | FlowCone (pointFlow x)} := by
  simp only [pointFlow_cone_iff,ofPred_and,ofPred_forall]
  repeat' first | apply IsClosed.inter | apply isClosed_iInter; intro i
  all_goals first | apply isClosed_le <;> fun_prop | apply isClosed_eq <;> fun_prop

theorem programDomain_closed (N : ℕ) : IsClosed (programDomain N) := by
  unfold programDomain
  simp only [ofPred_and]
  exact (pointFlow_cone_closed N).inter ((isClosed_le continuous_const (by fun_prop)).inter
    (isClosed_le continuous_const (by fun_prop)))

theorem feasible_points_closed {N : ℕ} (μ : Measure Gap) [IsProbabilityMeasure μ]
    {ρ : ℝ} (hρ : 0 ≤ ρ) (B : ℝ) :
    IsClosed {x : ProgramPoint N | Feasible μ ρ B (pointCertificate x)} := by
  simp only [point_feasible_iff μ hρ,robustResidual_nonpos_iff μ hρ,
    ofPred_and,ofPred_forall]
  apply (programDomain_closed N).inter
  apply isClosed_iInter
  intro j
  apply isClosed_iInter
  intro q
  apply isClosed_iInter
  intro hq
  exact isClosed_le (pointResidual_continuous_point B j (priorCoordinates N μ q)) continuous_const

end ThresholdHC.StoppingProgram
