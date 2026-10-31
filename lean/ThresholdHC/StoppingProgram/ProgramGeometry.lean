import ThresholdHC.StoppingProgram.FlowOperations

/-! A finite-dimensional ambient space for the unchanged certificate cone. -/

noncomputable section
open Set

namespace ThresholdHC.StoppingProgram

abbrev ProgramPoint (N : ℕ) := (Fin 3 → ℝ) × (Fin 4 → CountState N → ℝ)

def pointFlow {N : ℕ} (x : ProgramPoint N) : Flow N := ⟨x.2 0,x.2 1,x.2 2,x.2 3⟩

def pointCertificate {N : ℕ} (x : ProgramPoint N) : Certificate N :=
  ⟨pointFlow x,x.1 0,x.1 1,x.1 2⟩

def certificatePoint {N : ℕ} (C : Certificate N) : ProgramPoint N :=
  (![C.offset,C.bias,C.variance],![C.flow.stopWeight,C.flow.continueWeight,C.flow.outputWeight,C.flow.momentWeight])

theorem pointCertificate_certificatePoint {N : ℕ} (C : Certificate N) :
    pointCertificate (certificatePoint C) = C := by
  cases C with
  | mk f c b v => cases f; rfl

def programDomain (N : ℕ) : Set (ProgramPoint N) :=
  {x | FlowCone (pointFlow x) ∧ 0 ≤ x.1 1 ∧ 0 ≤ x.1 2}

theorem pointFlow_combo {N : ℕ} (x y : ProgramPoint N) (a b : ℝ) :
    pointFlow (a • x+b • y) = addFlow (scaleFlow a (pointFlow x)) (scaleFlow b (pointFlow y)) := rfl

theorem programDomain_convex (N : ℕ) : Convex ℝ (programDomain N) := by
  intro x hx y hy a b ha hb hab
  refine ⟨?_,?_,?_⟩
  · rw [pointFlow_combo]
    exact (hx.1.scale ha).add (hy.1.scale hb)
  · exact add_nonneg (mul_nonneg ha hx.2.1) (mul_nonneg hb hy.2.1)
  · exact add_nonneg (mul_nonneg ha hx.2.2) (mul_nonneg hb hy.2.2)

theorem certificatePoint_mem_domain {N : ℕ} (C : Certificate N)
    (hc : FlowCone C.flow) (hb : 0 ≤ C.bias) (hv : 0 ≤ C.variance) :
    certificatePoint C ∈ programDomain N := ⟨hc,hb,hv⟩

def pointObjective {N : ℕ} (x : ProgramPoint N) : ℝ := (x.1 1)^2+x.1 2

theorem pointObjective_continuous (N : ℕ) : Continuous (@pointObjective N) := by
  unfold pointObjective
  fun_prop

theorem pointObjective_convex (N : ℕ) : ConvexOn ℝ (programDomain N) (@pointObjective N) := by
  refine ⟨programDomain_convex N,?_⟩
  intro x hx y hy a b ha hb hab
  change (a*x.1 1+b*y.1 1)^2+(a*x.1 2+b*y.1 2) ≤
    a*((x.1 1)^2+x.1 2)+b*((y.1 1)^2+y.1 2)
  have hh : 0 ≤ a*b*(x.1 1-y.1 1)^2 := mul_nonneg (mul_nonneg ha hb) (sq_nonneg _)
  have hsum : b = 1-a := by linarith
  rw [hsum] at hh ⊢
  nlinarith

end ThresholdHC.StoppingProgram
