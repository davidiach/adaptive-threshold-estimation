import ThresholdHC.StoppingProgram.ProgramMultipliers
import ThresholdHC.StoppingProgram.MinimaxSelection

/-! Attained Lagrange multipliers represented by four actual globally rare
priors. Compact minimax selects one quadruple uniformly over the flow cone. -/

noncomputable section
open MeasureTheory Set
open scoped BigOperators ENNReal

namespace ThresholdHC.StoppingProgram
open ThresholdHC.Tier6 (Gap SignLaw signMean)

abbrev PriorTuple (N : ℕ) := Fin 4 → Option (CountState N) → ℝ

def priorTupleSet (N : ℕ) (μ : Measure Gap) (ρ : ℝ) : Set (PriorTuple N) :=
  {U | ∀ j, U j ∈ priorMomentImage N μ ρ}

def tupleLagrangian {N : ℕ} (B : ℝ) (weights : Fin 4 → ℝ) (U : PriorTuple N) (x : ProgramPoint N) : ℝ :=
  pointObjective x+∑ j, weights j*pointResidual B j (U j) x

theorem tupleLagrangian_continuous_prior {N : ℕ} (B : ℝ) (weights : Fin 4 → ℝ) (x : ProgramPoint N) :
    Continuous (fun U => tupleLagrangian B weights U x) := by
  exact continuous_const.add (continuous_finsetSum _ (fun j _ => continuous_const.mul
    ((pointResidual_continuous_prior B j x).comp (continuous_apply j))))

theorem tupleLagrangian_continuous_point {N : ℕ} (B : ℝ) (weights : Fin 4 → ℝ) (U : PriorTuple N) :
    Continuous (tupleLagrangian B weights U) := by
  exact (pointObjective_continuous N).add (continuous_finsetSum _ (fun j _ => continuous_const.mul
    (pointResidual_continuous_point B j (U j))))

theorem tupleLagrangian_convex {N : ℕ} (B : ℝ) (weights : Fin 4 → ℝ) (U : PriorTuple N) :
    ConvexOn ℝ (programDomain N) (tupleLagrangian B weights U) := by
  refine ⟨programDomain_convex N,?_⟩
  intro x hx y hy a b ha hb hab
  have ho := (pointObjective_convex N).2 hx hy ha hb hab
  have he : (∑ j, weights j*pointResidual B j (U j) (a • x+b • y)) =
      a*(∑ j, weights j*pointResidual B j (U j) x)+b*(∑ j, weights j*pointResidual B j (U j) y) := by
    simp only [pointResidual_combo_point B _ _ x y a b hab,Finset.mul_sum,← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    ring
  change pointObjective (a • x+b • y)+(∑ j, weights j*pointResidual B j (U j) (a • x+b • y)) ≤
    a*(pointObjective x+∑ j, weights j*pointResidual B j (U j) x)+
    b*(pointObjective y+∑ j, weights j*pointResidual B j (U j) y)
  rw [he]
  change pointObjective (a • x+b • y) ≤ a*pointObjective x+b*pointObjective y at ho
  nlinarith

theorem tupleLagrangian_concave {N : ℕ} (B : ℝ) (weights : Fin 4 → ℝ)
    (X : Set (PriorTuple N)) (hX : Convex ℝ X) (x : ProgramPoint N) :
    ConcaveOn ℝ X (fun U => tupleLagrangian B weights U x) := by
  refine ⟨hX,?_⟩
  intro U hU V hV a b ha hb hab
  have hterm (j : Fin 4) : pointResidual B j ((a • U+b • V) j) x =
      a*pointResidual B j (U j) x+b*pointResidual B j (V j) x :=
    pointResidual_combo_prior B j (U j) (V j) x a b hab
  have he : (∑ j, weights j*pointResidual B j ((a • U+b • V) j) x) =
      a*(∑ j, weights j*pointResidual B j (U j) x)+b*(∑ j, weights j*pointResidual B j (V j) x) := by
    simp only [hterm,Finset.mul_sum,← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    ring
  change a*(pointObjective x+∑ j, weights j*pointResidual B j (U j) x)+
    b*(pointObjective x+∑ j, weights j*pointResidual B j (V j) x) ≤
    pointObjective x+(∑ j, weights j*pointResidual B j ((a • U+b • V) j) x)
  rw [he]
  nlinarith [congrArg (fun r : ℝ => r*pointObjective x) hab]

theorem tuple_multipliers (N : ℕ) (μ : Measure Gap) [IsProbabilityMeasure μ]
    {ρ B : ℝ} (hρ : 0 ≤ ρ) (hB : 0 < B) :
    ∃ (weights : Fin 4 → ℝ) (U : PriorTuple N),
      (∀ j, 0 ≤ weights j) ∧ U ∈ priorTupleSet N μ ρ ∧
      ∀ x ∈ programDomain N, (programSquared μ ρ B N).toReal ≤ tupleLagrangian B weights U x := by
  obtain ⟨weights,hw,hmult⟩ := program_multipliers N μ hρ hB
  let X := priorTupleSet N μ ρ
  have hc : IsCompact X := isCompact_pi_infinite (fun _ => (priorMomentImage_compact_convex N μ ρ).1)
  have hv : Convex ℝ X := by
    intro U hU V hV a b ha hb hab j
    exact (priorMomentImage_compact_convex N μ ρ).2 (hU j) (hV j) ha hb hab
  have hne : X.Nonempty := by
    obtain ⟨u,hu⟩ := priorMomentImage_nonempty N μ hρ
    exact ⟨fun _ => u,fun _ => hu⟩
  have hpoint : ∀ x ∈ programDomain N, ∃ U ∈ X,
      (programSquared μ ρ B N).toReal ≤ tupleLagrangian B weights U x := by
    intro x hx
    have hm (j : Fin 4) := compactMaximum_attained (priorMomentImage N μ ρ)
      (priorMomentImage_nonempty N μ hρ) (priorMomentImage_compact_convex N μ ρ).1
      (fun u => pointResidual B j u x) (pointResidual_continuous_prior B j x).continuousOn
    choose U hU he using hm
    refine ⟨U,hU,(hmult x hx).trans_eq ?_⟩
    unfold tupleLagrangian
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    rw [robustResidual,he j]
  obtain ⟨U,hU,hh⟩ := compact_minimax_selection X (programDomain N) hne hc hv (programDomain_convex N)
    (tupleLagrangian B weights) (tupleLagrangian_continuous_prior B weights)
    (tupleLagrangian_continuous_point B weights)
    (fun x _ => tupleLagrangian_concave B weights X hv x)
    (fun U _ => tupleLagrangian_convex B weights U) _ hpoint
  exact ⟨weights,U,hw,hU,hh⟩

theorem four_prior_multipliers (N : ℕ) (μ : Measure Gap) [IsProbabilityMeasure μ]
    {ρ B : ℝ} (hρ : 0 ≤ ρ) (hB : 0 < B) :
    ∃ (weights : Fin 4 → ℝ) (Q : FourPriors), (∀ j, 0 ≤ weights j) ∧ Admissible μ ρ Q ∧
      ∀ C : Certificate N, FlowCone C.flow → 0 ≤ C.bias → 0 ≤ C.variance →
        (programSquared μ ρ B N).toReal ≤ C.bias^2+C.variance+
          weights 0*(C.offset+countMean μ Q.low C.flow.outputWeight-signMean μ Q.low.val-C.bias)+
          weights 1*(signMean μ Q.high.val-C.offset-countMean μ Q.high C.flow.outputWeight-C.bias)+
          weights 2*(countMean μ Q.variance C.flow.momentWeight-C.variance)+
          weights 3*(countMean μ Q.work C.flow.continueWeight-B) := by
  obtain ⟨weights,U,hw,hU,hh⟩ := tuple_multipliers N μ hρ hB
  choose q hq he using hU
  let Q : FourPriors := ⟨q 0,q 1,q 2,q 3⟩
  refine ⟨weights,Q,hw,⟨hq 0,hq 1,hq 2,hq 3⟩,?_⟩
  intro C hc hb hv
  have h := hh (certificatePoint C) (certificatePoint_mem_domain C hc hb hv)
  simp only [tupleLagrangian,he] at h
  simpa [pointObjective,certificatePoint,pointResidual,coordinateMean,priorCoordinates,
    countMean,Fin.sum_univ_succ,Q,add_assoc] using h

end ThresholdHC.StoppingProgram
