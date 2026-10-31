import ThresholdHC.StoppingProgram.RobustConstraints
import ThresholdHC.StoppingProgram.Slater

/-! The actual stopping program satisfies strict inequality feasibility.
Geometric separation supplies attained finite multipliers at its infimum. -/

noncomputable section
open MeasureTheory Set
open scoped BigOperators ENNReal

namespace ThresholdHC.StoppingProgram
open ThresholdHC.Tier6 (Gap signMean)

theorem program_point_lower {N : ℕ} (μ : Measure Gap) [IsProbabilityMeasure μ]
    {ρ : ℝ} (hρ : 0 ≤ ρ) (B : ℝ) (x : ProgramPoint N) (hx : x ∈ programDomain N)
    (hineq : ∀ j, robustResidual μ ρ B j x ≤ 0) :
    (programSquared μ ρ B N).toReal ≤ pointObjective x := by
  have hf := (point_feasible_iff μ hρ B x).mpr ⟨hx,hineq⟩
  have hh : programSquared μ ρ B N ≤ ENNReal.ofReal (pointObjective x) :=
    sInf_le ⟨pointCertificate x,hf,rfl⟩
  have ht := ENNReal.toReal_mono ENNReal.ofReal_ne_top hh
  rw [ENNReal.toReal_ofReal (show 0 ≤ pointObjective x from add_nonneg (sq_nonneg _) hx.2.2)] at ht
  exact ht

theorem program_strict_inequalities (N : ℕ) (μ : Measure Gap) [IsProbabilityMeasure μ]
    {ρ B : ℝ} (hρ : 0 ≤ ρ) (hB : 0 < B) :
    ∃ x ∈ programDomain N, ∀ j, robustResidual μ ρ B j x < 0 := by
  let C : Certificate N := ⟨zeroFlow N,0,ρ+1,1⟩
  let x := certificatePoint C
  refine ⟨x,certificatePoint_mem_domain C (zeroFlow_cone N) (by dsimp [C]; linarith) (by norm_num [C]),?_⟩
  intro j
  obtain ⟨u,hu,he⟩ := compactMaximum_attained (priorMomentImage N μ ρ)
    (priorMomentImage_nonempty N μ hρ) (priorMomentImage_compact_convex N μ ρ).1
    (fun u => pointResidual B j u x) (pointResidual_continuous_prior B j x).continuousOn
  change compactMaximum _ _ < 0
  rw [he]
  obtain ⟨q,hq,rfl⟩ := hu
  have ht := (ThresholdHC.Tier6.signMean_bounds μ q).1
  change signMean μ q.val ≤ ρ at hq
  fin_cases j <;> simp [pointResidual,coordinateMean,priorCoordinates,x,certificatePoint,C,zeroFlow] <;> linarith

theorem program_multipliers (N : ℕ) (μ : Measure Gap) [IsProbabilityMeasure μ]
    {ρ B : ℝ} (hρ : 0 ≤ ρ) (hB : 0 < B) :
    ∃ weights : Fin 4 → ℝ, (∀ j, 0 ≤ weights j) ∧
      ∀ x ∈ programDomain N, (programSquared μ ρ B N).toReal ≤
        pointObjective x+∑ j, weights j*robustResidual μ ρ B j x := by
  let g : Option (Fin 4) → ProgramPoint N → ℝ
    | none => pointObjective
    | some j => robustResidual μ ρ B j
  apply finite_slater_multipliers (programDomain N) (programDomain_convex N) g
  · intro i
    cases i with
    | none => exact pointObjective_convex N
    | some j => exact robustResidual_convex μ hρ B j
  · exact program_point_lower μ hρ B
  · exact program_strict_inequalities N μ hρ hB

end ThresholdHC.StoppingProgram
