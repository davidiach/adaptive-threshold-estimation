import ThresholdHC.StoppingProgram.ClosedProgram
import ThresholdHC.StoppingProgram.SublevelBounds

/-! Compactness of the original feasible objective sublevel after removing
universally null output coordinates. -/

noncomputable section
open MeasureTheory Set
open scoped BigOperators

namespace ThresholdHC.StoppingProgram
open ThresholdHC.Tier6 (Gap SignLaw)

def prunedSublevel (N : ℕ) (μ : Measure Gap) (ρ B M : ℝ) (qref : SignLaw) : Set (ProgramPoint N) :=
  {x | Feasible μ ρ B (pointCertificate x) ∧ NullPruned μ qref (pointCertificate x) ∧ pointObjective x ≤ M}

theorem nullPruned_points_closed (N : ℕ) (μ : Measure Gap) (qref : SignLaw) :
    IsClosed {x : ProgramPoint N | NullPruned μ qref (pointCertificate x)} := by
  simp only [NullPruned,pointCertificate,pointFlow,ofPred_forall,ofPred_and]
  apply isClosed_iInter
  intro s
  apply isClosed_iInter
  intro hs
  exact (isClosed_eq (by fun_prop) continuous_const).inter (isClosed_eq (by fun_prop) continuous_const)

theorem prunedSublevel_closed (N : ℕ) (μ : Measure Gap) [IsProbabilityMeasure μ]
    {ρ : ℝ} (hρ : 0 ≤ ρ) (B M : ℝ) (qref : SignLaw) :
    IsClosed (prunedSublevel N μ ρ B M qref) := by
  unfold prunedSublevel
  simp only [ofPred_and]
  exact (feasible_points_closed μ hρ B).inter ((nullPruned_points_closed N μ qref).inter
    (isClosed_le (pointObjective_continuous N) continuous_const))

theorem prunedSublevel_box (N : ℕ) (μ : Measure Gap) [IsProbabilityMeasure μ]
    {ρ B M : ℝ} (hρ : 0 < ρ) (hρhalf : ρ ≤ 1/2) (hB : 0 ≤ B) (hM : 0 ≤ M) :
    ∃ L : ProgramPoint N,
      prunedSublevel N μ ρ B M (constantPrior ρ ⟨hρ.le,by linarith⟩) ⊆ Icc (-L) L := by
  let q := constantPrior ρ ⟨hρ.le,by linarith⟩
  let T : CountState N → ℝ := momentCoordinateBound μ q M
  let Z : CountState N → ℝ := outputCoordinateBound μ q B M
  let O := offsetCoordinateBound N μ q B M
  let L : ProgramPoint N := (![O,M+1,M],![fun _ => B,fun _ => B,Z,T])
  refine ⟨L,?_⟩
  intro x hx
  obtain ⟨hf,hp,hobj⟩ := hx
  obtain ⟨hb,hv,hs,ho⟩ := feasible_sublevel_bounds μ hρ hρhalf hB hM (pointCertificate x) hf hobj hp
  have hb0 : 0 ≤ x.1 1 := hf.bias_nonneg
  have hv0 : 0 ≤ x.1 2 := hf.variance_nonneg
  change x.1 1 ≤ M+1 at hb
  change x.1 2 ≤ M at hv
  change |x.1 0| ≤ O at ho
  have ht0 (s : CountState N) : 0 ≤ T s := div_nonneg hM (countCoefficient_nonneg μ q s)
  have ha0 (s : CountState N) : 0 ≤ x.2 0 s := hf.cone.stop_nonneg s
  have hc0 (s : CountState N) : 0 ≤ x.2 1 s := hf.cone.continue_nonneg s
  have hm0 (s : CountState N) : 0 ≤ x.2 3 s := hf.cone.moment_nonneg s
  have hstate (s : CountState N) : x.2 0 s ≤ B ∧ x.2 1 s ≤ B ∧ x.2 3 s ≤ T s ∧ |x.2 2 s| ≤ Z s := hs s
  constructor
  · constructor
    · intro i
      fin_cases i <;> dsimp [L]
      · exact (abs_le.mp ho).1
      · linarith
      · linarith
    · intro i s
      fin_cases i <;> dsimp [L]
      · linarith [ha0 s]
      · linarith [hc0 s]
      · exact (abs_le.mp (hstate s).2.2.2).1
      · linarith [ht0 s,hm0 s]
  · constructor
    · intro i
      fin_cases i <;> dsimp [L]
      · exact (abs_le.mp ho).2
      · exact hb
      · exact hv
    · intro i s
      fin_cases i <;> dsimp [L]
      · exact (hstate s).1
      · exact (hstate s).2.1
      · exact (abs_le.mp (hstate s).2.2.2).2
      · exact (hstate s).2.2.1

theorem prunedSublevel_compact (N : ℕ) (μ : Measure Gap) [IsProbabilityMeasure μ]
    {ρ B M : ℝ} (hρ : 0 < ρ) (hρhalf : ρ ≤ 1/2) (hB : 0 ≤ B) (hM : 0 ≤ M) :
    IsCompact (prunedSublevel N μ ρ B M (constantPrior ρ ⟨hρ.le,by linarith⟩)) := by
  obtain ⟨L,hL⟩ := prunedSublevel_box N μ hρ hρhalf hB hM
  exact isCompact_Icc.of_isClosed_subset (prunedSublevel_closed N μ hρ.le B M _) hL

end ThresholdHC.StoppingProgram
