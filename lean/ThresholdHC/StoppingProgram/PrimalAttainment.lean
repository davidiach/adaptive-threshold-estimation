import ThresholdHC.StoppingProgram.PrimalCompactness

/-! The robust stopping program attains its minimum. Null-state pruning
allows compactness without an artificial bound on observable outputs. -/

noncomputable section
open MeasureTheory Set
open scoped ENNReal

namespace ThresholdHC.StoppingProgram
open ThresholdHC.Tier6 (Gap)

theorem programSquared_attained (N : ℕ) (μ : Measure Gap) [IsProbabilityMeasure μ]
    {ρ B : ℝ} (hρ : 0 < ρ) (hρhalf : ρ ≤ 1/2) (hB : 0 ≤ B) :
    ∃ C : Certificate N, Feasible μ ρ B C ∧ certificateSquared C = programSquared μ ρ B N := by
  let qref := constantPrior ρ ⟨hρ.le,by linarith⟩
  let M := (ρ/2)^2
  let S := prunedSublevel N μ ρ B M qref
  have hc : IsCompact S := prunedSublevel_compact N μ hρ hρhalf hB (sq_nonneg _)
  have hne : S.Nonempty := by
    refine ⟨certificatePoint (constantCertificate N ρ),?_⟩
    change Feasible μ ρ B (pointCertificate (certificatePoint (constantCertificate N ρ))) ∧
      NullPruned μ qref (pointCertificate (certificatePoint (constantCertificate N ρ))) ∧ _
    rw [pointCertificate_certificatePoint]
    refine ⟨constantCertificate_feasible μ hρ.le hB N,?_,?_⟩
    · intro s hs
      exact ⟨rfl,rfl⟩
    · simp [pointObjective,certificatePoint,constantCertificate,M]
  obtain ⟨x0,hx0,hmin⟩ := hc.exists_isMinOn hne (pointObjective_continuous N).continuousOn
  refine ⟨pointCertificate x0,hx0.1,le_antisymm ?_ ?_⟩
  · apply le_sInf
    rintro z ⟨C,hC,rfl⟩
    apply ENNReal.ofReal_le_ofReal
    change pointObjective x0 ≤ C.bias^2+C.variance
    by_cases hbound : C.bias^2+C.variance ≤ M
    · let Cp := pruneCertificate μ qref C
      have hmem : certificatePoint Cp ∈ S := by
        change Feasible μ ρ B (pointCertificate (certificatePoint Cp)) ∧
          NullPruned μ qref (pointCertificate (certificatePoint Cp)) ∧ _
        rw [pointCertificate_certificatePoint]
        exact ⟨pruneCertificate_feasible μ hρ hρhalf C hC,pruneCertificate_pruned μ qref C,hbound⟩
      have hh := hmin hmem
      change pointObjective x0 ≤ pointObjective (certificatePoint Cp) at hh
      exact hh
    · exact hx0.2.2.trans (le_of_lt (lt_of_not_ge hbound))
  · exact sInf_le ⟨pointCertificate x0,hx0.1,rfl⟩

end ThresholdHC.StoppingProgram
