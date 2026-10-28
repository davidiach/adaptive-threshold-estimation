import ThresholdHC.CriticalEntropy.PopulationTransfer

noncomputable section
namespace ThresholdHC.CriticalEntropy
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
local instance : MeasurableSpace (Option Bool) := ⊤

theorem finitePopulationWeight_gap_congr {D : Type} [MeasurableSpace D] {m n : ℕ}
    (μ : Measure D) [SigmaFinite μ] (pol : List Bool → Option (Fin m))
    (d e : D → ℝ) (hde : d =ᵐ[μ] e) (q : Fin m → D → ℝ) :
    finitePopulationWeight (n := n) μ pol d q = finitePopulationWeight μ pol e q := by
  funext w
  rw [finite_population_factor,finite_population_factor]
  congr 1
  apply Finset.prod_congr rfl
  intro i hi
  apply integral_congr_ae
  filter_upwards [hde] with x hx
  rw [hx]

def criticalClippedGap (d : ℝ) : ℝ := max 0 (min d (1/4))

theorem measurable_criticalClippedGap : Measurable criticalClippedGap := by
  unfold criticalClippedGap
  fun_prop

theorem criticalClippedGap_bounds (d : ℝ) :
    0 ≤ criticalClippedGap d ∧ criticalClippedGap d ≤ 1/2 := by
  constructor
  · exact le_max_left _ _
  · apply max_le (by norm_num)
    exact (min_le_right _ _).trans (by norm_num)

theorem criticalClippedGap_ae : criticalClippedGap =ᵐ[criticalGapLaw] id := by
  have hsupport : ∀ᵐ d ∂criticalGapLaw, d ∈ Ioc (0 : ℝ) (1/4) :=
    ae_iff.mpr criticalGapLaw_supported
  filter_upwards [hsupport] with d hd
  simp only [criticalClippedGap,min_eq_left hd.2,max_eq_right hd.1.le,id_eq]

/-- One common critical pair controls every fixed finite family and deterministic
finite horizon in the actual adaptive population experiment. The cost is the
expected number of observed flips under the common midpoint population. -/
theorem critical_common_finite_population_pair : ∃ C : ℝ, 0 < C ∧
    ∀ (ρ : unitInterval), 0 < (ρ : ℝ) → (ρ : ℝ) ≤ 1/4 →
    ∀ δ : ℝ, 0 ≤ δ → δ ≤ (ρ : ℝ)/96 →
    ∃ q r : ℝ → unitInterval, CappedPrior criticalGapLaw (ρ : ℝ) q ∧
      CappedPrior criticalGapLaw (ρ : ℝ) r ∧
      δ ≤ (∫ d, (r d : ℝ) ∂criticalGapLaw)-(∫ d, (q d : ℝ) ∂criticalGapLaw) ∧
      ∀ (m n : ℕ) (pol : List Bool → Option (Fin m)),
        (1-realFiniteAffinity
          (finitePopulationWeight (n := n) criticalGapLaw pol id (fun _ d => (q d : ℝ)))
          (finitePopulationWeight criticalGapLaw pol id (fun _ d => (r d : ℝ))))*
          (ρ : ℝ)*criticalLogFactor (ρ : ℝ) ≤
        C*δ^2*(finitePopulationExpectedWork criticalGapLaw
          (fun d => criticalParameter d false) (fun d => criticalParameter d true)
          (midpointPrior q r) pol n).toReal := by
  classical
  obtain ⟨C,hC,hcommon⟩ := critical_common_capped_pair
  refine ⟨2*C,mul_pos (by norm_num) hC,?_⟩
  intro ρ hρ hρ' δ hδ hδρ
  obtain ⟨q,r,hq,hr,hsep,hpair⟩ := hcommon ρ hρ hρ' δ hδ hδρ
  refine ⟨q,r,hq,hr,hsep,?_⟩
  intro m n pol
  have hp (b : Bool) : ∀ᵐ d ∂criticalGapLaw,
      (criticalParameter d b : ℝ) = 1/2+(if b then criticalClippedGap d else -criticalClippedGap d) := by
    have hsupport : ∀ᵐ d ∂criticalGapLaw, d ∈ Ioc (0 : ℝ) (1/4) :=
      ae_iff.mpr criticalGapLaw_supported
    filter_upwards [hsupport,criticalClippedGap_ae] with d hd hc
    rw [criticalParameter_coe_of_mem d hd,hc]
    rfl
  have hp₀ : ∀ᵐ d ∂criticalGapLaw,
      (criticalParameter d false : ℝ) = 1/2-criticalClippedGap d := by
    simpa only [Bool.false_eq_true,ite_false,sub_eq_add_neg] using hp false
  have hp₁ : ∀ᵐ d ∂criticalGapLaw,
      (criticalParameter d true : ℝ) = 1/2+criticalClippedGap d := by
    simpa only [ite_true] using hp true
  have h := finite_population_transfer criticalGapLaw
    (fun d => criticalParameter d false) (fun d => criticalParameter d true) q r
    (measurable_criticalParameter false) (measurable_criticalParameter true)
    hq.1 hr.1 hq.2.1 hr.2.1 criticalClippedGap measurable_criticalClippedGap
    criticalClippedGap_bounds hp₀ hp₁ pol ((ρ : ℝ)*criticalLogFactor (ρ : ℝ)) (C*δ^2)
    (mul_nonneg hρ.le (criticalLogFactor_pos (ρ : ℝ) hρ ρ.property.2).le)
    (mul_nonneg hC.le (sq_nonneg δ)) (n := n)
  have hbound : let ν := Measure.pi (fun _ : Fin m => parameterTapeLaw
      (populationParameterLaw criticalGapLaw (fun d => criticalParameter d false)
        (fun d => criticalParameter d true) (midpointPrior q r)))
      ∀ i : Fin m, (1-(hellingerAffinity
        (cappedTranscriptLaw criticalGapLaw ν (fun d => criticalParameter d false)
          (fun d => criticalParameter d true) q (localSimulationProcedure i n pol) n)
        (cappedTranscriptLaw criticalGapLaw ν (fun d => criticalParameter d false)
          (fun d => criticalParameter d true) r (localSimulationProcedure i n pol) n)).toReal)*
          ((ρ : ℝ)*criticalLogFactor (ρ : ℝ)) ≤
        C*δ^2*(populationExpectedWork criticalGapLaw ν (fun d => criticalParameter d false)
          (fun d => criticalParameter d true) (fun _ => 0) (localSimulationProcedure i n pol)).toReal := by
    let : IsProbabilityMeasure (populationParameterLaw criticalGapLaw
        (fun d => criticalParameter d false) (fun d => criticalParameter d true) (midpointPrior q r)) :=
      populationParameterLaw_probability criticalGapLaw _ _ _ (measurable_criticalParameter false)
        (measurable_criticalParameter true) (measurable_midpointPrior q r hq.1 hr.1)
    dsimp only
    intro i
    simpa only [mul_assoc] using hpair _ _ _ (localSimulationProcedure i n pol) n
      (localSimulationProcedure_capped i n pol)
  specialize h hbound
  rw [finitePopulationWeight_gap_congr criticalGapLaw pol criticalClippedGap id
      criticalClippedGap_ae (fun _ d => (q d : ℝ)),
    finitePopulationWeight_gap_congr criticalGapLaw pol criticalClippedGap id
      criticalClippedGap_ae (fun _ d => (r d : ℝ))] at h
  simpa only [mul_assoc] using h

end ThresholdHC.CriticalEntropy
