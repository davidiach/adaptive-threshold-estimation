import ThresholdHC.PaperStatements.Critical
import ThresholdHC.PaperStatements.OneFlip
import ThresholdHC.PaperStatements.Observable
import ThresholdHC.PaperStatements.Quantile

/-! Paper and guide claims that had only a written proof, a numerical check or
an existential constant, as Lean theorems: the critical theorem with explicit
constants and the paper's `Ψ` sequence in its model, the sharpness of the
unbiased coefficient `1/16`, the endpoint case of the nonnegativity
proposition, the constant `1/2` for a known point mass, the moment sentence of
the 713 construction, the bound `1.462554551279` for the sharp quantile factor, and
selection stability with the factors `20/31` and `1/c_vec`. -/
noncomputable section
namespace ThresholdHC.PaperStatements
open MeasureTheory ProbabilityTheory ThresholdHC.Tier6 ThresholdHC.UnbiasedConverse

theorem critical_power_law_exact : CriticalPowerLawStatement := critical_power_law

theorem critical_model : CriticalModelStatement := critical_minimax_eq

theorem critical_explicit_constants : CriticalExplicitStatement := critical_explicit

theorem critical_slow_divergence : SlowDivergenceStatement := slow_divergence

theorem critical_psi_divergence : CriticalPsiSequenceStatement := by
  intro n hn
  exact critical_psi_sequence n hn

theorem one_flip : OneFlipStatement := by
  intro d
  obtain ⟨hu, hv, hw, hhalf⟩ := one_flip_bounds d
  refine ⟨oneFlip d, hu, hv, hw, le_antisymm (iSup_le hv) ?_⟩
  rw [← hhalf]
  exact le_iSup (fun q : SignLaw =>
    evariance (populationOutput (oneFlip d)) (experimentLaw (Measure.dirac d) (oneFlip d) q)) halfLaw

theorem unbiased_fixed_gap_equality : FixedGapEqualityStatement := fixed_gap_equality

theorem unbiased_sharp_coefficient : UnbiasedSharpStatement := sharp_coefficient

theorem half_gap_one_flip : HalfGapUnbiasedStatement := half_gap_unbiased

theorem point_mass_half : PointMassUpperStatement := point_mass_upper

theorem observable_second_moment : SecondMomentStatement :=
  ⟨Observable713.observableEstimator, fun μ _ hI => second_moment_bounds μ hI⟩

theorem quantile_root_lower : RootLowerStatement := root_lower

theorem quantile_finite_ratio : FiniteRatioStatement :=
  QuantileOptimality.finite_sharpness _ root_lower

theorem selection_stability_quantile : StabilityQuantileStatement := by
  intro μ μ₀ _ _ T hm r η ρ B hr hρ hrho hB hη hd hb
  exact stability_quantile μ μ₀ T hm hr hρ hrho hB hη hd hb

theorem selection_stability_sharp : StabilitySharpStatement := by
  intro μ μ₀ _ _ T hm r η ρ B hr hρ hrho hB hη hd hb
  exact stability_sharp μ μ₀ T hm hr hρ hrho hB hη hd hb

end ThresholdHC.PaperStatements
