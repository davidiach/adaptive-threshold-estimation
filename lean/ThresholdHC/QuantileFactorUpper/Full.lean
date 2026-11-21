import ThresholdHC.QuantileFactorUpper.Specification
import ThresholdHC.QuantileFactorUpper.Cover
import ThresholdHC.QuantileFactorUpper.Certificate
import ThresholdHC.PaperStatements.Quantile
import ThresholdHC.QuantileOptimality.Full

/-! The upper end of the decimal bracket and `thm:sharp-quantile-factor`.

The kernel-checked cover places the partition series below one on `[1,31/20]`
at `k = 1462554551280/10^12`. The peak is attained, so it lies below one; the
peak is strictly decreasing and equals one at the root, so the root lies below
`1.462554551280`. The lower end is `PaperStatements.root_lower`, and the
characterization of the least factor is `universalFactor_iff` and
`finiteUniversalFactor_iff`. -/
noncomputable section
open Real
namespace ThresholdHC.QuantileFactorUpper
open ThresholdHC.OptimalQuantile ThresholdHC.QuantileOptimality

theorem partitionSeries_lt_one {u : ℝ} (hu : u ∈ Set.Icc (1 : ℝ) (31/20)) :
    partitionSeries (1462554551280/1000000000000) u < 1 :=
  cover_of_certify certify_full hu

theorem peak_upper : PeakUpperStatement := by
  obtain ⟨u, hu, he, _⟩ := scalarPeak_attained factor_ge_sqrt
  unfold PeakUpperStatement
  rw [he]
  exact partitionSeries_lt_one hu

theorem root_upper : RootUpperStatement := by
  unfold RootUpperStatement
  by_contra h
  have hle : (1462554551280/1000000000000 : ℝ) ≤ scalarRoot := not_lt.mp h
  have hm := scalarPeak_strictAntiOn.antitoneOn
    (show (1462554551280/1000000000000 : ℝ) ∈ Set.Ici (sqrt 2) from factor_ge_sqrt)
    (show scalarRoot ∈ Set.Ici (sqrt 2) from scalarRoot_spec.1.1) hle
  rw [scalarRoot_spec.2] at hm
  have hp := peak_upper
  unfold PeakUpperStatement at hp
  linarith

theorem root_bracket : RootBracketStatement :=
  ⟨ThresholdHC.PaperStatements.root_lower, root_upper⟩

theorem sharp_quantile_factor : SharpQuantileFactorStatement := by
  refine ⟨scalarRoot, scalarRoot_spec.1, ?_, ?_,
    fun k => ⟨universalFactor_iff k, finiteUniversalFactor_iff k⟩, root_bracket.1, root_bracket.2⟩
  · obtain ⟨u, hu, he, hmax⟩ := scalarPeak_attained scalarRoot_spec.1.1
    rw [scalarRoot_spec.2] at he
    refine ⟨⟨u, hu, he.symm⟩, ?_⟩
    rintro y ⟨v, hv, rfl⟩
    rw [he]
    exact hmax v hv
  · intro k hk hg
    have h1 : scalarPeak k = 1 := hg.csSup_eq
    exact exists_unique_scalarRoot.unique ⟨hk, h1⟩ scalarRoot_spec

end ThresholdHC.QuantileFactorUpper
