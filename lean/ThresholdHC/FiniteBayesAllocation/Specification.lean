import ThresholdHC.FiniteLawCertificates.Atomic
import ThresholdHC.HardBudget.Words

/-! Target statements for the horizon-eight finite-prior Bayes allocation
example of the population-step research package.

Source: `research/2026-10-27-population-step/RESEARCH_NOTE.tex`, section
Exact finite-horizon evidence (the table with the two-scales and
three-scales rows), the summary in
`research/2026-10-27-population-step/FINAL_REPORT.md` (section Computation,
formal coverage, and practical limits), the fixed diagnostic of
`research/2026-10-27-population-step/CONTRACT.md` (section Fixed finite-horizon
diagnostic specification), the locked laws and priors of
`research/2026-10-27-population-step/FINITE_LOCK.json`, the exact values of
`research/2026-10-27-population-step/FINITE_RESULTS.json`, the program
`research/2026-10-27-population-step/finite_bayes.py`, and the horizon-eight
adaptive policies `two_scales_policy.json` and `three_scales_policy.json` of the
same package.

The model is the original population experiment of `ThresholdHC.Tier6`
(private seed, iid hidden magnitudes from the gap law, iid hidden signs with
`P(positive) = q(d)`, every flip charged). The gap law is atomic:

* two scales: masses `1/8, 7/8` at gaps `1/32, 1/4`;
* three scales: masses `1/16, 3/16, 3/4` at gaps `1/32, 1/8, 1/2`.

The prior is uniform over the locked sign laws of `FINITE_LOCK.json` (six for
two scales, seven for three scales), each given by its values at the atoms and
set to `0` off the atoms (a null set). The target is `signMean μ q = ∑ m_j q_j`.
`bayesRisk` is the uniform prior average of the mean squared error.

* The adaptive witness has the policy `stopAt 8 (tableLabel T)`, where the
  ordered label table `T` transcribes the stored horizon-eight dynamic-program
  policy: a fresh action takes the next unused label, and a revisit of a sorted
  coin takes the first label with those head and tail counts. Index `2^t + b`
  holds the label of flip `t + 1` after the ordered word with binary value `b`
  (`true` is a head); index `0` is unused.
* The comparison classes are the fixed designs of `finite_bayes.py`: fresh
  coins `0, 1, ..., 7` in order, or eight flips of coin `0`, each with any
  private seed and any measurable output.

What is proved is that an explicit capped eight-flip adaptive policy beats
every fresh-only and every single-coin design by at least `1.5917%` (two
scales) and `5.0307%` (three scales) in squared Bayes error. The stored
adaptive value is the dynamic-program minimum; here it is only the risk of the
explicit witness, so adaptive optimality, horizons one to seven, and fresh or
single designs with other labels, randomized schedules or early stopping are
not covered. All constants are roundings at `10^-15` of the exact fractions
(upper values rounded up, lower values rounded down). -/

noncomputable section
namespace ThresholdHC.FiniteBayesAllocation
open MeasureTheory
open scoped ENNReal
open ThresholdHC.Tier3 ThresholdHC.Tier6 ThresholdHC.HardBudget ThresholdHC.FiniteLawCertificates

def gap32 : Gap := ⟨1/32, by norm_num⟩
def gap8 : Gap := ⟨1/8, by norm_num⟩
def gap4 : Gap := ⟨1/4, by norm_num⟩
def gap2 : Gap := ⟨1/2, by norm_num⟩

/-- Two scales: masses `1/8, 7/8` at gaps `1/32, 1/4`. -/
def twoScalesLaw : Measure Gap := atomicMeasure ![gap32, gap4] ![1/8, 7/8]

/-- Three scales: masses `1/16, 3/16, 3/4` at gaps `1/32, 1/8, 1/2`. -/
def threeScalesLaw : Measure Gap := atomicMeasure ![gap32, gap8, gap2] ![1/16, 3/16, 3/4]

instance twoScalesLaw_probability : IsProbabilityMeasure twoScalesLaw :=
  atomicMeasure_probability _ _ (by intro i; fin_cases i <;> norm_num)
    (by simp [Fin.sum_univ_succ]; norm_num)

instance threeScalesLaw_probability : IsProbabilityMeasure threeScalesLaw :=
  atomicMeasure_probability _ _ (by intro i; fin_cases i <;> norm_num)
    (by simp [Fin.sum_univ_succ]; norm_num)

/-- Sign law with value `v j` (clipped to `[0,1]`) at the atom `d j` for
injective `d` (for repeated atoms, the clipped sum), and `0` off the atoms. -/
def atomSign {J : ℕ} (d : Fin J → Gap) (v : Fin J → ℚ) : SignLaw :=
  ⟨fun x => max 0 (min 1 (∑ j, ({d j} : Set Gap).indicator (fun _ => (v j : ℝ)) x)),
    measurable_const.max (measurable_const.min (Finset.measurable_sum _ fun _ _ =>
      measurable_const.indicator (measurableSet_singleton _))),
    fun _ => ⟨le_max_left _ _, max_le zero_le_one (min_le_left _ _)⟩⟩

/-- The six locked sign laws of two scales, in `FINITE_LOCK.json` order. -/
def twoScalesSign (k : Fin 6) : SignLaw :=
  atomSign ![gap32, gap4]
    (![![0, 0], ![1/2, 0], ![1, 0], ![0, 1/14], ![0, 1/7], ![1/8, 1/8]] k)

/-- The seven locked sign laws of three scales, in `FINITE_LOCK.json` order. -/
def threeScalesSign (k : Fin 7) : SignLaw :=
  atomSign ![gap32, gap8, gap2]
    (![![0, 0, 0], ![1, 0, 0], ![0, 1/3, 0], ![0, 2/3, 0], ![0, 0, 1/12], ![0, 0, 1/6],
      ![1/8, 1/8, 1/8]] k)

/-- Uniform-prior Bayes mean squared error for the target `∫ q dμ` in the
original experiment. -/
def bayesRisk {R : Type} [MeasurableSpace R] {K : ℕ} (μ : Measure Gap) [IsProbabilityMeasure μ]
    (q : Fin K → SignLaw) (A : AdaptiveEstimator R) : ℝ≥0∞ :=
  (∑ k, squaredRisk (experimentLaw μ A (q k)) (populationOutput A) (signMean μ (q k).val)) / K

/-- The fresh design of `finite_bayes.py`: coin `t` at step `t`, exactly eight
flips; any private seed and any measurable output. -/
def FreshDesign {R : Type} [MeasurableSpace R] (A : AdaptiveEstimator R) : Prop :=
  ∀ r, A.policy r = stopAt 8 (fun xs => xs.length)

/-- The single-coin design of `finite_bayes.py`: eight flips of coin `0`. -/
def SingleDesign {R : Type} [MeasurableSpace R] (A : AdaptiveEstimator R) : Prop :=
  ∀ r, A.policy r = stopAt 8 (fun _ => 0)

/-- Ordered-word reader of a label table: index `2^|xs|` plus the binary value
of `xs` (`true` is the digit one). -/
def tableLabel (T : List ℕ) (xs : List Bool) : ℕ :=
  T.getD (xs.foldl (fun a b => 2 * a + b.toNat) 1) 0

/-- Ordered label table of the stored two-scales horizon-eight policy. -/
def twoScalesTable : List ℕ :=
  [0, 0, 1, 0, 2, 1, 1, 0, 3, 2, 2, 1, 2, 1, 0, 0, 4, 3, 3, 2, 3, 2, 1, 1, 3, 2, 2, 1, 1, 0, 0, 0,
   5, 4, 4, 3, 4, 3, 2, 2, 4, 3, 3, 2, 2, 1, 1, 1, 4, 3, 3, 2, 3, 2, 1, 1, 2, 1, 0, 0, 0, 0, 0, 0,
   6, 5, 5, 4, 5, 4, 3, 3, 5, 4, 4, 3, 3, 2, 2, 2, 5, 4, 4, 3, 4, 3, 2, 2, 3, 2, 1, 1, 1, 1, 1, 1,
   5, 4, 4, 3, 4, 3, 2, 2, 4, 3, 3, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0,
   7, 6, 6, 5, 6, 5, 4, 4, 6, 5, 5, 4, 4, 3, 3, 3, 6, 5, 5, 4, 5, 4, 3, 3, 4, 3, 2, 2, 2, 2, 2, 2,
   6, 5, 5, 4, 5, 4, 3, 3, 5, 4, 4, 3, 3, 2, 2, 2, 4, 3, 3, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1,
   6, 5, 5, 4, 5, 4, 3, 3, 5, 4, 4, 3, 3, 2, 2, 2, 5, 4, 4, 3, 4, 3, 2, 2, 3, 2, 1, 1, 1, 1, 1, 1,
   4, 3, 3, 2, 3, 2, 1, 1, 2, 1, 0, 0, 0, 0, 0, 0, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

/-- Ordered label table of the stored three-scales horizon-eight policy. -/
def threeScalesTable : List ℕ :=
  [0, 0, 1, 0, 2, 1, 1, 0, 3, 2, 2, 1, 2, 1, 1, 0, 4, 3, 3, 2, 3, 2, 2, 1, 3, 2, 2, 1, 2, 1, 1, 0,
   5, 4, 4, 3, 4, 3, 3, 2, 4, 3, 3, 2, 3, 2, 2, 1, 4, 3, 3, 2, 3, 2, 2, 1, 3, 2, 2, 1, 2, 1, 1, 0,
   6, 5, 5, 4, 5, 4, 4, 3, 5, 4, 4, 3, 4, 3, 3, 2, 5, 4, 4, 3, 4, 3, 3, 2, 4, 3, 3, 2, 3, 2, 2, 1,
   5, 4, 4, 3, 4, 3, 3, 2, 4, 3, 3, 2, 3, 2, 2, 1, 4, 3, 3, 2, 3, 2, 2, 1, 3, 2, 2, 1, 2, 1, 1, 0,
   7, 6, 6, 5, 6, 5, 5, 4, 6, 5, 5, 4, 5, 4, 4, 3, 6, 5, 5, 4, 5, 4, 4, 3, 5, 4, 4, 3, 4, 3, 3, 2,
   6, 5, 5, 4, 5, 4, 4, 3, 5, 4, 4, 3, 4, 3, 3, 2, 5, 4, 4, 3, 4, 3, 3, 2, 4, 3, 3, 2, 3, 2, 1, 1,
   6, 5, 5, 4, 5, 4, 4, 3, 5, 4, 4, 3, 4, 3, 3, 2, 5, 4, 4, 3, 4, 3, 3, 2, 4, 3, 3, 2, 3, 2, 2, 1,
   5, 4, 4, 3, 4, 3, 3, 2, 4, 3, 3, 2, 3, 2, 2, 1, 4, 3, 3, 2, 3, 2, 2, 1, 3, 2, 2, 1, 0, 1, 0, 0]

/-- Some estimator with the two-scales table policy (pathwise cap eight) has
Bayes squared error at most `2111783001239/10^15`. -/
def TwoScalesUpperStatement : Prop :=
  ∃ A : AdaptiveEstimator Unit, (∀ r, A.policy r = stopAt 8 (tableLabel twoScalesTable)) ∧
    PathwiseCap A 8 ∧ bayesRisk twoScalesLaw twoScalesSign A ≤ ENNReal.ofReal (2111783001239 / 10^15)

/-- Some estimator with the three-scales table policy (pathwise cap eight) has
Bayes squared error at most `1706729084112/10^15`. -/
def ThreeScalesUpperStatement : Prop :=
  ∃ A : AdaptiveEstimator Unit, (∀ r, A.policy r = stopAt 8 (tableLabel threeScalesTable)) ∧
    PathwiseCap A 8 ∧
    bayesRisk threeScalesLaw threeScalesSign A ≤ ENNReal.ofReal (1706729084112 / 10^15)

/-- Every estimator with the fixed fresh design (coins `0, ..., 7` in order) or
the fixed single-coin design (coin `0`), exactly eight flips, any private seed
and any measurable output, has at least the rounded-down restricted Bayes
errors. -/
def RestrictedLowerStatement : Prop :=
  ∀ {R : Type} [MeasurableSpace R] (A : AdaptiveEstimator R),
    (FreshDesign A →
      ENNReal.ofReal (2149143352671 / 10^15) ≤ bayesRisk twoScalesLaw twoScalesSign A ∧
      ENNReal.ofReal (1797138065871 / 10^15) ≤ bayesRisk threeScalesLaw threeScalesSign A) ∧
    (SingleDesign A →
      ENNReal.ofReal (2145940859276 / 10^15) ≤ bayesRisk twoScalesLaw twoScalesSign A ∧
      ENNReal.ofReal (1868722055075 / 10^15) ≤ bayesRisk threeScalesLaw threeScalesSign A)

/-- The two-scales comparison classes are inhabited, and some member of each has
risk within `10^-15` of the lower constant (the proof uses the posterior-mean
member). -/
def TwoScalesRestrictedTightStatement : Prop :=
  (∃ A : AdaptiveEstimator Unit, FreshDesign A ∧
     bayesRisk twoScalesLaw twoScalesSign A ≤ ENNReal.ofReal (2149143352672 / 10^15)) ∧
  (∃ A : AdaptiveEstimator Unit, SingleDesign A ∧
     bayesRisk twoScalesLaw twoScalesSign A ≤ ENNReal.ofReal (2145940859277 / 10^15))

/-- The three-scales comparison classes are inhabited, and some member of each
has risk within `10^-15` of the lower constant (the proof uses the
posterior-mean member). -/
def ThreeScalesRestrictedTightStatement : Prop :=
  (∃ A : AdaptiveEstimator Unit, FreshDesign A ∧
     bayesRisk threeScalesLaw threeScalesSign A ≤ ENNReal.ofReal (1797138065872 / 10^15)) ∧
  (∃ A : AdaptiveEstimator Unit, SingleDesign A ∧
     bayesRisk threeScalesLaw threeScalesSign A ≤ ENNReal.ofReal (1868722055076 / 10^15))

/-- Headline (table-free): some estimator with a deterministic eight-flip
adaptive policy improves by at least `1.5917%` in two-scales squared Bayes
error on every estimator with the fixed fresh or the fixed single-coin design
(exactly eight flips, any private seed, any measurable output). -/
def TwoScalesGainStatement : Prop :=
  ∃ W : AdaptiveEstimator Unit, (∃ p : List Bool → ℕ, ∀ r, W.policy r = stopAt 8 p) ∧
    ∀ {R : Type} [MeasurableSpace R] (A : AdaptiveEstimator R), FreshDesign A ∨ SingleDesign A →
      bayesRisk twoScalesLaw twoScalesSign W ≤
        ENNReal.ofReal (1 - 15917 / 1000000) * bayesRisk twoScalesLaw twoScalesSign A

/-- Headline (table-free): some estimator with a deterministic eight-flip
adaptive policy improves by at least `5.0307%` in three-scales squared Bayes
error on every estimator with the fixed fresh or the fixed single-coin design
(exactly eight flips, any private seed, any measurable output). -/
def ThreeScalesGainStatement : Prop :=
  ∃ W : AdaptiveEstimator Unit, (∃ p : List Bool → ℕ, ∀ r, W.policy r = stopAt 8 p) ∧
    ∀ {R : Type} [MeasurableSpace R] (A : AdaptiveEstimator R), FreshDesign A ∨ SingleDesign A →
      bayesRisk threeScalesLaw threeScalesSign W ≤
        ENNReal.ofReal (1 - 50307 / 1000000) * bayesRisk threeScalesLaw threeScalesSign A

/-- The two-scales gain with the witness identified as the table policy. -/
def TwoScalesPinnedGainStatement : Prop :=
  ∃ W : AdaptiveEstimator Unit, (∀ r, W.policy r = stopAt 8 (tableLabel twoScalesTable)) ∧
    PathwiseCap W 8 ∧
    ∀ {R : Type} [MeasurableSpace R] (A : AdaptiveEstimator R), FreshDesign A ∨ SingleDesign A →
      bayesRisk twoScalesLaw twoScalesSign W ≤
        ENNReal.ofReal (1 - 15917 / 1000000) * bayesRisk twoScalesLaw twoScalesSign A

/-- The three-scales gain with the witness identified as the table policy. -/
def ThreeScalesPinnedGainStatement : Prop :=
  ∃ W : AdaptiveEstimator Unit, (∀ r, W.policy r = stopAt 8 (tableLabel threeScalesTable)) ∧
    PathwiseCap W 8 ∧
    ∀ {R : Type} [MeasurableSpace R] (A : AdaptiveEstimator R), FreshDesign A ∨ SingleDesign A →
      bayesRisk threeScalesLaw threeScalesSign W ≤
        ENNReal.ofReal (1 - 50307 / 1000000) * bayesRisk threeScalesLaw threeScalesSign A

end ThresholdHC.FiniteBayesAllocation
