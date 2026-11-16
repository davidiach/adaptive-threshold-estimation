import ThresholdHC.RobustContinuation.Clipping
import ThresholdHC.HardBudget.RareModel

/-! A base estimator selected from the reference law alone. The large zero
atom case uses the constant fallback; no continuation-risk oracle is assumed. -/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace ThresholdHC.RobustContinuation
open ThresholdHC.Tier3 ThresholdHC.Tier6 ThresholdHC.RareAboveTwo
open ThresholdHC.ArbitraryLawAdaptation ThresholdHC.KnownLawPlanner
open ThresholdHC.HardBudget

def ValidReference (α : Measure ℝ) (ρ b : ℝ) : Prop :=
  IsProbabilityMeasure α ∧ α (Set.Icc 0 (1/2))ᶜ = 0 ∧ 0 < ρ ∧ ρ ≤ 1/4 ∧ 0 < b

def referenceRadius (α : Measure ℝ) (ρ b : ℝ) : ℝ :=
  plannedCoefficient 28000 * (zeroSelection α ρ b).toReal

theorem plannedCoefficient_ge_one : 1 ≤ plannedCoefficient 28000 := by
  unfold plannedCoefficient
  linarith [le_max_left (4096 : ℝ) (8 * Real.sqrt 2 * 28000)]

theorem referenceRadius_nonneg (α : Measure ℝ) (ρ b : ℝ) :
    0 ≤ referenceRadius α ρ b :=
  mul_nonneg (le_trans zero_le_one plannedCoefficient_ge_one) ENNReal.toReal_nonneg

theorem ofReal_referenceRadius (α : Measure ℝ) (ρ b : ℝ) :
    ENNReal.ofReal (referenceRadius α ρ b) =
      ENNReal.ofReal (plannedCoefficient 28000) * zeroSelection α ρ b := by
  have hfin : zeroSelection α ρ b ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top (min_le_left _ _)
  rw [referenceRadius, ENNReal.ofReal_mul (le_trans zero_le_one plannedCoefficient_ge_one),
    ENNReal.ofReal_toReal hfin]

theorem reference_base_exists (α : Measure ℝ) (ρ b : ℝ) :
    ∃ (R : Type) (_ : MeasurableSpace R) (A : AdaptiveEstimator R),
      ValidReference α ρ b →
      (∀ z, 0 ≤ A.output z ∧ A.output z ≤ ρ) ∧
      ∀ (μ : Measure Gap) [IsProbabilityMeasure μ],
        (∀ x, cdf (μ.map Subtype.val) x ≤ cdf α x) →
        RareBudget μ A ρ b ∧ rareRisk μ A ρ ≤ ENNReal.ofReal (referenceRadius α ρ b) := by
  classical
  by_cases hv : ValidReference α ρ b
  · obtain ⟨hprob, hsupp, hρ, hρ4, hb⟩ := hv
    let := hprob
    by_cases hz : zeroMass α < ρ
    · obtain ⟨hη, hdec⟩ := zeroAtomLaw_decomposition α hsupp (by linarith)
      let := hη
      obtain ⟨R, mR, A, hrange, hA⟩ := clipped_cdf_planner_rate (positiveLaw α)
        (show 0 ≤ zeroMass α from measureReal_nonneg) hz hρ4 hb
      refine ⟨R, mR, A, fun _ => ⟨hrange, ?_⟩⟩
      intro μ hμ hdom
      rw [hdec] at hA
      simpa only [ofReal_referenceRadius] using hA μ hdom
    · have hk : zeroSelection α ρ b = ENNReal.ofReal ρ := by
        apply le_antisymm (show zeroSelection α ρ b ≤ ENNReal.ofReal ρ from min_le_left _ _)
        have hmass : ENNReal.ofReal ρ ≤ α {0} := by
          rw [← ofReal_measureReal]
          exact ENNReal.ofReal_le_ofReal (le_of_not_gt hz)
        simpa only [min_eq_left hmass] using min_zeroMass_le_zeroSelection α hρ hb
      refine ⟨Unit, inferInstance, constantEstimator (ρ/2), fun _ => ⟨?_, ?_⟩⟩
      · intro z; change 0 ≤ ρ/2 ∧ ρ/2 ≤ ρ; constructor <;> linarith
      · intro μ hμ _
        refine ⟨constant_rare_budget μ ρ b (ρ/2), (half_rarity_risk μ ρ hρ.le).trans ?_⟩
        apply ENNReal.ofReal_le_ofReal
        rw [referenceRadius, hk, ENNReal.toReal_ofReal hρ.le]
        nlinarith [plannedCoefficient_ge_one]
  · exact ⟨Unit, inferInstance, constantEstimator (ρ/2), fun h => (hv h).elim⟩

def ReferenceSeed (α : Measure ℝ) (ρ b : ℝ) : Type :=
  (reference_base_exists α ρ b).choose

instance referenceSeedMeasurableSpace (α : Measure ℝ) (ρ b : ℝ) :
    MeasurableSpace (ReferenceSeed α ρ b) :=
  (reference_base_exists α ρ b).choose_spec.choose

def referenceBase (α : Measure ℝ) (ρ b : ℝ) : AdaptiveEstimator (ReferenceSeed α ρ b) :=
  (reference_base_exists α ρ b).choose_spec.choose_spec.choose

theorem referenceBase_valid (α : Measure ℝ) (ρ b : ℝ) (hv : ValidReference α ρ b) :
    (∀ z, 0 ≤ (referenceBase α ρ b).output z ∧ (referenceBase α ρ b).output z ≤ ρ) ∧
    ∀ (μ : Measure Gap) [IsProbabilityMeasure μ],
      (∀ x, cdf (μ.map Subtype.val) x ≤ cdf α x) →
      RareBudget μ (referenceBase α ρ b) ρ b ∧
        rareRisk μ (referenceBase α ρ b) ρ ≤ ENNReal.ofReal (referenceRadius α ρ b) :=
  (reference_base_exists α ρ b).choose_spec.choose_spec.choose_spec hv

end ThresholdHC.RobustContinuation
