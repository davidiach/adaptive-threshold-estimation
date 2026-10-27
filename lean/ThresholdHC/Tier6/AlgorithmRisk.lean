import ThresholdHC.Tier6.AlgorithmModel
import ThresholdHC.Tier6.HardPair
import ThresholdHC.Tier6.Testing
import ThresholdHC.Tier6.RiskReduction
import ThresholdHC.Tier5.Full

noncomputable section
open MeasureTheory InformationTheory
open scoped ENNReal
namespace ThresholdHC.Tier6
open ThresholdHC.Tier3 ThresholdHC.Tier4 ThresholdHC.Tier5

theorem algorithmLowerBound_of_realization (hreal : PopulationRealizationStatement) :
    AlgorithmLowerBoundStatement := by
  intro R _ μ _ A B hB hbudget
  let h := budgetScale B
  have hh : 0 < h := (budget_hard_pair μ B hB).1
  have hv := hard_pair_validity h hh
  let qp : SignLaw := ⟨hardPlus h, hv.2.1, fun d => (hv.2.2.2 d).2.2.1⟩
  let qm : SignLaw := ⟨hardMinus h, hv.2.2.1, fun d => (hv.2.2.2 d).2.2.2⟩
  let P := experimentLaw μ A qp
  let Q := experimentLaw μ A qm
  let η : PopulationSeed R → ℕ → ℝ := fun u i => hardEta h (u.2 i)
  let a := signMean μ qp.val
  let b := signMean μ qm.val
  have hP := (hreal R μ A qp).2
  have hQ := (hreal R μ A qm).2
  have hηm : MeasurableEnvironment η := by
    intro i
    exact (measurable_hardEta h).comp ((measurable_pi_apply i).comp measurable_snd)
  have hw : (∫⁻ z, totalProcessWork z.2 ∂P) ≤ ENNReal.ofReal B := hbudget qp
  have hwork : (∫⁻ z, totalProcessWork z.2 ∂P) < ∞ :=
    lt_of_le_of_lt hw ENNReal.ofReal_lt_top
  have hbound := creation_infinite_kl_bound (PopulationSeed R) (PopulationSeed R × ProcessTape)
    (populationSeedLaw μ A) P Q Prod.fst Prod.snd (populationPolicy A) populationGap η h
    measurable_fst (fun n b => measurableSet_eq_fun
      ((measurable_pi_apply n).comp measurable_snd) measurable_const)
    (measurable_populationPolicy A) measurable_populationGap hηm
    (by exact hP)
    (by exact hQ)
    hh (fun u i => (u.2 i).property)
    (fun u i => hardEta_bounds hh.le (u.2 i))
    (fun u i => gap_mul_hardEta_le (u.2 i)) hwork
  have hkl : klDiv P Q ≤ ENNReal.ofReal (1/8:ℝ) := by
    have hk : klDiv P Q ≤ ENNReal.ofReal ((128/225:ℝ)*h^2) *
        ∫⁻ z, totalProcessWork z.2 ∂P := by
      simpa only [infiniteTranscriptLaw, Prod.mk.eta, Measure.map_id'] using hbound
    apply hk.trans
    calc
      _ ≤ ENNReal.ofReal ((128/225:ℝ)*h^2) * ENNReal.ofReal B :=
        mul_le_mul le_rfl hw bot_le bot_le
      _ = ENNReal.ofReal ((128/225:ℝ)*h^2*B) :=
        (ENNReal.ofReal_mul (by positivity)).symm
      _ ≤ ENNReal.ofReal (1/8:ℝ) := by
        apply ENNReal.ofReal_le_ofReal
        have hs : h^2*B = 1/16 := (budget_hard_pair μ B hB).2.1
        nlinarith
  have hsep : a-b = (1/4:ℝ)*modulus μ h := hard_pair_separation μ h hh
  have hgap : 0 < a-b := by
    rw [hsep]
    exact mul_pos (by norm_num) (modulus_pos μ hh)
  have hne : a ≠ b := by intro he; rw [he, sub_self] at hgap; exact lt_irrefl _ hgap
  have hsq := two_point_risk_lower_of_ne P Q (populationOutput A) a b
    (measurable_populationOutput A) hne hkl
  have hsquared : ENNReal.ofReal ((a-b)^2/16) ≤
      max (squaredRisk P (populationOutput A) a) (squaredRisk Q (populationOutput A) b) := by
    convert hsq using 1 <;> congr 1 <;> ring
  have hrms := rms_of_squared_lower P Q (populationOutput A) a b (a-b) hgap.le hsquared
  have hscale : modulus μ (1/Real.sqrt B)/16 ≤ a-b := (budget_hard_pair μ B hB).2.2
  calc
    ENNReal.ofReal (modulus μ (1/Real.sqrt B)/64) ≤ ENNReal.ofReal ((a-b)/4) :=
      ENNReal.ofReal_le_ofReal (by linarith)
    _ ≤ max (rootMeanRisk P (populationOutput A) a) (rootMeanRisk Q (populationOutput A) b) := hrms
    _ ≤ maximalRMSRisk μ A := max_le
      (le_iSup (fun q : SignLaw => rootMeanRisk (experimentLaw μ A q)
        (populationOutput A) (signMean μ q.val)) qp)
      (le_iSup (fun q : SignLaw => rootMeanRisk (experimentLaw μ A q)
        (populationOutput A) (signMean μ q.val)) qm)

end ThresholdHC.Tier6
