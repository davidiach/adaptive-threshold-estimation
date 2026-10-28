import ThresholdHC.OracleLower.Realization
import ThresholdHC.Tier6.Full

noncomputable section
open MeasureTheory InformationTheory
open scoped ENNReal
namespace ThresholdHC.OracleLower
open ThresholdHC.Tier3 ThresholdHC.Tier4 ThresholdHC.Tier5 ThresholdHC.Tier6

/-- The information bound charges actual flips even when all potential gaps
are known to the policy. No sampling law for the gap array is required. -/
theorem oracle_hard_pair_information {R : Type} [MeasurableSpace R]
    (A : OracleEstimator R) (B h : ℝ) (hh : 0 < h) (hbudget : OracleBudget A B) :
    let hv := hard_pair_validity h hh
    let qp : SignLaw := ⟨hardPlus h,hv.2.1,fun d => (hv.2.2.2 d).2.2.1⟩
    let qm : SignLaw := ⟨hardMinus h,hv.2.2.1,fun d => (hv.2.2.2 d).2.2.2⟩
    klDiv (oracleLaw A qp) (oracleLaw A qm) ≤ ENNReal.ofReal ((128/225:ℝ)*h^2*B) := by
  intro hv qp qm
  let P := oracleLaw A qp
  let Q := oracleLaw A qm
  let η : R → ℕ → ℝ := fun u i => hardEta h (A.gap u i)
  have hP := (oracle_realization R A qp).2
  have hQ := (oracle_realization R A qm).2
  have hηm : MeasurableEnvironment η :=
    fun i => (measurable_hardEta h).comp (A.gap_measurable i)
  have hw : (∫⁻ z, totalProcessWork z.2 ∂P) ≤ ENNReal.ofReal B := hbudget qp
  have hwork : (∫⁻ z, totalProcessWork z.2 ∂P) < ∞ :=
    lt_of_le_of_lt hw ENNReal.ofReal_lt_top
  have hbound := creation_infinite_kl_bound R (R × ProcessTape)
    A.randomLaw P Q Prod.fst Prod.snd A.policy (fun u i => A.gap u i) η h
    measurable_fst (fun n b => measurableSet_eq_fun
      ((measurable_pi_apply n).comp measurable_snd) measurable_const)
    A.policy_measurable (fun i => measurable_subtype_coe.comp (A.gap_measurable i)) hηm
    (by exact hP) (by exact hQ) hh (fun u i => (A.gap u i).property)
    (fun u i => hardEta_bounds hh.le (A.gap u i))
    (fun u i => gap_mul_hardEta_le (A.gap u i)) hwork
  have hk : klDiv P Q ≤ ENNReal.ofReal ((128/225:ℝ)*h^2) *
      ∫⁻ z, totalProcessWork z.2 ∂P := by
    simpa only [infiniteTranscriptLaw,Prod.mk.eta,Measure.map_id'] using hbound
  apply hk.trans
  calc
    _ ≤ ENNReal.ofReal ((128/225:ℝ)*h^2) * ENNReal.ofReal B :=
      mul_le_mul le_rfl hw bot_le bot_le
    _ = ENNReal.ofReal ((128/225:ℝ)*h^2*B) :=
      (ENNReal.ofReal_mul (by positivity)).symm

end ThresholdHC.OracleLower
