import ThresholdHC.MarginClasses.Power
import ThresholdHC.MarginClasses.Unbiased

/-! The margin-class corollaries: Corollary `cor:gap`, the rows `0 < α < 1`
and `α > 1` of Corollary `cor:power`, its unbiased dichotomy, and the common
estimators. The upper halves of the three work statements come from the one
common confidence family by taking it as the witness of the infimum. -/
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace ThresholdHC.MarginClasses
open ThresholdHC.Tier6 ThresholdHC.Confidence ThresholdHC.Envelope

/-- One `(B,δ)` family attains every stated upper budget. -/
theorem common_confidence : CommonConfidenceStatement := by
  obtain ⟨R,mR,rule,h⟩ := common_rule
  refine ⟨R,mR,rule,?_,?_,?_⟩
  · intro Δ ε δ hΔ hΔ' hε hε' hδ hδ' ν _ hν
    obtain ⟨hB,hm⟩ := gap_scale hΔ hΔ' hε hε' hδ hδ'
    exact h _ δ ε hB hδ hδ' (Measure.dirac (⟨Δ,hΔ,hΔ'⟩ : Gap)) ν (gapClass_within hΔ hΔ' ν hν) hm
  · intro α C ε δ hα hα1 hC hε hε' hδ hδ' ν _ hν
    obtain ⟨hB,hm⟩ := sub_scale hα hα1 hC hε hε' hδ hδ' ν hν
    exact h _ δ ε hB hδ hδ' ν ν (within_self ν) hm
  · intro α C ε δ hα hC hε hε' hδ hδ' ν _ hν
    obtain ⟨hB,hm⟩ := super_scale hα hC hε hε' hδ hδ' ν hν
    exact h _ δ ε hB hδ hδ' ν ν (within_self ν) hm

/-- Corollary `cor:gap`. -/
theorem gap_class : GapClassStatement := by
  intro Δ ε δ hΔ hΔ' hε hε' hδ hδ'
  refine ⟨gap_lower hΔ hΔ' hε hε' hδ hδ',?_⟩
  obtain ⟨R,mR,rule,hg,_,_⟩ := common_confidence
  exact sInf_le ⟨R,mR,rule _ δ,_,fun ν _ hν => hg Δ ε δ hΔ hΔ' hε hε' hδ hδ' ν hν,rfl⟩

/-- Corollary `cor:power`, row `0 < α < 1`. -/
theorem sublinear_class : SublinearClassStatement := by
  intro α C ε δ hα hα1 hC hε hε' hδ hδ'
  refine ⟨sub_lower hα hC hε hε' hδ hδ',?_⟩
  obtain ⟨R,mR,rule,_,hs,_⟩ := common_confidence
  exact sInf_le ⟨R,mR,rule _ δ,_,fun ν _ hν => hs α C ε δ hα hα1 hC hε hε' hδ hδ' ν hν,rfl⟩

/-- Corollary `cor:power`, row `α > 1`. -/
theorem superlinear_class : SuperlinearClassStatement := by
  intro α C ε δ hα hC hε hε' hδ hδ'
  refine ⟨super_lower hα hC hε hε' hδ hδ',?_⟩
  obtain ⟨R,mR,rule,_,_,hs⟩ := common_confidence
  exact sInf_le ⟨R,mR,rule _ δ,_,fun ν _ hν => hs α C ε δ hα hC hε hε' hδ hδ' ν hν,rfl⟩

/-- Corollary `cor:power`, the unbiased dichotomy. -/
theorem power_unbiased : PowerUnbiasedStatement := unbiased_dichotomy

/-- Corollary `cor:power`, the common unbiased estimator for `α > 1`. -/
theorem common_unbiased : CommonUnbiasedStatement := common_unbiased_estimator

end ThresholdHC.MarginClasses
