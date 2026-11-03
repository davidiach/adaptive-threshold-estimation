import ThresholdHC.EntropyTail.Model
import ThresholdHC.EntropyTail.Specification
import ThresholdHC.EntropyTail.Band
import ThresholdHC.EntropyTail.Entropy
import ThresholdHC.EntropyTail.Gamma
import ThresholdHC.EntropyTail.Objective
import ThresholdHC.EntropyTail.Bounds
import ThresholdHC.EntropyTail.SingleAtom
import ThresholdHC.EntropyTail.Nonvacuity
import ThresholdHC.EntropyTail.Superadditive
import ThresholdHC.EntropyTail.HardSelection
import ThresholdHC.EntropyTail.Bridge
import ThresholdHC.EntropyTail.Upper
import ThresholdHC.EntropyTail.Lower
import ThresholdHC.EntropyTail.Law

example : ThresholdHC.EntropyTail.SelectionBoundsStatement := ThresholdHC.EntropyTail.selection_bounds
example : ThresholdHC.EntropyTail.SingleAtomStatement := ThresholdHC.EntropyTail.single_atom
example : ThresholdHC.EntropyTail.SmallBudgetStatement := ThresholdHC.EntropyTail.small_budget
example : ThresholdHC.EntropyTail.EntropyTailNonvacuityStatement := ThresholdHC.EntropyTail.entropy_tail_nonvacuity
example : ThresholdHC.EntropyTail.HardSelectionStatement := ThresholdHC.EntropyTail.hard_selection
example : ThresholdHC.EntropyTail.EntropyTailUpperStatement := ThresholdHC.EntropyTail.entropy_tail_upper
example : ThresholdHC.EntropyTail.EntropyTailLowerStatement := ThresholdHC.EntropyTail.entropy_tail_lower
example : ThresholdHC.EntropyTail.EntropyTailLawStatement := ThresholdHC.EntropyTail.entropy_tail_law

#print axioms ThresholdHC.EntropyTail.EntropyTailLawStatement
#print axioms ThresholdHC.EntropyTail.EntropyTailLowerStatement
#print axioms ThresholdHC.EntropyTail.EntropyTailNonvacuityStatement
#print axioms ThresholdHC.EntropyTail.EntropyTailUpperStatement
#print axioms ThresholdHC.EntropyTail.HardSelectionStatement
#print axioms ThresholdHC.EntropyTail.SelectionBoundsStatement
#print axioms ThresholdHC.EntropyTail.SingleAtomStatement
#print axioms ThresholdHC.EntropyTail.SmallBudgetStatement
#print axioms ThresholdHC.EntropyTail.band
#print axioms ThresholdHC.EntropyTail.bandCost
#print axioms ThresholdHC.EntropyTail.bandCost_dirac
#print axioms ThresholdHC.EntropyTail.bandCost_mono
#print axioms ThresholdHC.EntropyTail.bandCost_ne_top
#print axioms ThresholdHC.EntropyTail.bandCost_sum_smul
#print axioms ThresholdHC.EntropyTail.band_disjoint
#print axioms ThresholdHC.EntropyTail.costEntropy
#print axioms ThresholdHC.EntropyTail.costEntropy_add
#print axioms ThresholdHC.EntropyTail.costEntropy_eq_sum
#print axioms ThresholdHC.EntropyTail.costEntropy_mono
#print axioms ThresholdHC.EntropyTail.costEntropy_nonneg
#print axioms ThresholdHC.EntropyTail.costEntropy_prefix_le_succ
#print axioms ThresholdHC.EntropyTail.costEntropy_smul
#print axioms ThresholdHC.EntropyTail.entropyTerm_ofReal
#print axioms ThresholdHC.EntropyTail.entropy_tail_law
#print axioms ThresholdHC.EntropyTail.entropy_tail_lower
#print axioms ThresholdHC.EntropyTail.entropy_tail_nonvacuity
#print axioms ThresholdHC.EntropyTail.entropy_tail_upper
#print axioms ThresholdHC.EntropyTail.entropy_tail_upper_explicit
#print axioms ThresholdHC.EntropyTail.eq_smul_dirac_of_le
#print axioms ThresholdHC.EntropyTail.exists_band
#print axioms ThresholdHC.EntropyTail.four_le_inv_sq
#print axioms ThresholdHC.EntropyTail.four_mass_le_gamma
#print axioms ThresholdHC.EntropyTail.gamma
#print axioms ThresholdHC.EntropyTail.gamma_dirac_le
#print axioms ThresholdHC.EntropyTail.gamma_eq_iSup
#print axioms ThresholdHC.EntropyTail.gamma_le_quantile_measureCostEntropy
#print axioms ThresholdHC.EntropyTail.gamma_mono
#print axioms ThresholdHC.EntropyTail.gamma_zero
#print axioms ThresholdHC.EntropyTail.hard_le_objective_add
#print axioms ThresholdHC.EntropyTail.hard_selection
#print axioms ThresholdHC.EntropyTail.iInf_objective_lower
#print axioms ThresholdHC.EntropyTail.layer
#print axioms ThresholdHC.EntropyTail.layerDensity
#print axioms ThresholdHC.EntropyTail.layerDensity_bounds
#print axioms ThresholdHC.EntropyTail.layerMixture
#print axioms ThresholdHC.EntropyTail.lintegral_layerMixture
#print axioms ThresholdHC.EntropyTail.lintegral_le_gamma
#print axioms ThresholdHC.EntropyTail.logsum_two
#print axioms ThresholdHC.EntropyTail.measurableSet_band
#print axioms ThresholdHC.EntropyTail.measurableSet_layer
#print axioms ThresholdHC.EntropyTail.measurable_layerDensity
#print axioms ThresholdHC.EntropyTail.measurable_tailWeight
#print axioms ThresholdHC.EntropyTail.objective_eq_ofReal
#print axioms ThresholdHC.EntropyTail.objective_lower
#print axioms ThresholdHC.EntropyTail.ofReal_prefixEntropy_le_gamma
#print axioms ThresholdHC.EntropyTail.prefixEntropy
#print axioms ThresholdHC.EntropyTail.prefixEntropy_mono
#print axioms ThresholdHC.EntropyTail.prefixEntropy_nonneg
#print axioms ThresholdHC.EntropyTail.quantile_bandCost_eq
#print axioms ThresholdHC.EntropyTail.quantile_bandCost_lt_top
#print axioms ThresholdHC.EntropyTail.quantile_band_eq
#print axioms ThresholdHC.EntropyTail.quantile_costEntropy_eq
#print axioms ThresholdHC.EntropyTail.quantile_measureCostEntropy_le
#print axioms ThresholdHC.EntropyTail.quantile_prefix_eq
#print axioms ThresholdHC.EntropyTail.quantile_selectionValue_eq
#print axioms ThresholdHC.EntropyTail.quantile_selectionValue_le
#print axioms ThresholdHC.EntropyTail.quantile_tailModulus_eq
#print axioms ThresholdHC.EntropyTail.quantile_tailModulus_le
#print axioms ThresholdHC.EntropyTail.selection
#print axioms ThresholdHC.EntropyTail.selectionObjective
#print axioms ThresholdHC.EntropyTail.selectionObjective_self
#print axioms ThresholdHC.EntropyTail.selectionObjective_zero
#print axioms ThresholdHC.EntropyTail.selection_bounds
#print axioms ThresholdHC.EntropyTail.selection_le_objective
#print axioms ThresholdHC.EntropyTail.selection_le_rho
#print axioms ThresholdHC.EntropyTail.selection_quantile_comparison
#print axioms ThresholdHC.EntropyTail.single_atom
#print axioms ThresholdHC.EntropyTail.single_lower
#print axioms ThresholdHC.EntropyTail.small_budget
#print axioms ThresholdHC.EntropyTail.sum_bandCost_le_gamma
#print axioms ThresholdHC.EntropyTail.sum_le_costEntropy
#print axioms ThresholdHC.EntropyTail.sum_mul_sqrt_le
#print axioms ThresholdHC.EntropyTail.sum_smul_costEntropy_le
#print axioms ThresholdHC.EntropyTail.sum_smul_gamma_le
#print axioms ThresholdHC.EntropyTail.tailCost
#print axioms ThresholdHC.EntropyTail.tailCost_dirac
#print axioms ThresholdHC.EntropyTail.tailCost_le_mass
#print axioms ThresholdHC.EntropyTail.tailCost_lower
#print axioms ThresholdHC.EntropyTail.tailCost_smul
#print axioms ThresholdHC.EntropyTail.tailCost_sub_add
#print axioms ThresholdHC.EntropyTail.tailCost_sum_smul
#print axioms ThresholdHC.EntropyTail.tailCost_zero
