import ThresholdHC.FiniteBayesAllocation.Kernel

/-! Kernel certificates for two scales: floor and ceiling sums, at precision
`10^20`, of the scaled posterior variance over the `256` ordered words, for the
table policy, the fresh design and the single-coin design. -/

namespace ThresholdHC.FiniteBayesAllocation

theorem two_adaptive_cert : certify (scaleOf twoCode) (run twoCode (tableLabel twoScalesTable)) =
    (1267069800743260913, 1267069800743261169, true) := by
  decide +kernel

theorem two_fresh_cert : certify (scaleOf twoCode) (run twoCode (fun xs => xs.length)) =
    (1289486011602810850, 1289486011602811106, true) := by
  decide +kernel

theorem two_single_cert : certify (scaleOf twoCode) (run twoCode (fun _ => 0)) =
    (1287564515565886501, 1287564515565886757, true) := by
  decide +kernel

end ThresholdHC.FiniteBayesAllocation
