import ThresholdHC.FiniteBayesAllocation.Kernel

/-! Kernel certificates for three scales: floor and ceiling sums, at precision
`10^20`, of the scaled posterior variance over the `256` ordered words, for the
table policy, the fresh design and the single-coin design. -/

namespace ThresholdHC.FiniteBayesAllocation

theorem three_adaptive_cert :
    certify (scaleOf threeCode) (run threeCode (tableLabel threeScalesTable)) =
      (1194710358878043972, 1194710358878044228, true) := by
  decide +kernel

theorem three_fresh_cert : certify (scaleOf threeCode) (run threeCode (fun xs => xs.length)) =
    (1257996646109909931, 1257996646109910187, true) := by
  decide +kernel

theorem three_single_cert : certify (scaleOf threeCode) (run threeCode (fun _ => 0)) =
    (1308105438553130292, 1308105438553130548, true) := by
  decide +kernel

end ThresholdHC.FiniteBayesAllocation
