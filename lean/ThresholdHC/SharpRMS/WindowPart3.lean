import ThresholdHC.SharpRMS.WindowBound

/-! Bias intervals 041 to 060 of the intermediate window. Each closed
comparison checks all 2,048 bins, all 19 finite barrier prices and the tail
price, and reduces in the Lean kernel. -/
namespace ThresholdHC.SharpRMS.Window

set_option maxHeartbeats 8000000
set_option maxRecDepth 200000

theorem interval041 : gridBound 17626 17672 := by decide +kernel
theorem interval042 : gridBound 17672 17718 := by decide +kernel
theorem interval043 : gridBound 17718 17764 := by decide +kernel
theorem interval044 : gridBound 17764 17810 := by decide +kernel
theorem interval045 : gridBound 17810 17856 := by decide +kernel
theorem interval046 : gridBound 17856 17902 := by decide +kernel
theorem interval047 : gridBound 17902 17948 := by decide +kernel
theorem interval048 : gridBound 17948 17994 := by decide +kernel
theorem interval049 : gridBound 17994 18040 := by decide +kernel
theorem interval050 : gridBound 18040 18086 := by decide +kernel
theorem interval051 : gridBound 18086 18132 := by decide +kernel
theorem interval052 : gridBound 18132 18224 := by decide +kernel
theorem interval053 : gridBound 18224 18316 := by decide +kernel
theorem interval054 : gridBound 18316 18408 := by decide +kernel
theorem interval055 : gridBound 18408 18500 := by decide +kernel
theorem interval056 : gridBound 18500 18592 := by decide +kernel
theorem interval057 : gridBound 18592 18684 := by decide +kernel
theorem interval058 : gridBound 18684 18776 := by decide +kernel
theorem interval059 : gridBound 18776 18868 := by decide +kernel
theorem interval060 : gridBound 18868 18960 := by decide +kernel

end ThresholdHC.SharpRMS.Window
