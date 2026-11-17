import ThresholdHC.SharpRMS.WindowBound

/-! Bias intervals 061 to 080 of the intermediate window. Each closed
comparison checks all 2,048 bins, all 19 finite barrier prices and the tail
price, and reduces in the Lean kernel. -/
namespace ThresholdHC.SharpRMS.Window

set_option maxHeartbeats 8000000
set_option maxRecDepth 200000

theorem interval061 : gridBound 18960 19052 := by decide +kernel
theorem interval062 : gridBound 19052 19144 := by decide +kernel
theorem interval063 : gridBound 19144 19236 := by decide +kernel
theorem interval064 : gridBound 19236 19328 := by decide +kernel
theorem interval065 : gridBound 19328 19420 := by decide +kernel
theorem interval066 : gridBound 19420 19512 := by decide +kernel
theorem interval067 : gridBound 19512 19604 := by decide +kernel
theorem interval068 : gridBound 19604 19696 := by decide +kernel
theorem interval069 : gridBound 19696 19788 := by decide +kernel
theorem interval070 : gridBound 19788 19880 := by decide +kernel
theorem interval071 : gridBound 19880 19972 := by decide +kernel
theorem interval072 : gridBound 19972 20064 := by decide +kernel
theorem interval073 : gridBound 20064 20156 := by decide +kernel
theorem interval074 : gridBound 20156 20248 := by decide +kernel
theorem interval075 : gridBound 20248 20432 := by decide +kernel
theorem interval076 : gridBound 20432 20616 := by decide +kernel
theorem interval077 : gridBound 20616 20800 := by decide +kernel
theorem interval078 : gridBound 20800 20984 := by decide +kernel
theorem interval079 : gridBound 20984 21168 := by decide +kernel
theorem interval080 : gridBound 21168 21352 := by decide +kernel

end ThresholdHC.SharpRMS.Window
