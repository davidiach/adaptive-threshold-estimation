import ThresholdHC.SharpRMS.WindowBound

/-! Bias intervals 081 to 100 of the intermediate window. Each closed
comparison checks all 2,048 bins, all 19 finite barrier prices and the tail
price, and reduces in the Lean kernel. -/
namespace ThresholdHC.SharpRMS.Window

set_option maxHeartbeats 8000000
set_option maxRecDepth 200000

theorem interval081 : gridBound 21352 21536 := by decide +kernel
theorem interval082 : gridBound 21536 21720 := by decide +kernel
theorem interval083 : gridBound 21720 21904 := by decide +kernel
theorem interval084 : gridBound 21904 22088 := by decide +kernel
theorem interval085 : gridBound 22088 22272 := by decide +kernel
theorem interval086 : gridBound 22272 22456 := by decide +kernel
theorem interval087 : gridBound 22456 22640 := by decide +kernel
theorem interval088 : gridBound 22640 22824 := by decide +kernel
theorem interval089 : gridBound 22824 23008 := by decide +kernel
theorem interval090 : gridBound 23008 23192 := by decide +kernel
theorem interval091 : gridBound 23192 23376 := by decide +kernel
theorem interval092 : gridBound 23376 23560 := by decide +kernel
theorem interval093 : gridBound 23560 23744 := by decide +kernel
theorem interval094 : gridBound 23744 23928 := by decide +kernel
theorem interval095 : gridBound 23928 24112 := by decide +kernel
theorem interval096 : gridBound 24112 24480 := by decide +kernel
theorem interval097 : gridBound 24480 24848 := by decide +kernel
theorem interval098 : gridBound 24848 25216 := by decide +kernel
theorem interval099 : gridBound 25216 25584 := by decide +kernel
theorem interval100 : gridBound 25584 25952 := by decide +kernel

end ThresholdHC.SharpRMS.Window
