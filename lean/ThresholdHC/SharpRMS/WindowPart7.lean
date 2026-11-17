import ThresholdHC.SharpRMS.WindowBound

/-! Bias intervals 121 to 140 of the intermediate window. Each closed
comparison checks all 2,048 bins, all 19 finite barrier prices and the tail
price, and reduces in the Lean kernel. -/
namespace ThresholdHC.SharpRMS.Window

set_option maxHeartbeats 8000000
set_option maxRecDepth 200000

theorem interval121 : gridBound 33312 33680 := by decide +kernel
theorem interval122 : gridBound 33680 34048 := by decide +kernel
theorem interval123 : gridBound 34048 34416 := by decide +kernel
theorem interval124 : gridBound 34416 34784 := by decide +kernel
theorem interval125 : gridBound 34784 35152 := by decide +kernel
theorem interval126 : gridBound 35152 35520 := by decide +kernel
theorem interval127 : gridBound 35520 35888 := by decide +kernel
theorem interval128 : gridBound 35888 36256 := by decide +kernel
theorem interval129 : gridBound 36256 36624 := by decide +kernel
theorem interval130 : gridBound 36624 36992 := by decide +kernel
theorem interval131 : gridBound 36992 37360 := by decide +kernel
theorem interval132 : gridBound 37360 37728 := by decide +kernel
theorem interval133 : gridBound 37728 38096 := by decide +kernel
theorem interval134 : gridBound 38096 38464 := by decide +kernel
theorem interval135 : gridBound 38464 38832 := by decide +kernel
theorem interval136 : gridBound 38832 39200 := by decide +kernel
theorem interval137 : gridBound 39200 39384 := by decide +kernel
theorem interval138 : gridBound 39384 39568 := by decide +kernel
theorem interval139 : gridBound 39568 39752 := by decide +kernel
theorem interval140 : gridBound 39752 39936 := by decide +kernel

end ThresholdHC.SharpRMS.Window
