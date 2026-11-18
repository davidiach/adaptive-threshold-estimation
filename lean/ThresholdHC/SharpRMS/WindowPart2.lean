import ThresholdHC.SharpRMS.WindowBound

/-! Bias intervals 021 to 040 of the intermediate window. Each closed
comparison checks all 2,048 bins, all 19 finite barrier prices and the tail
price, and reduces in the Lean kernel. -/
namespace ThresholdHC.SharpRMS.Window

set_option maxHeartbeats 8000000
set_option maxRecDepth 200000

theorem interval021 : gridBound 16844 16867 := by decide +kernel
theorem interval022 : gridBound 16867 16890 := by decide +kernel
theorem interval023 : gridBound 16890 16913 := by decide +kernel
theorem interval024 : gridBound 16913 16936 := by decide +kernel
theorem interval025 : gridBound 16936 16959 := by decide +kernel
theorem interval026 : gridBound 16959 16982 := by decide +kernel
theorem interval027 : gridBound 16982 17028 := by decide +kernel
theorem interval028 : gridBound 17028 17074 := by decide +kernel
theorem interval029 : gridBound 17074 17120 := by decide +kernel
theorem interval030 : gridBound 17120 17166 := by decide +kernel
theorem interval031 : gridBound 17166 17212 := by decide +kernel
theorem interval032 : gridBound 17212 17258 := by decide +kernel
theorem interval033 : gridBound 17258 17304 := by decide +kernel
theorem interval034 : gridBound 17304 17350 := by decide +kernel
theorem interval035 : gridBound 17350 17396 := by decide +kernel
theorem interval036 : gridBound 17396 17442 := by decide +kernel
theorem interval037 : gridBound 17442 17488 := by decide +kernel
theorem interval038 : gridBound 17488 17534 := by decide +kernel
theorem interval039 : gridBound 17534 17580 := by decide +kernel
theorem interval040 : gridBound 17580 17626 := by decide +kernel

end ThresholdHC.SharpRMS.Window
