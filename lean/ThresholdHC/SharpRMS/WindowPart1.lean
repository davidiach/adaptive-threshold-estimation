import ThresholdHC.SharpRMS.WindowBound

/-! Bias intervals 001 to 020 of the intermediate window. Each closed
comparison checks all 2,048 bins, all 19 finite barrier prices and the tail
price, and reduces in the Lean kernel. -/
namespace ThresholdHC.SharpRMS.Window

set_option maxHeartbeats 8000000
set_option maxRecDepth 200000

theorem interval001 : gridBound 16384 16407 := by decide +kernel
theorem interval002 : gridBound 16407 16430 := by decide +kernel
theorem interval003 : gridBound 16430 16453 := by decide +kernel
theorem interval004 : gridBound 16453 16476 := by decide +kernel
theorem interval005 : gridBound 16476 16499 := by decide +kernel
theorem interval006 : gridBound 16499 16522 := by decide +kernel
theorem interval007 : gridBound 16522 16545 := by decide +kernel
theorem interval008 : gridBound 16545 16568 := by decide +kernel
theorem interval009 : gridBound 16568 16591 := by decide +kernel
theorem interval010 : gridBound 16591 16614 := by decide +kernel
theorem interval011 : gridBound 16614 16637 := by decide +kernel
theorem interval012 : gridBound 16637 16660 := by decide +kernel
theorem interval013 : gridBound 16660 16683 := by decide +kernel
theorem interval014 : gridBound 16683 16706 := by decide +kernel
theorem interval015 : gridBound 16706 16729 := by decide +kernel
theorem interval016 : gridBound 16729 16752 := by decide +kernel
theorem interval017 : gridBound 16752 16775 := by decide +kernel
theorem interval018 : gridBound 16775 16798 := by decide +kernel
theorem interval019 : gridBound 16798 16821 := by decide +kernel
theorem interval020 : gridBound 16821 16844 := by decide +kernel

end ThresholdHC.SharpRMS.Window
