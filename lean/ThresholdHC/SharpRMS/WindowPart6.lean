import ThresholdHC.SharpRMS.WindowBound

/-! Bias intervals 101 to 120 of the intermediate window. Each closed
comparison checks all 2,048 bins, all 19 finite barrier prices and the tail
price. The kernel reduces it in the form `fastBound`, and
`gridBound_of_fastBound` gives `gridBound`. -/
namespace ThresholdHC.SharpRMS.Window

set_option maxHeartbeats 8000000
set_option maxRecDepth 200000

theorem interval101 : gridBound 25952 26320 := gridBound_of_fastBound (by decide +kernel)
theorem interval102 : gridBound 26320 26688 := gridBound_of_fastBound (by decide +kernel)
theorem interval103 : gridBound 26688 27056 := gridBound_of_fastBound (by decide +kernel)
theorem interval104 : gridBound 27056 27424 := gridBound_of_fastBound (by decide +kernel)
theorem interval105 : gridBound 27424 27792 := gridBound_of_fastBound (by decide +kernel)
theorem interval106 : gridBound 27792 28160 := gridBound_of_fastBound (by decide +kernel)
theorem interval107 : gridBound 28160 28528 := gridBound_of_fastBound (by decide +kernel)
theorem interval108 : gridBound 28528 28896 := gridBound_of_fastBound (by decide +kernel)
theorem interval109 : gridBound 28896 29264 := gridBound_of_fastBound (by decide +kernel)
theorem interval110 : gridBound 29264 29632 := gridBound_of_fastBound (by decide +kernel)
theorem interval111 : gridBound 29632 30000 := gridBound_of_fastBound (by decide +kernel)
theorem interval112 : gridBound 30000 30368 := gridBound_of_fastBound (by decide +kernel)
theorem interval113 : gridBound 30368 30736 := gridBound_of_fastBound (by decide +kernel)
theorem interval114 : gridBound 30736 31104 := gridBound_of_fastBound (by decide +kernel)
theorem interval115 : gridBound 31104 31472 := gridBound_of_fastBound (by decide +kernel)
theorem interval116 : gridBound 31472 31840 := gridBound_of_fastBound (by decide +kernel)
theorem interval117 : gridBound 31840 32208 := gridBound_of_fastBound (by decide +kernel)
theorem interval118 : gridBound 32208 32576 := gridBound_of_fastBound (by decide +kernel)
theorem interval119 : gridBound 32576 32944 := gridBound_of_fastBound (by decide +kernel)
theorem interval120 : gridBound 32944 33312 := gridBound_of_fastBound (by decide +kernel)

end ThresholdHC.SharpRMS.Window
