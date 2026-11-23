import ThresholdHC.SharpRMS.WindowBound

/-! Bias intervals 121 to 140 of the intermediate window. Each closed
comparison checks all 2,048 bins, all 19 finite barrier prices and the tail
price. The kernel reduces it in the form `fastBound`, and
`gridBound_of_fastBound` gives `gridBound`. -/
namespace ThresholdHC.SharpRMS.Window

set_option maxHeartbeats 8000000
set_option maxRecDepth 200000

theorem interval121 : gridBound 33312 33680 := gridBound_of_fastBound (by decide +kernel)
theorem interval122 : gridBound 33680 34048 := gridBound_of_fastBound (by decide +kernel)
theorem interval123 : gridBound 34048 34416 := gridBound_of_fastBound (by decide +kernel)
theorem interval124 : gridBound 34416 34784 := gridBound_of_fastBound (by decide +kernel)
theorem interval125 : gridBound 34784 35152 := gridBound_of_fastBound (by decide +kernel)
theorem interval126 : gridBound 35152 35520 := gridBound_of_fastBound (by decide +kernel)
theorem interval127 : gridBound 35520 35888 := gridBound_of_fastBound (by decide +kernel)
theorem interval128 : gridBound 35888 36256 := gridBound_of_fastBound (by decide +kernel)
theorem interval129 : gridBound 36256 36624 := gridBound_of_fastBound (by decide +kernel)
theorem interval130 : gridBound 36624 36992 := gridBound_of_fastBound (by decide +kernel)
theorem interval131 : gridBound 36992 37360 := gridBound_of_fastBound (by decide +kernel)
theorem interval132 : gridBound 37360 37728 := gridBound_of_fastBound (by decide +kernel)
theorem interval133 : gridBound 37728 38096 := gridBound_of_fastBound (by decide +kernel)
theorem interval134 : gridBound 38096 38464 := gridBound_of_fastBound (by decide +kernel)
theorem interval135 : gridBound 38464 38832 := gridBound_of_fastBound (by decide +kernel)
theorem interval136 : gridBound 38832 39200 := gridBound_of_fastBound (by decide +kernel)
theorem interval137 : gridBound 39200 39384 := gridBound_of_fastBound (by decide +kernel)
theorem interval138 : gridBound 39384 39568 := gridBound_of_fastBound (by decide +kernel)
theorem interval139 : gridBound 39568 39752 := gridBound_of_fastBound (by decide +kernel)
theorem interval140 : gridBound 39752 39936 := gridBound_of_fastBound (by decide +kernel)

end ThresholdHC.SharpRMS.Window
