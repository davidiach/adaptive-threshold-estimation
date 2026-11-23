import ThresholdHC.SharpRMS.WindowBound

/-! Bias intervals 081 to 100 of the intermediate window. Each closed
comparison checks all 2,048 bins, all 19 finite barrier prices and the tail
price. The kernel reduces it in the form `fastBound`, and
`gridBound_of_fastBound` gives `gridBound`. -/
namespace ThresholdHC.SharpRMS.Window

set_option maxHeartbeats 8000000
set_option maxRecDepth 200000

theorem interval081 : gridBound 21352 21536 := gridBound_of_fastBound (by decide +kernel)
theorem interval082 : gridBound 21536 21720 := gridBound_of_fastBound (by decide +kernel)
theorem interval083 : gridBound 21720 21904 := gridBound_of_fastBound (by decide +kernel)
theorem interval084 : gridBound 21904 22088 := gridBound_of_fastBound (by decide +kernel)
theorem interval085 : gridBound 22088 22272 := gridBound_of_fastBound (by decide +kernel)
theorem interval086 : gridBound 22272 22456 := gridBound_of_fastBound (by decide +kernel)
theorem interval087 : gridBound 22456 22640 := gridBound_of_fastBound (by decide +kernel)
theorem interval088 : gridBound 22640 22824 := gridBound_of_fastBound (by decide +kernel)
theorem interval089 : gridBound 22824 23008 := gridBound_of_fastBound (by decide +kernel)
theorem interval090 : gridBound 23008 23192 := gridBound_of_fastBound (by decide +kernel)
theorem interval091 : gridBound 23192 23376 := gridBound_of_fastBound (by decide +kernel)
theorem interval092 : gridBound 23376 23560 := gridBound_of_fastBound (by decide +kernel)
theorem interval093 : gridBound 23560 23744 := gridBound_of_fastBound (by decide +kernel)
theorem interval094 : gridBound 23744 23928 := gridBound_of_fastBound (by decide +kernel)
theorem interval095 : gridBound 23928 24112 := gridBound_of_fastBound (by decide +kernel)
theorem interval096 : gridBound 24112 24480 := gridBound_of_fastBound (by decide +kernel)
theorem interval097 : gridBound 24480 24848 := gridBound_of_fastBound (by decide +kernel)
theorem interval098 : gridBound 24848 25216 := gridBound_of_fastBound (by decide +kernel)
theorem interval099 : gridBound 25216 25584 := gridBound_of_fastBound (by decide +kernel)
theorem interval100 : gridBound 25584 25952 := gridBound_of_fastBound (by decide +kernel)

end ThresholdHC.SharpRMS.Window
