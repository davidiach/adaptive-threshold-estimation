import ThresholdHC.SharpRMS.WindowBound

/-! Bias intervals 041 to 060 of the intermediate window. Each closed
comparison checks all 2,048 bins, all 19 finite barrier prices and the tail
price. The kernel reduces it in the form `fastBound`, and
`gridBound_of_fastBound` gives `gridBound`. -/
namespace ThresholdHC.SharpRMS.Window

set_option maxHeartbeats 8000000
set_option maxRecDepth 200000

theorem interval041 : gridBound 17626 17672 := gridBound_of_fastBound (by decide +kernel)
theorem interval042 : gridBound 17672 17718 := gridBound_of_fastBound (by decide +kernel)
theorem interval043 : gridBound 17718 17764 := gridBound_of_fastBound (by decide +kernel)
theorem interval044 : gridBound 17764 17810 := gridBound_of_fastBound (by decide +kernel)
theorem interval045 : gridBound 17810 17856 := gridBound_of_fastBound (by decide +kernel)
theorem interval046 : gridBound 17856 17902 := gridBound_of_fastBound (by decide +kernel)
theorem interval047 : gridBound 17902 17948 := gridBound_of_fastBound (by decide +kernel)
theorem interval048 : gridBound 17948 17994 := gridBound_of_fastBound (by decide +kernel)
theorem interval049 : gridBound 17994 18040 := gridBound_of_fastBound (by decide +kernel)
theorem interval050 : gridBound 18040 18086 := gridBound_of_fastBound (by decide +kernel)
theorem interval051 : gridBound 18086 18132 := gridBound_of_fastBound (by decide +kernel)
theorem interval052 : gridBound 18132 18224 := gridBound_of_fastBound (by decide +kernel)
theorem interval053 : gridBound 18224 18316 := gridBound_of_fastBound (by decide +kernel)
theorem interval054 : gridBound 18316 18408 := gridBound_of_fastBound (by decide +kernel)
theorem interval055 : gridBound 18408 18500 := gridBound_of_fastBound (by decide +kernel)
theorem interval056 : gridBound 18500 18592 := gridBound_of_fastBound (by decide +kernel)
theorem interval057 : gridBound 18592 18684 := gridBound_of_fastBound (by decide +kernel)
theorem interval058 : gridBound 18684 18776 := gridBound_of_fastBound (by decide +kernel)
theorem interval059 : gridBound 18776 18868 := gridBound_of_fastBound (by decide +kernel)
theorem interval060 : gridBound 18868 18960 := gridBound_of_fastBound (by decide +kernel)

end ThresholdHC.SharpRMS.Window
