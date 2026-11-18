import StoppingBounds

namespace PilotFeedback.Stopping

set_option maxHeartbeats 0
set_option maxRecDepth 100000

private theorem row0 : rowCheck 0 = true := by decide +kernel
private theorem row1 : rowCheck 1 = true := by decide +kernel
private theorem row2 : rowCheck 2 = true := by decide +kernel
private theorem row3 : rowCheck 3 = true := by decide +kernel
private theorem row4 : rowCheck 4 = true := by decide +kernel
private theorem row5 : rowCheck 5 = true := by decide +kernel
private theorem row6 : rowCheck 6 = true := by decide +kernel
private theorem row7 : rowCheck 7 = true := by decide +kernel
private theorem row8 : rowCheck 8 = true := by decide +kernel
private theorem row9 : rowCheck 9 = true := by decide +kernel
private theorem row10 : rowCheck 10 = true := by decide +kernel
private theorem row11 : rowCheck 11 = true := by decide +kernel
private theorem row12 : rowCheck 12 = true := by decide +kernel
private theorem row13 : rowCheck 13 = true := by decide +kernel
private theorem row14 : rowCheck 14 = true := by decide +kernel
private theorem row15 : rowCheck 15 = true := by decide +kernel
private theorem row16 : rowCheck 16 = true := by decide +kernel
private theorem row17 : rowCheck 17 = true := by decide +kernel
private theorem row18 : rowCheck 18 = true := by decide +kernel

theorem certified (j : Fin 19) : rowCheck j = true := by
  fin_cases j
  · exact row0
  · exact row1
  · exact row2
  · exact row3
  · exact row4
  · exact row5
  · exact row6
  · exact row7
  · exact row8
  · exact row9
  · exact row10
  · exact row11
  · exact row12
  · exact row13
  · exact row14
  · exact row15
  · exact row16
  · exact row17
  · exact row18

theorem total : 186844275^2 * 10^6 ≤ pilotSum 18 0 := by decide +kernel

end PilotFeedback.Stopping
