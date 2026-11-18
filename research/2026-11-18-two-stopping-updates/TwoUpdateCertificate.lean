import TwoUpdateBellman

namespace PilotFeedback.TwoUpdates

set_option maxHeartbeats 0
set_option maxRecDepth 100000

private theorem row0 : Row 0 := by decide +kernel
private theorem row1 : Row 1 := by decide +kernel
private theorem row2 : Row 2 := by decide +kernel
private theorem row3 : Row 3 := by decide +kernel
private theorem row4 : Row 4 := by decide +kernel
private theorem row5 : Row 5 := by decide +kernel
private theorem row6 : Row 6 := by decide +kernel
private theorem row7 : Row 7 := by decide +kernel
private theorem row8 : Row 8 := by decide +kernel
private theorem row9 : Row 9 := by decide +kernel
private theorem row10 : Row 10 := by decide +kernel
private theorem row11 : Row 11 := by decide +kernel
private theorem row12 : Row 12 := by decide +kernel
private theorem row13 : Row 13 := by decide +kernel
private theorem row14 : Row 14 := by decide +kernel
private theorem row15 : Row 15 := by decide +kernel
private theorem row16 : Row 16 := by decide +kernel
private theorem row17 : Row 17 := by decide +kernel
private theorem row18 : Row 18 := by decide +kernel

theorem certified (j : Fin 19) : Row j := by
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

theorem total_eq : pilotSum 18 0 = 34880963526638591801106 := by decide +kernel

theorem total : 186764460^2 * 10^6 ≤ pilotSum 18 0 := by rw [total_eq]; decide

end PilotFeedback.TwoUpdates
