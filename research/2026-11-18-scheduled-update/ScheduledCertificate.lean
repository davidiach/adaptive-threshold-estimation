import ScheduledBounds

namespace PilotFeedback.Scheduled

set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem certified (j : Fin 19) : Row j := by
  fin_cases j <;> decide +kernel

theorem certificate_total : 186960371^2 * 10^6 ≤ pilotSum 18 0 := by decide +kernel

end PilotFeedback.Scheduled
