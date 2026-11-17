import ThresholdHC.SharpRMS.WindowPart1
import ThresholdHC.SharpRMS.WindowPart2
import ThresholdHC.SharpRMS.WindowPart3
import ThresholdHC.SharpRMS.WindowPart4
import ThresholdHC.SharpRMS.WindowPart5
import ThresholdHC.SharpRMS.WindowPart6
import ThresholdHC.SharpRMS.WindowPart7

/-! The 140 adjacent bias intervals of the intermediate window form one chain.
The continuous enclosure argument is a separate step. -/
namespace ThresholdHC.SharpRMS.Window

/-- Consecutive integer endpoints are on the 1/40960 bias grid. -/
theorem checked_window : gridChain 16384 endpoints :=
  ⟨interval001, interval002, interval003, interval004, interval005, interval006, interval007, interval008,
    interval009, interval010, interval011, interval012, interval013, interval014, interval015, interval016,
    interval017, interval018, interval019, interval020, interval021, interval022, interval023, interval024,
    interval025, interval026, interval027, interval028, interval029, interval030, interval031, interval032,
    interval033, interval034, interval035, interval036, interval037, interval038, interval039, interval040,
    interval041, interval042, interval043, interval044, interval045, interval046, interval047, interval048,
    interval049, interval050, interval051, interval052, interval053, interval054, interval055, interval056,
    interval057, interval058, interval059, interval060, interval061, interval062, interval063, interval064,
    interval065, interval066, interval067, interval068, interval069, interval070, interval071, interval072,
    interval073, interval074, interval075, interval076, interval077, interval078, interval079, interval080,
    interval081, interval082, interval083, interval084, interval085, interval086, interval087, interval088,
    interval089, interval090, interval091, interval092, interval093, interval094, interval095, interval096,
    interval097, interval098, interval099, interval100, interval101, interval102, interval103, interval104,
    interval105, interval106, interval107, interval108, interval109, interval110, interval111, interval112,
    interval113, interval114, interval115, interval116, interval117, interval118, interval119, interval120,
    interval121, interval122, interval123, interval124, interval125, interval126, interval127, interval128,
    interval129, interval130, interval131, interval132, interval133, interval134, interval135, interval136,
    interval137, interval138, interval139, interval140, True.intro⟩

end ThresholdHC.SharpRMS.Window
