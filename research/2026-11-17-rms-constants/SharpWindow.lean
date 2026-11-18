import SharpGridArithmetic

/-! Integer upper sums on the intermediate bias window. The public theorem
checks all 2,048 bins, all 19 finite barrier prices and the tail price on
each of the 140 adjacent bias intervals. Each closed comparison reduces in
the Lean kernel. The continuous enclosure argument is a separate step. -/
namespace ThresholdHC.SharpRMS.Window

/-- After multiplying by (hi/lo)^2, the scaled upper sum is at most 2/3. -/
def gridBound (lo hi : Nat) : Prop :=
  0 < lo ∧ lo ≤ hi ∧ 3*hi^2*upperSum hi ≤ 2*lo^2*bins*scale

instance (lo hi : Nat) : Decidable (gridBound lo hi) := inferInstanceAs
  (Decidable (0 < lo ∧ lo ≤ hi ∧ 3*hi^2*upperSum hi ≤ 2*lo^2*bins*scale))

def gridChain (lo : Nat) : List Nat → Prop
  | [] => True
  | hi :: rest => gridBound lo hi ∧ gridChain hi rest

def endpoints : List Nat := [
    16407, 16430, 16453, 16476, 16499, 16522, 16545, 16568, 16591, 16614, 16637, 16660,
    16683, 16706, 16729, 16752, 16775, 16798, 16821, 16844, 16867, 16890, 16913, 16936,
    16959, 16982, 17028, 17074, 17120, 17166, 17212, 17258, 17304, 17350, 17396, 17442,
    17488, 17534, 17580, 17626, 17672, 17718, 17764, 17810, 17856, 17902, 17948, 17994,
    18040, 18086, 18132, 18224, 18316, 18408, 18500, 18592, 18684, 18776, 18868, 18960,
    19052, 19144, 19236, 19328, 19420, 19512, 19604, 19696, 19788, 19880, 19972, 20064,
    20156, 20248, 20432, 20616, 20800, 20984, 21168, 21352, 21536, 21720, 21904, 22088,
    22272, 22456, 22640, 22824, 23008, 23192, 23376, 23560, 23744, 23928, 24112, 24480,
    24848, 25216, 25584, 25952, 26320, 26688, 27056, 27424, 27792, 28160, 28528, 28896,
    29264, 29632, 30000, 30368, 30736, 31104, 31472, 31840, 32208, 32576, 32944, 33312,
    33680, 34048, 34416, 34784, 35152, 35520, 35888, 36256, 36624, 36992, 37360, 37728,
    38096, 38464, 38832, 39200, 39384, 39568, 39752, 39936]

set_option maxHeartbeats 8000000
set_option maxRecDepth 200000

private theorem interval001 : gridBound 16384 16407 := by decide +kernel
private theorem interval002 : gridBound 16407 16430 := by decide +kernel
private theorem interval003 : gridBound 16430 16453 := by decide +kernel
private theorem interval004 : gridBound 16453 16476 := by decide +kernel
private theorem interval005 : gridBound 16476 16499 := by decide +kernel
private theorem interval006 : gridBound 16499 16522 := by decide +kernel
private theorem interval007 : gridBound 16522 16545 := by decide +kernel
private theorem interval008 : gridBound 16545 16568 := by decide +kernel
private theorem interval009 : gridBound 16568 16591 := by decide +kernel
private theorem interval010 : gridBound 16591 16614 := by decide +kernel
private theorem interval011 : gridBound 16614 16637 := by decide +kernel
private theorem interval012 : gridBound 16637 16660 := by decide +kernel
private theorem interval013 : gridBound 16660 16683 := by decide +kernel
private theorem interval014 : gridBound 16683 16706 := by decide +kernel
private theorem interval015 : gridBound 16706 16729 := by decide +kernel
private theorem interval016 : gridBound 16729 16752 := by decide +kernel
private theorem interval017 : gridBound 16752 16775 := by decide +kernel
private theorem interval018 : gridBound 16775 16798 := by decide +kernel
private theorem interval019 : gridBound 16798 16821 := by decide +kernel
private theorem interval020 : gridBound 16821 16844 := by decide +kernel
private theorem interval021 : gridBound 16844 16867 := by decide +kernel
private theorem interval022 : gridBound 16867 16890 := by decide +kernel
private theorem interval023 : gridBound 16890 16913 := by decide +kernel
private theorem interval024 : gridBound 16913 16936 := by decide +kernel
private theorem interval025 : gridBound 16936 16959 := by decide +kernel
private theorem interval026 : gridBound 16959 16982 := by decide +kernel
private theorem interval027 : gridBound 16982 17028 := by decide +kernel
private theorem interval028 : gridBound 17028 17074 := by decide +kernel
private theorem interval029 : gridBound 17074 17120 := by decide +kernel
private theorem interval030 : gridBound 17120 17166 := by decide +kernel
private theorem interval031 : gridBound 17166 17212 := by decide +kernel
private theorem interval032 : gridBound 17212 17258 := by decide +kernel
private theorem interval033 : gridBound 17258 17304 := by decide +kernel
private theorem interval034 : gridBound 17304 17350 := by decide +kernel
private theorem interval035 : gridBound 17350 17396 := by decide +kernel
private theorem interval036 : gridBound 17396 17442 := by decide +kernel
private theorem interval037 : gridBound 17442 17488 := by decide +kernel
private theorem interval038 : gridBound 17488 17534 := by decide +kernel
private theorem interval039 : gridBound 17534 17580 := by decide +kernel
private theorem interval040 : gridBound 17580 17626 := by decide +kernel
private theorem interval041 : gridBound 17626 17672 := by decide +kernel
private theorem interval042 : gridBound 17672 17718 := by decide +kernel
private theorem interval043 : gridBound 17718 17764 := by decide +kernel
private theorem interval044 : gridBound 17764 17810 := by decide +kernel
private theorem interval045 : gridBound 17810 17856 := by decide +kernel
private theorem interval046 : gridBound 17856 17902 := by decide +kernel
private theorem interval047 : gridBound 17902 17948 := by decide +kernel
private theorem interval048 : gridBound 17948 17994 := by decide +kernel
private theorem interval049 : gridBound 17994 18040 := by decide +kernel
private theorem interval050 : gridBound 18040 18086 := by decide +kernel
private theorem interval051 : gridBound 18086 18132 := by decide +kernel
private theorem interval052 : gridBound 18132 18224 := by decide +kernel
private theorem interval053 : gridBound 18224 18316 := by decide +kernel
private theorem interval054 : gridBound 18316 18408 := by decide +kernel
private theorem interval055 : gridBound 18408 18500 := by decide +kernel
private theorem interval056 : gridBound 18500 18592 := by decide +kernel
private theorem interval057 : gridBound 18592 18684 := by decide +kernel
private theorem interval058 : gridBound 18684 18776 := by decide +kernel
private theorem interval059 : gridBound 18776 18868 := by decide +kernel
private theorem interval060 : gridBound 18868 18960 := by decide +kernel
private theorem interval061 : gridBound 18960 19052 := by decide +kernel
private theorem interval062 : gridBound 19052 19144 := by decide +kernel
private theorem interval063 : gridBound 19144 19236 := by decide +kernel
private theorem interval064 : gridBound 19236 19328 := by decide +kernel
private theorem interval065 : gridBound 19328 19420 := by decide +kernel
private theorem interval066 : gridBound 19420 19512 := by decide +kernel
private theorem interval067 : gridBound 19512 19604 := by decide +kernel
private theorem interval068 : gridBound 19604 19696 := by decide +kernel
private theorem interval069 : gridBound 19696 19788 := by decide +kernel
private theorem interval070 : gridBound 19788 19880 := by decide +kernel
private theorem interval071 : gridBound 19880 19972 := by decide +kernel
private theorem interval072 : gridBound 19972 20064 := by decide +kernel
private theorem interval073 : gridBound 20064 20156 := by decide +kernel
private theorem interval074 : gridBound 20156 20248 := by decide +kernel
private theorem interval075 : gridBound 20248 20432 := by decide +kernel
private theorem interval076 : gridBound 20432 20616 := by decide +kernel
private theorem interval077 : gridBound 20616 20800 := by decide +kernel
private theorem interval078 : gridBound 20800 20984 := by decide +kernel
private theorem interval079 : gridBound 20984 21168 := by decide +kernel
private theorem interval080 : gridBound 21168 21352 := by decide +kernel
private theorem interval081 : gridBound 21352 21536 := by decide +kernel
private theorem interval082 : gridBound 21536 21720 := by decide +kernel
private theorem interval083 : gridBound 21720 21904 := by decide +kernel
private theorem interval084 : gridBound 21904 22088 := by decide +kernel
private theorem interval085 : gridBound 22088 22272 := by decide +kernel
private theorem interval086 : gridBound 22272 22456 := by decide +kernel
private theorem interval087 : gridBound 22456 22640 := by decide +kernel
private theorem interval088 : gridBound 22640 22824 := by decide +kernel
private theorem interval089 : gridBound 22824 23008 := by decide +kernel
private theorem interval090 : gridBound 23008 23192 := by decide +kernel
private theorem interval091 : gridBound 23192 23376 := by decide +kernel
private theorem interval092 : gridBound 23376 23560 := by decide +kernel
private theorem interval093 : gridBound 23560 23744 := by decide +kernel
private theorem interval094 : gridBound 23744 23928 := by decide +kernel
private theorem interval095 : gridBound 23928 24112 := by decide +kernel
private theorem interval096 : gridBound 24112 24480 := by decide +kernel
private theorem interval097 : gridBound 24480 24848 := by decide +kernel
private theorem interval098 : gridBound 24848 25216 := by decide +kernel
private theorem interval099 : gridBound 25216 25584 := by decide +kernel
private theorem interval100 : gridBound 25584 25952 := by decide +kernel
private theorem interval101 : gridBound 25952 26320 := by decide +kernel
private theorem interval102 : gridBound 26320 26688 := by decide +kernel
private theorem interval103 : gridBound 26688 27056 := by decide +kernel
private theorem interval104 : gridBound 27056 27424 := by decide +kernel
private theorem interval105 : gridBound 27424 27792 := by decide +kernel
private theorem interval106 : gridBound 27792 28160 := by decide +kernel
private theorem interval107 : gridBound 28160 28528 := by decide +kernel
private theorem interval108 : gridBound 28528 28896 := by decide +kernel
private theorem interval109 : gridBound 28896 29264 := by decide +kernel
private theorem interval110 : gridBound 29264 29632 := by decide +kernel
private theorem interval111 : gridBound 29632 30000 := by decide +kernel
private theorem interval112 : gridBound 30000 30368 := by decide +kernel
private theorem interval113 : gridBound 30368 30736 := by decide +kernel
private theorem interval114 : gridBound 30736 31104 := by decide +kernel
private theorem interval115 : gridBound 31104 31472 := by decide +kernel
private theorem interval116 : gridBound 31472 31840 := by decide +kernel
private theorem interval117 : gridBound 31840 32208 := by decide +kernel
private theorem interval118 : gridBound 32208 32576 := by decide +kernel
private theorem interval119 : gridBound 32576 32944 := by decide +kernel
private theorem interval120 : gridBound 32944 33312 := by decide +kernel
private theorem interval121 : gridBound 33312 33680 := by decide +kernel
private theorem interval122 : gridBound 33680 34048 := by decide +kernel
private theorem interval123 : gridBound 34048 34416 := by decide +kernel
private theorem interval124 : gridBound 34416 34784 := by decide +kernel
private theorem interval125 : gridBound 34784 35152 := by decide +kernel
private theorem interval126 : gridBound 35152 35520 := by decide +kernel
private theorem interval127 : gridBound 35520 35888 := by decide +kernel
private theorem interval128 : gridBound 35888 36256 := by decide +kernel
private theorem interval129 : gridBound 36256 36624 := by decide +kernel
private theorem interval130 : gridBound 36624 36992 := by decide +kernel
private theorem interval131 : gridBound 36992 37360 := by decide +kernel
private theorem interval132 : gridBound 37360 37728 := by decide +kernel
private theorem interval133 : gridBound 37728 38096 := by decide +kernel
private theorem interval134 : gridBound 38096 38464 := by decide +kernel
private theorem interval135 : gridBound 38464 38832 := by decide +kernel
private theorem interval136 : gridBound 38832 39200 := by decide +kernel
private theorem interval137 : gridBound 39200 39384 := by decide +kernel
private theorem interval138 : gridBound 39384 39568 := by decide +kernel
private theorem interval139 : gridBound 39568 39752 := by decide +kernel
private theorem interval140 : gridBound 39752 39936 := by decide +kernel

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
