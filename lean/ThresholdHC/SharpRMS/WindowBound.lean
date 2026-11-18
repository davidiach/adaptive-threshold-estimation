import ThresholdHC.SharpRMS.GridArithmetic

/-! Integer upper sums on the intermediate bias window: the bound checked on
each bias interval, the chain of adjacent intervals and its 140 endpoints.
The closed comparisons are in the WindowPart modules. -/
namespace ThresholdHC.SharpRMS.Window

/-- After multiplying by (hi/lo)^2, the scaled upper sum is at most 2/3. -/
def gridBound (lo hi : Nat) : Prop :=
  0 < lo ∧ lo ≤ hi ∧ 3*hi^2*upperSum hi ≤ 2*lo^2*bins*scale

instance decidableGridBound (lo hi : Nat) : Decidable (gridBound lo hi) := inferInstanceAs
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

end ThresholdHC.SharpRMS.Window
