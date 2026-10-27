import ThresholdHC.Tier4.Model

namespace ThresholdHC.Tier4

def Tier4LandmarkStatement : Prop :=
  FinitePrefixKLStatement ∧ InfiniteKLSupremumStatement ∧ InfiniteKLBoundStatement ∧
    InfiniteKLFiniteStatement ∧ ObservableKLBoundStatement

end ThresholdHC.Tier4
