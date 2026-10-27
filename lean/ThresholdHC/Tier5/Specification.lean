import ThresholdHC.Tier5.Model

namespace ThresholdHC.Tier5

def Tier5LandmarkStatement : Prop :=
  CreationTotalStatement ∧ CreationConsistencyStatement ∧ CreationFiniteKLStatement ∧
    CreationStopsStatement ∧ CreationKLSupremumStatement ∧ CreationInfiniteKLStatement ∧
    CreationObservableKLStatement ∧ UnboundedCreationExampleStatement

end ThresholdHC.Tier5
