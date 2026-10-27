import ThresholdHC.Tier5.StoppingEntropy
import ThresholdHC.Tier5.FiniteCreation

namespace ThresholdHC.Tier5

theorem creation_kl_eq_iSup : CreationKLSupremumStatement :=
  creationKLSupremum_of_finiteKL creation_finite_kl_bound

end ThresholdHC.Tier5
