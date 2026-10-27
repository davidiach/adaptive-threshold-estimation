import ThresholdHC.Tier3.Specification
import ThresholdHC.Tier3.Randomized
import ThresholdHC.Tier3.Stopping
import ThresholdHC.Tier3.Optimizer
import ThresholdHC.Tier3.Examples

/-!
The complete Tier 3 landmark. Each component has exactly its locked statement
type; the concrete example rules out a merely bounded-horizon instantiation.
-/
namespace ThresholdHC.Tier3

theorem tier3_landmark : Tier3LandmarkStatement :=
  ⟨randomized_law_total, randomized_information_bound,
    randomized_marginal_kl_bound, randomized_testing_bound,
    finite_work_stops, unbounded_stopping, unbounded_testing,
    arbitrary_law_cutoff, arbitrary_law_optimizer, unbounded_example⟩

end ThresholdHC.Tier3
