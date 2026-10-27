import ThresholdHC.CriticalEntropy.PopulationModel
import ThresholdHC.CriticalEntropy.RepeatedModel

noncomputable section
open MeasureTheory ProbabilityTheory Set Real
open scoped ENNReal
namespace ThresholdHC.CriticalEntropy

/-- Seeds which request at least one observation; the canonical false tape is used
only to define this seed event. Prefix observability proves independence from flips. -/
def activeSeeds {R E : Type} [MeasurableSpace R] [MeasurableSpace E]
    (A : StoppedProcedure R E) : Set R := {r | A.stop (r,fun _ => false) ≠ 0}

def populationSeedEvent {D R : Type} (S : Set R) : Set (D × (ℝ × (R × (ℕ → ℝ)))) :=
  univ ×ˢ (univ ×ˢ (S ×ˢ univ))

/-- Under the seed law conditioned on activation, use pY+c. Both constants depend
only on the original seed law and procedure, never on the gap, sign or prior. -/
def activeProcedure {R : Type} [MeasurableSpace R] (ν : Measure R)
    (A : StoppedProcedure R ℝ) : StoppedProcedure R ℝ :=
  postprocessProcedure A
    (fun y => ν.real (activeSeeds A)*y+(∫ r in (activeSeeds A)ᶜ,A.output (r,fun _ => false) ∂ν))
    (by fun_prop)

end ThresholdHC.CriticalEntropy
