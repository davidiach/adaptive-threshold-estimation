import ThresholdHC.Tier3.StoppingModel
import Mathlib.Probability.Distributions.Geometric
import Mathlib.Probability.Distributions.Bernoulli

/-!
A concrete randomized experiment with genuinely unbounded work. Its common
seed N is geometric with success probability one half. It queries a single
deterministic-given-sign coin N+1 times. Every finite work cap is exceeded with
positive probability, while expected work is finite. The sign prior is arbitrary.
-/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace ThresholdHC.Tier3

def exampleSeedLaw : Measure ℕ := geometricMeasure ⟨1/2, by constructor <;> norm_num⟩

def exampleProcessLaw (q : unitInterval) : Measure (ℕ × Bool) :=
  exampleSeedLaw.prod (bernoulliMeasure true false q)

def examplePolicy (N : ℕ) (history : List Bool) : Option (Fin 1) :=
  if history.length < N+1 then some 0 else none

def exampleTape (ω : ℕ × Bool) : ProcessTape :=
  fun k => if k < ω.1+1 then some ω.2 else none

def UnboundedExampleStatement : Prop :=
  MeasurablePolicy examplePolicy ∧
  ∀ q : unitInterval,
    RealizesPrefixes exampleSeedLaw (exampleProcessLaw q) Prod.fst exampleTape
      examplePolicy (fun _ => 1/2) (fun _ => (q : ℝ)) ∧
    (∀ ω : ℕ × Bool, totalProcessWork (exampleTape ω) = (ω.1+1 : ℕ)) ∧
    (∫⁻ ω, totalProcessWork (exampleTape ω) ∂exampleProcessLaw q) < ∞ ∧
    ∀ n : ℕ, 0 < exampleProcessLaw q {ω | (n : ℝ≥0∞) < totalProcessWork (exampleTape ω)}

end ThresholdHC.Tier3
