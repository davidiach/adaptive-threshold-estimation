import ThresholdHC.StoppingProgram.Perspective
import ThresholdHC.RareAboveTwo.Model

/-! The paper's robust stopping-flow program. These are definitions of the
actual finite conic program and four-prior information ratio, not assumptions
of strong duality or of statistical realization. Root activation is charged. -/

noncomputable section
open MeasureTheory Real
open scoped ENNReal BigOperators

namespace ThresholdHC.StoppingProgram
open ThresholdHC.Tier6 ThresholdHC.RareAboveTwo

abbrev CountState (N : ℕ) := (n : Fin (N+1)) × Fin (n.val+1)

def rootState (N : ℕ) : CountState N := ⟨⟨0,by omega⟩,⟨0,by omega⟩⟩

def arrayAt {N : ℕ} (u : CountState N → ℝ) (n k : ℕ) : ℝ :=
  if hn : n ≤ N then if hk : k ≤ n then
    u ⟨⟨n,by omega⟩,⟨k,by change k < n+1; omega⟩⟩ else 0 else 0

def prefixLikelihood (s : Bool) (n k : ℕ) (d : Gap) : ℝ :=
  if s then (1/2+(d:ℝ))^k*(1/2-(d:ℝ))^(n-k)
  else (1/2-(d:ℝ))^k*(1/2+(d:ℝ))^(n-k)

def countCoefficient {N : ℕ} (μ : Measure Gap) (q : SignLaw) (s : CountState N) : ℝ :=
  (s.1.val.choose s.2.val:ℝ)*∫ d : Gap,
    q.val d*prefixLikelihood true s.1.val s.2.val d+
      (1-q.val d)*prefixLikelihood false s.1.val s.2.val d ∂μ

def countMean {N : ℕ} (μ : Measure Gap) (q : SignLaw) (u : CountState N → ℝ) : ℝ :=
  ∑ s, countCoefficient μ q s*u s

structure Flow (N : ℕ) where
  stopWeight : CountState N → ℝ
  continueWeight : CountState N → ℝ
  outputWeight : CountState N → ℝ
  momentWeight : CountState N → ℝ

def intensity {N : ℕ} (f : Flow N) : ℝ := f.continueWeight (rootState N)

structure FlowCone {N : ℕ} (f : Flow N) : Prop where
  stop_nonneg : ∀ s, 0 ≤ f.stopWeight s
  continue_nonneg : ∀ s, 0 ≤ f.continueWeight s
  moment_nonneg : ∀ s, 0 ≤ f.momentWeight s
  root_stop : f.stopWeight (rootState N) = 0
  root_output : f.outputWeight (rootState N) = 0
  root_moment : f.momentWeight (rootState N) = 0
  terminal : ∀ s, s.1.val = N → f.continueWeight s = 0
  recursion : ∀ s, 0 < s.1.val →
    f.stopWeight s+f.continueWeight s =
      ((s.1.val-s.2.val:ℕ):ℝ)/s.1.val*arrayAt f.continueWeight (s.1.val-1) s.2.val+
      (s.2.val:ℝ)/s.1.val*arrayAt f.continueWeight (s.1.val-1) (s.2.val-1)
  perspective : ∀ s, (f.outputWeight s)^2 ≤ f.stopWeight s*f.momentWeight s

structure Certificate (N : ℕ) where
  flow : Flow N
  offset : ℝ
  bias : ℝ
  variance : ℝ

structure Feasible {N : ℕ} (μ : Measure Gap) (ρ B : ℝ) (C : Certificate N) : Prop where
  cone : FlowCone C.flow
  bias_nonneg : 0 ≤ C.bias
  variance_nonneg : 0 ≤ C.variance
  bias_bound : ∀ q : SignLaw, RarePrior μ ρ q →
    |C.offset+countMean μ q C.flow.outputWeight-signMean μ q.val| ≤ C.bias
  variance_bound : ∀ q : SignLaw, RarePrior μ ρ q → countMean μ q C.flow.momentWeight ≤ C.variance
  work_bound : ∀ q : SignLaw, RarePrior μ ρ q → countMean μ q C.flow.continueWeight ≤ B

def certificateSquared {N : ℕ} (C : Certificate N) : ℝ≥0∞ := ENNReal.ofReal (C.bias^2+C.variance)

def programSquared (μ : Measure Gap) (ρ B : ℝ) (N : ℕ) : ℝ≥0∞ :=
  sInf {x | ∃ C : Certificate N, Feasible μ ρ B C ∧ x = certificateSquared C}

def programValue (μ : Measure Gap) (ρ B : ℝ) (N : ℕ) : ℝ≥0∞ := programSquared μ ρ B N ^ (1/(2:ℝ))

structure FourPriors where
  low : SignLaw
  high : SignLaw
  variance : SignLaw
  work : SignLaw

def Admissible (μ : Measure Gap) (ρ : ℝ) (Q : FourPriors) : Prop :=
  RarePrior μ ρ Q.low ∧ RarePrior μ ρ Q.high ∧ RarePrior μ ρ Q.variance ∧ RarePrior μ ρ Q.work

def flowInformation {N : ℕ} (μ : Measure Gap) (Q : FourPriors) (f : Flow N) : ℝ≥0∞ :=
  ∑ s, ENNReal.ofReal (f.stopWeight s)*perspective
    (countCoefficient μ Q.high s-countCoefficient μ Q.low s) (countCoefficient μ Q.variance s)

def informationRatio (μ : Measure Gap) (N : ℕ) (Q : FourPriors) : ℝ≥0∞ :=
  ⨆ (f : Flow N) (_ : FlowCone f) (_ : intensity f = 1),
    flowInformation μ Q f/ENNReal.ofReal (countMean μ Q.work f.continueWeight)

def dualRatio (μ : Measure Gap) (B : ℝ) (N : ℕ) (Q : FourPriors) : ℝ≥0∞ :=
  (ENNReal.ofReal (signMean μ Q.high.val-signMean μ Q.low.val))^2/
    (4+ENNReal.ofReal B*informationRatio μ N Q)

def dualValue (μ : Measure Gap) (ρ B : ℝ) (N : ℕ) : ℝ≥0∞ :=
  ⨆ (Q : FourPriors) (_ : Admissible μ ρ Q), dualRatio μ B N Q

end ThresholdHC.StoppingProgram
