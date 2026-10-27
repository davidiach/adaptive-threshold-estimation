import ThresholdHC.CriticalEntropy.GoodGapModel

/-! The fixed quadratic gap law, its separated annuli, and the observation parameter.
These definitions contain no estimator guarantee or information inequality. -/

noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace ThresholdHC.CriticalEntropy

/-- The probability density is 32d on (0,1/4], giving F(d)=16d². -/
def criticalGapLaw : Measure ℝ :=
  (volume.restrict (Ioc (0 : ℝ) (1/4))).withDensity (fun d => ENNReal.ofReal (32*d))

def criticalUpper (j : ℕ) : ℝ := (1/4 : ℝ)/(4 : ℝ)^j

def criticalAnnulus (j : ℕ) : Set ℝ := Ioc (criticalUpper j/2) (criticalUpper j)

/-- Clip only to define the parameter on all real inputs; the support lies inside
the interval where it equals 1/2 ± d. -/
def criticalParameter (d : ℝ) (b : Bool) : unitInterval :=
  projIcc 0 1 (by norm_num) (1/2+(if b then d else -d))

end ThresholdHC.CriticalEntropy
