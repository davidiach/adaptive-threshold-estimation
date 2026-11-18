import LargeBudgetPrice
import RevisitPolynomial

/-! Constants of the finite testing problem. The sign mean is t in [-1,1],
and its squared-error scale is four times the population-fraction scale. -/
noncomputable section
namespace ThresholdHC.SharpRMS.MultiBias
open Real

abbrev radius : ℝ := 175198/1000000
abbrev target : ℝ := 4*radius^2
abbrev tilt : ℝ := 19780099/1000000

def bias : Fin 5 → ℝ := ![527436/1000000,679980/1000000,753283/1000000,798023/1000000,816490/1000000]
def slope : Fin 5 → ℝ := ![6121167/1000000,7070320/1000000,7599955/1000000,7966557/1000000,8119407/1000000]

theorem params (i : Fin 5) : 0<bias i ∧ (bias i)^2≤2/3 ∧ 0<slope i ∧ slope i*target<1 := by
  fin_cases i <;> norm_num [bias,slope]

def cut (i : Fin 5) := 1-4*(bias i)^2/25

theorem cut_pos (i : Fin 5) : 0<cut i := by
  unfold cut; linarith [(params i).2.1]

def test (i : Fin 5) (t x : ℝ) := 1+slope i*((x-t)^2-target)

theorem test_pos (i : Fin 5) (t x : ℝ) : 0<test i t x := by
  unfold test
  nlinarith only [(params i).2.2.2,mul_nonneg (params i).2.2.1.le (sq_nonneg (x-t))]

def pair (i : Fin 5) (x : ℝ) := log (test i (bias i) x)+log (test i (-bias i) x)

def quad (i : Fin 5) (y : ℝ) := (1+slope i*(y+(bias i)^2-target))^2-4*(slope i*bias i)^2*y

theorem quad_eq (i : Fin 5) (x : ℝ) :
    quad i (x^2)=test i (bias i) x*test i (-bias i) x := by unfold quad test; ring

end ThresholdHC.SharpRMS.MultiBias
