import ThresholdHC.StoppingProgram.NullPruning
import ThresholdHC.CapIdentification.CountBounds

/-! Finite coordinate bounds for null-pruned feasible objective sublevels.
They use only the root charge and a strictly interior constant prior. -/

noncomputable section
open MeasureTheory
open scoped BigOperators

namespace ThresholdHC.StoppingProgram
open ThresholdHC.Tier6 (Gap signMean)
open ThresholdHC.RareAboveTwo ThresholdHC.CapIdentification

theorem abs_le_square_bound {x M : ℝ} (_hM : 0 ≤ M) (hx : x^2 ≤ M) : |x| ≤ M+1 := by
  apply abs_le.mpr
  constructor <;> nlinarith [sq_nonneg (x-1/2),sq_nonneg (x+1/2)]

def momentCoordinateBound {N : ℕ} (μ : Measure Gap) (q : ThresholdHC.Tier6.SignLaw) (M : ℝ)
    (s : CountState N) : ℝ := M/countCoefficient μ q s

def outputCoordinateBound {N : ℕ} (μ : Measure Gap) (q : ThresholdHC.Tier6.SignLaw) (B M : ℝ)
    (s : CountState N) : ℝ := B*momentCoordinateBound μ q M s+1

def offsetCoordinateBound (N : ℕ) (μ : Measure Gap) (q : ThresholdHC.Tier6.SignLaw) (B M : ℝ) : ℝ :=
  M+1+∑ s : CountState N, countCoefficient μ nullSignLaw s*outputCoordinateBound μ q B M s

theorem feasible_sublevel_bounds {N : ℕ} (μ : Measure Gap) [IsProbabilityMeasure μ]
    {ρ B M : ℝ} (hρ : 0 < ρ) (hρhalf : ρ ≤ 1/2) (hB : 0 ≤ B) (hM : 0 ≤ M)
    (C : Certificate N) (hC : Feasible μ ρ B C) (hobj : C.bias^2+C.variance ≤ M)
    (hprune : NullPruned μ (constantPrior ρ ⟨hρ.le,by linarith⟩) C) :
    C.bias ≤ M+1 ∧ C.variance ≤ M ∧
    (∀ s, C.flow.stopWeight s ≤ B ∧ C.flow.continueWeight s ≤ B ∧
      C.flow.momentWeight s ≤ momentCoordinateBound μ (constantPrior ρ ⟨hρ.le,by linarith⟩) M s ∧
      |C.flow.outputWeight s| ≤ outputCoordinateBound μ (constantPrior ρ ⟨hρ.le,by linarith⟩) B M s) ∧
    |C.offset| ≤ offsetCoordinateBound N μ (constantPrior ρ ⟨hρ.le,by linarith⟩) B M := by
  let q := constantPrior ρ ⟨hρ.le,by linarith⟩
  have hq : RarePrior μ ρ q := le_of_eq (constantPrior_mean μ _ _)
  have hb : C.bias ≤ M+1 := by
    have hh := abs_le_square_bound hM (show C.bias^2 ≤ M by linarith [hC.variance_nonneg])
    exact (le_abs_self C.bias).trans hh
  have hv : C.variance ≤ M := by nlinarith [sq_nonneg C.bias]
  have hi : intensity C.flow ≤ B := (flow_work_ge_intensity μ q C.flow hC.cone).trans (hC.work_bound q hq)
  have hstop (s : CountState N) : C.flow.stopWeight s ≤ B := (flow_stop_le_intensity C.flow hC.cone s).trans hi
  have hcont (s : CountState N) : C.flow.continueWeight s ≤ B := (flow_continue_le_intensity C.flow hC.cone s).trans hi
  have hmoment (s : CountState N) : C.flow.momentWeight s ≤ momentCoordinateBound μ q M s := by
    by_cases hs : countCoefficient μ q s = 0
    · have hz := (hprune s hs).2
      simp [momentCoordinateBound,hs,hz]
    have hs' : 0 < countCoefficient μ q s := lt_of_le_of_ne (countCoefficient_nonneg μ q s) (Ne.symm hs)
    have hh : countCoefficient μ q s*C.flow.momentWeight s ≤ countMean μ q C.flow.momentWeight :=
      Finset.single_le_sum (fun t _ => mul_nonneg (countCoefficient_nonneg μ q t) (hC.cone.moment_nonneg t)) (Finset.mem_univ s)
    apply (le_div_iff₀ hs').mpr
    nlinarith [hC.variance_bound q hq]
  have houtput (s : CountState N) : |C.flow.outputWeight s| ≤ outputCoordinateBound μ q B M s := by
    apply abs_le_square_bound (mul_nonneg hB (div_nonneg hM (countCoefficient_nonneg μ q s)))
    exact (hC.cone.perspective s).trans
      (mul_le_mul (hstop s) (hmoment s) (hC.cone.moment_nonneg s) hB)
  refine ⟨hb,hv,fun s => ⟨hstop s,hcont s,hmoment s,houtput s⟩,?_⟩
  have hnull : RarePrior μ ρ nullSignLaw := by simpa [RarePrior,signMean,nullSignLaw] using hρ.le
  have hmean : |countMean μ nullSignLaw C.flow.outputWeight| ≤
      ∑ s : CountState N, countCoefficient μ nullSignLaw s*outputCoordinateBound μ q B M s := by
    calc
      |countMean μ nullSignLaw C.flow.outputWeight| ≤
          ∑ s, |countCoefficient μ nullSignLaw s*C.flow.outputWeight s| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro s _
        rw [abs_mul,abs_of_nonneg (countCoefficient_nonneg μ nullSignLaw s)]
        exact mul_le_mul_of_nonneg_left (houtput s) (countCoefficient_nonneg μ nullSignLaw s)
  have hbias := hC.bias_bound nullSignLaw hnull
  simp only [signMean,nullSignLaw,integral_zero,sub_zero] at hbias
  change |C.offset+countMean μ nullSignLaw C.flow.outputWeight| ≤ C.bias at hbias
  have htri := abs_add_le (C.offset+countMean μ nullSignLaw C.flow.outputWeight)
    (-countMean μ nullSignLaw C.flow.outputWeight)
  rw [add_neg_cancel_right,abs_neg] at htri
  change |C.offset| ≤ M+1+∑ s : CountState N, countCoefficient μ nullSignLaw s*outputCoordinateBound μ q B M s
  linarith

end ThresholdHC.StoppingProgram
