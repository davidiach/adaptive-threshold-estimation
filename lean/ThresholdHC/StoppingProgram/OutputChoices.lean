import ThresholdHC.StoppingProgram.ConeLagrange

/-! Explicit output and second-moment choices on a fixed stopping flow.
These choices justify exact elimination, including universally null states. -/

noncomputable section
open MeasureTheory
open scoped ENNReal BigOperators

namespace ThresholdHC.StoppingProgram
open ThresholdHC.Tier6 (Gap)

def withOutputs {N : ℕ} (f : Flow N) (z t : CountState N → ℝ) : Flow N :=
  ⟨f.stopWeight,f.continueWeight,z,t⟩

theorem FlowCone.withOutputs {N : ℕ} {f : Flow N} (hf : FlowCone f)
    (z t : CountState N → ℝ) (ht : ∀ s, 0 ≤ t s)
    (hz0 : z (rootState N) = 0) (ht0 : t (rootState N) = 0)
    (hcone : ∀ s, (z s)^2 ≤ f.stopWeight s*t s) : FlowCone (withOutputs f z t) :=
  ⟨hf.stop_nonneg,hf.continue_nonneg,ht,hf.root_stop,hz0,ht0,hf.terminal,hf.recursion,hcone⟩

theorem countMean_single {N : ℕ} (μ : Measure Gap) (q : ThresholdHC.Tier6.SignLaw)
    (s : CountState N) (r : ℝ) : countMean μ q (Pi.single s r) = countCoefficient μ q s*r := by
  classical
  simp [countMean,Pi.single_apply,mul_ite]

def singleOutput {N : ℕ} (f : Flow N) (s : CountState N) (z : ℝ) : Flow N :=
  withOutputs f (Pi.single s z) (Pi.single s (z^2/f.stopWeight s))

theorem singleOutput_cone {N : ℕ} (f : Flow N) (hf : FlowCone f)
    (s : CountState N) (hs : 0 < f.stopWeight s) (z : ℝ) : FlowCone (singleOutput f s z) := by
  classical
  have hsr : s ≠ rootState N := by intro h; rw [h,hf.root_stop] at hs; exact lt_irrefl _ hs
  apply hf.withOutputs
  · intro t
    by_cases ht : t = s
    · subst t; simpa using div_nonneg (sq_nonneg z) hs.le
    · simp [ht]
  · simp [Ne.symm hsr]
  · simp [Ne.symm hsr]
  · intro t
    by_cases ht : t = s
    · subst t
      simp only [Pi.single_eq_same]
      rw [mul_div_cancel₀ _ hs.ne']
    · simp [ht]

def optimizedOutput {N : ℕ} (μ : Measure Gap) (Q : FourPriors) (α : ℝ) (f : Flow N) : Flow N :=
  withOutputs f
    (fun s => α*f.stopWeight s*(countCoefficient μ Q.high s-countCoefficient μ Q.low s)/
      (2*countCoefficient μ Q.variance s))
    (fun s => α^2*f.stopWeight s*(countCoefficient μ Q.high s-countCoefficient μ Q.low s)^2/
      (4*(countCoefficient μ Q.variance s)^2))

theorem optimizedOutput_cone {N : ℕ} (μ : Measure Gap) (Q : FourPriors) (α : ℝ)
    (f : Flow N) (hf : FlowCone f) : FlowCone (optimizedOutput μ Q α f) := by
  apply hf.withOutputs
  · intro s
    exact div_nonneg (mul_nonneg (mul_nonneg (sq_nonneg _) (hf.stop_nonneg s)) (sq_nonneg _))
      (mul_nonneg (by norm_num) (sq_nonneg _))
  · simp [hf.root_stop]
  · simp [hf.root_stop]
  · intro s
    by_cases hv : countCoefficient μ Q.variance s = 0
    · simp [hv]
    · apply le_of_eq
      field_simp
      ring

theorem optimized_perspective_identity {a v d α : ℝ} (ha : 0 ≤ a) (hv : 0 ≤ v) :
    v*(α^2*a*d^2/(4*v^2))-α*d*(α*a*d/(2*v)) =
      -(α^2/4)*(ENNReal.ofReal a*perspective d v).toReal := by
  by_cases hv0 : v = 0
  · by_cases hd : d = 0 <;> simp [hv0,hd,perspective,ENNReal.toReal_mul]
  · rw [perspective_pos (lt_of_le_of_ne hv (Ne.symm hv0)),ENNReal.toReal_mul,
      ENNReal.toReal_ofReal ha,ENNReal.toReal_ofReal (div_nonneg (sq_nonneg d) hv)]
    field_simp
    ring

theorem optimizedOutput_lagrange {N : ℕ} (μ : Measure Gap) (Q : FourPriors) (α : ℝ)
    (f : Flow N) (hf : FlowCone f) (hI : flowInformation μ Q f ≠ ⊤) :
    countMean μ Q.variance (optimizedOutput μ Q α f).momentWeight-
      α*(countMean μ Q.high (optimizedOutput μ Q α f).outputWeight-
        countMean μ Q.low (optimizedOutput μ Q α f).outputWeight) =
      -(α^2/4)*(flowInformation μ Q f).toReal := by
  let T : CountState N → ℝ≥0∞ := fun s => ENNReal.ofReal (f.stopWeight s)*perspective
    (countCoefficient μ Q.high s-countCoefficient μ Q.low s) (countCoefficient μ Q.variance s)
  have hT (s : CountState N) : T s ≠ ⊤ := ne_top_of_le_ne_top hI
    (Finset.single_le_sum (fun _ _ => bot_le) (Finset.mem_univ s))
  have hi : (flowInformation μ Q f).toReal = ∑ s, (T s).toReal := ENNReal.toReal_sum (fun s _ => hT s)
  rw [hi,Finset.mul_sum]
  simp only [countMean,optimizedOutput,withOutputs,Finset.mul_sum,← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro s _
  have hh := optimized_perspective_identity (α := α)
    (d := countCoefficient μ Q.high s-countCoefficient μ Q.low s)
    (hf.stop_nonneg s) (countCoefficient_nonneg μ Q.variance s)
  change _ = -(α^2/4)*(T s).toReal at hh
  convert hh using 1
  ring

end ThresholdHC.StoppingProgram
