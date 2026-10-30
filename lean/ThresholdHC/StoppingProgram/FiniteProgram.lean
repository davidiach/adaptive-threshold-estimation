import ThresholdHC.StoppingProgram.RobustRarity

/-! Exact finite-law reduction of the robust stopping program. Each of the
four prior constraints is equivalent to one cutoff and finitely many
nonnegative excess variables; no continuum constraints remain. -/

noncomputable section
open MeasureTheory Polynomial
open scoped BigOperators ENNReal

namespace ThresholdHC.StoppingProgram
open ThresholdHC.Tier6 (Gap SignLaw)
open ThresholdHC.RareAboveTwo ThresholdHC.CapIdentification

variable {I : Type*} [Fintype I]

theorem finite_law_integral (μ : Measure Gap) (w : I → ℝ) (d : I → Gap)
    (hw : ∀ i, 0 ≤ w i) (hμ : μ = ∑ i, ENNReal.ofReal (w i) • Measure.dirac (d i))
    (f : Gap → ℝ) : (∫ x, f x ∂μ) = ∑ i, w i*f (d i) := by
  rw [hμ,integral_finsetSum_measure (fun i _ =>
    (integrable_dirac (by finiteness)).smul_measure (by finiteness))]
  simp only [integral_smul_measure,integral_dirac,ENNReal.toReal_ofReal (hw _),smul_eq_mul]

theorem finite_law_tail (μ : Measure Gap) (w : I → ℝ) (d : I → Gap)
    (hw : ∀ i, 0 ≤ w i) (hμ : μ = ∑ i, ENNReal.ofReal (w i) • Measure.dirac (d i))
    (ρ : ℝ) (P : ℝ[X]) (ell : ℝ) :
    polynomialTail μ ρ P ell = ρ*ell+∑ i, w i*max (P.eval (d i:ℝ)-ell) 0 := by
  rw [polynomialTail,finite_law_integral μ w d hw hμ]

def FiniteTailBound (w : I → ℝ) (d : I → Gap) (ρ : ℝ) (P : ℝ[X]) (z : ℝ) : Prop :=
  ∃ (ell : ℝ) (u : I → ℝ), 0 ≤ ell ∧ (∀ i, 0 ≤ u i ∧ P.eval (d i:ℝ)-ell ≤ u i) ∧
    ρ*ell+∑ i, w i*u i ≤ z

theorem finiteTailBound_iff (μ : Measure Gap) (w : I → ℝ) (d : I → Gap)
    (hw : ∀ i, 0 ≤ w i) (hμ : μ = ∑ i, ENNReal.ofReal (w i) • Measure.dirac (d i))
    (ρ : ℝ) (P : ℝ[X]) (z : ℝ) :
    FiniteTailBound w d ρ P z ↔ ∃ ell, 0 ≤ ell ∧ polynomialTail μ ρ P ell ≤ z := by
  constructor
  · rintro ⟨ell,u,hell,hu,hz⟩
    refine ⟨ell,hell,?_⟩
    rw [finite_law_tail μ w d hw hμ]
    exact (add_le_add le_rfl (Finset.sum_le_sum (s := Finset.univ) (fun i _ =>
      mul_le_mul_of_nonneg_left (max_le (hu i).2 (hu i).1) (hw i)))).trans hz
  · rintro ⟨ell,hell,hz⟩
    exact ⟨ell,fun i => max (P.eval (d i:ℝ)-ell) 0,hell,
      fun i => ⟨le_max_right _ _,le_max_left _ _⟩,by rwa [finite_law_tail μ w d hw hμ] at hz⟩

def finiteNullMean {N : ℕ} (w : I → ℝ) (d : I → Gap) (u : CountState N → ℝ) : ℝ :=
  ∑ s, (s.1.val.choose s.2.val:ℝ)*(∑ i, w i*prefixLikelihood false s.1.val s.2.val (d i))*u s

theorem finiteNullMean_eq {N : ℕ} (μ : Measure Gap) (w : I → ℝ) (d : I → Gap)
    (hw : ∀ i, 0 ≤ w i) (hμ : μ = ∑ i, ENNReal.ofReal (w i) • Measure.dirac (d i))
    (u : CountState N → ℝ) : finiteNullMean w d u = countMean μ nullSignLaw u := by
  unfold finiteNullMean countMean countCoefficient
  simp only [nullSignLaw,zero_mul,sub_zero,one_mul,zero_add,finite_law_integral μ w d hw hμ]

theorem feasible_iff_finite_program {N : ℕ} (μ : Measure Gap) [IsProbabilityMeasure μ]
    (w : I → ℝ) (d : I → Gap) (hw : ∀ i, 0 ≤ w i)
    (hμ : μ = ∑ i, ENNReal.ofReal (w i) • Measure.dirac (d i))
    {ρ B : ℝ} (hρ : 0 < ρ) (C : Certificate N) :
    Feasible μ ρ B C ↔ FlowCone C.flow ∧ 0 ≤ C.bias ∧ 0 ≤ C.variance ∧
      FiniteTailBound w d ρ (biasPolynomial C)
        (C.bias-(C.offset+finiteNullMean w d C.flow.outputWeight)) ∧
      FiniteTailBound w d ρ (-biasPolynomial C)
        (C.bias+(C.offset+finiteNullMean w d C.flow.outputWeight)) ∧
      FiniteTailBound w d ρ (countMeanPolynomial C.flow.momentWeight)
        (C.variance-finiteNullMean w d C.flow.momentWeight) ∧
      FiniteTailBound w d ρ (countMeanPolynomial C.flow.continueWeight)
        (B-finiteNullMean w d C.flow.continueWeight) := by
  simp only [finiteTailBound_iff μ w d hw hμ,finiteNullMean_eq μ w d hw hμ]
  rw [feasible_iff_four_cutoffs μ hρ C]
  constructor
  · rintro ⟨hf,hb,hv,t,ht,h0,h1,h2,h3⟩
    exact ⟨hf,hb,hv,⟨t 0,ht 0,by linarith⟩,⟨t 1,ht 1,by linarith⟩,
      ⟨t 2,ht 2,by linarith⟩,⟨t 3,ht 3,by linarith⟩⟩
  · rintro ⟨hf,hb,hv,⟨t0,h0,ht0⟩,⟨t1,h1,ht1⟩,⟨t2,h2,ht2⟩,⟨t3,h3,ht3⟩⟩
    refine ⟨hf,hb,hv,![t0,t1,t2,t3],?_,?_,?_,?_,?_⟩
    · intro i; fin_cases i <;> assumption
    · change C.offset+countMean μ nullSignLaw C.flow.outputWeight+polynomialTail μ ρ (biasPolynomial C) t0 ≤ C.bias
      linarith
    · change -(C.offset+countMean μ nullSignLaw C.flow.outputWeight)+polynomialTail μ ρ (-biasPolynomial C) t1 ≤ C.bias
      linarith
    · change countMean μ nullSignLaw C.flow.momentWeight+polynomialTail μ ρ (countMeanPolynomial C.flow.momentWeight) t2 ≤ C.variance
      linarith
    · change countMean μ nullSignLaw C.flow.continueWeight+polynomialTail μ ρ (countMeanPolynomial C.flow.continueWeight) t3 ≤ B
      linarith

end ThresholdHC.StoppingProgram
