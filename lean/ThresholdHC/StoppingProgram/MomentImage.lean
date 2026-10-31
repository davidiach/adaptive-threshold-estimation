import ThresholdHC.CapIdentification.MomentCoordinates
import ThresholdHC.CapIdentification.TerminalMoments

/-! Compact convex images of actual rare priors under the target and all
finite-depth count coefficients. -/

noncomputable section
open MeasureTheory Polynomial Set
open scoped BigOperators

namespace ThresholdHC.StoppingProgram
open ThresholdHC.Tier6 (Gap SignLaw signMean)
open ThresholdHC.RareAboveTwo ThresholdHC.CapIdentification

def countContrastPolynomial {N : ℕ} (s : CountState N) : ℝ[X] :=
  (s.1.val.choose s.2.val:ℝ) •
    ((prefixPolynomial s.1.val s.2.val).comp (C (1/2)+X)-
      (prefixPolynomial s.1.val s.2.val).comp (C (1/2)-X))

theorem countContrastPolynomial_eval {N : ℕ} (s : CountState N) (d : Gap) :
    (countContrastPolynomial s).eval (d:ℝ) =
      (s.1.val.choose s.2.val:ℝ)*
        (prefixLikelihood true s.1.val s.2.val d-prefixLikelihood false s.1.val s.2.val d) := by
  simp only [countContrastPolynomial,eval_smul,eval_sub,eval_comp,eval_add,eval_C,eval_X,
    prefixPolynomial_eval_plus,prefixPolynomial_eval_minus,smul_eq_mul]

theorem countCoefficient_affine {N : ℕ} (μ : Measure Gap) [IsFiniteMeasure μ]
    (q : SignLaw) (s : CountState N) :
    countCoefficient μ q s = (∫ d, q.val d*(countContrastPolynomial s).eval (d:ℝ) ∂μ)+
      countCoefficient μ nullSignLaw s := by
  have hh := countCoefficient_difference μ q nullSignLaw s
  rw [signContrast_apply] at hh
  simp only [nullSignLaw,sub_zero,prefixPolynomial_eval_plus,prefixPolynomial_eval_minus] at hh
  rw [← integral_sub (integrable_weighted_prefix μ q true _ _) (integrable_weighted_prefix μ q false _ _),
    ← integral_const_mul] at hh
  have he : (∫ d, (s.1.val.choose s.2.val:ℝ)*
      (q.val d*prefixLikelihood true s.1.val s.2.val d-q.val d*prefixLikelihood false s.1.val s.2.val d) ∂μ) =
      ∫ d, q.val d*(countContrastPolynomial s).eval (d:ℝ) ∂μ := by
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun d => by
      dsimp only
      rw [countContrastPolynomial_eval]
      ring)
  rw [he] at hh
  change countCoefficient μ q s-countCoefficient μ nullSignLaw s = _ at hh
  linarith

def priorCoordinates (N : ℕ) (μ : Measure Gap) (q : SignLaw) : Option (CountState N) → ℝ
  | none => signMean μ q.val
  | some s => countCoefficient μ q s

def priorMomentImage (N : ℕ) (μ : Measure Gap) (ρ : ℝ) : Set (Option (CountState N) → ℝ) :=
  {u | ∃ q : SignLaw, RarePrior μ ρ q ∧ u = priorCoordinates N μ q}

theorem priorMomentImage_compact_convex (N : ℕ) (μ : Measure Gap) [IsProbabilityMeasure μ] (ρ : ℝ) :
    IsCompact (priorMomentImage N μ ρ) ∧ Convex ℝ (priorMomentImage N μ ρ) := by
  let P : Option (CountState N) → ℝ[X] := fun i => match i with
    | none => 1
    | some s => countContrastPolynomial s
  let b : Option (CountState N) → ℝ := fun i => match i with
    | none => 0
    | some s => countCoefficient μ nullSignLaw s
  have he (q : SignLaw) (i : Option (CountState N)) :
      priorCoordinates N μ q i = (∫ d, q.val d*polynomialL2 μ (P i) d ∂μ)+b i := by
    have hint : (∫ d, q.val d*polynomialL2 μ (P i) d ∂μ) =
        ∫ d, q.val d*(P i).eval (d:ℝ) ∂μ := by
      apply integral_congr_ae
      filter_upwards [polynomialL2_ae μ (P i)] with d hd
      rw [hd]
    rw [hint]
    cases i with
    | none => simp [P,b,priorCoordinates,signMean]
    | some s => exact countCoefficient_affine μ q s
  have heq : priorMomentImage N μ ρ = rareMomentSet μ ρ (fun i => polynomialL2 μ (P i)) b := by
    ext u
    simp only [priorMomentImage,rareMomentSet,funext_iff,he]
  rw [heq]
  exact rareMomentSet_compact_convex μ ρ _ _

theorem priorMomentImage_nonempty (N : ℕ) (μ : Measure Gap) {ρ : ℝ} (hρ : 0 ≤ ρ) :
    (priorMomentImage N μ ρ).Nonempty := by
  refine ⟨priorCoordinates N μ nullSignLaw,nullSignLaw,?_,rfl⟩
  simpa [RarePrior,signMean,nullSignLaw] using hρ

theorem priorMomentImage_mem (N : ℕ) (μ : Measure Gap) (ρ : ℝ) (q : SignLaw)
    (hq : RarePrior μ ρ q) : priorCoordinates N μ q ∈ priorMomentImage N μ ρ := ⟨q,hq,rfl⟩

end ThresholdHC.StoppingProgram
