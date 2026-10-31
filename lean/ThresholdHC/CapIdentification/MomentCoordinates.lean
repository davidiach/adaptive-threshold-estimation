import ThresholdHC.CapIdentification.PolynomialL2
import ThresholdHC.CapIdentification.CountMatching
import ThresholdHC.StoppingProgram.RareCompactness

/-! The target and finite list of odd moments form a compact convex image
of the original globally rare sign-prior class. -/

noncomputable section
open MeasureTheory Polynomial Set

namespace ThresholdHC.CapIdentification
open ThresholdHC.Tier6 (Gap SignLaw signMean)
open ThresholdHC.StoppingProgram ThresholdHC.RareAboveTwo

theorem integrable_sign_polynomial (μ : Measure Gap) [IsFiniteMeasure μ] (q : SignLaw) (P : ℝ[X]) :
    Integrable (fun d => q.val d*P.eval (d:ℝ)) μ := by
  apply ((polynomial_gap_memLp μ P).integrable (by norm_num)).bdd_mul q.property.1.aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun d => by
    simpa only [Real.norm_eq_abs,abs_of_nonneg (q.property.2 d).1] using (q.property.2 d).2)

theorem polynomial_moment_difference (μ : Measure Gap) [IsFiniteMeasure μ]
    (qH qL : SignLaw) (P : ℝ[X]) :
    (∫ d, (qH.val d-qL.val d)*P.eval (d:ℝ) ∂μ) =
      (∫ d, qH.val d*P.eval (d:ℝ) ∂μ)-(∫ d, qL.val d*P.eval (d:ℝ) ∂μ) := by
  simp_rw [sub_mul]
  exact integral_sub (integrable_sign_polynomial μ qH P) (integrable_sign_polynomial μ qL P)

def polynomialMomentSet {I : Type} (μ : Measure Gap) (ρ : ℝ) (P : I → ℝ[X]) : Set (I → ℝ) :=
  {v | ∃ q : SignLaw, RarePrior μ ρ q ∧ ∀ i, v i = ∫ d, q.val d*(P i).eval (d:ℝ) ∂μ}

theorem polynomialMomentSet_eq_rareMomentSet {I : Type} (μ : Measure Gap) [IsFiniteMeasure μ]
    (ρ : ℝ) (P : I → ℝ[X]) :
    polynomialMomentSet μ ρ P = rareMomentSet μ ρ (fun i => polynomialL2 μ (P i)) (fun _ => 0) := by
  have he (q : SignLaw) (i : I) : (∫ d, q.val d*(P i).eval (d:ℝ) ∂μ) =
      (∫ d, q.val d*polynomialL2 μ (P i) d ∂μ)+0 := by
    rw [add_zero]
    apply integral_congr_ae
    filter_upwards [polynomialL2_ae μ (P i)] with d hd
    rw [hd]
  simp only [polynomialMomentSet,rareMomentSet,he]

theorem polynomialMomentSet_compact_convex {I : Type} (μ : Measure Gap) [IsProbabilityMeasure μ]
    (ρ : ℝ) (P : I → ℝ[X]) :
    IsCompact (polynomialMomentSet μ ρ P) ∧ Convex ℝ (polynomialMomentSet μ ρ P) := by
  rw [polynomialMomentSet_eq_rareMomentSet]
  exact rareMomentSet_compact_convex μ ρ _ _

def momentPolynomial (L : ℕ) : Option (Fin L) → ℝ[X]
  | none => 1
  | some j => X^(2*j.val+1)

def momentCoordinates (μ : Measure Gap) (q : SignLaw) (L : ℕ) : Option (Fin L) → ℝ :=
  fun i => ∫ d, q.val d*(momentPolynomial L i).eval (d:ℝ) ∂μ

theorem momentCoordinates_none (μ : Measure Gap) (q : SignLaw) (L : ℕ) :
    momentCoordinates μ q L none = signMean μ q.val := by
  simp only [momentCoordinates,momentPolynomial,eval_one,mul_one,signMean]

theorem momentCoordinates_some (μ : Measure Gap) (q : SignLaw) (L : ℕ) (j : Fin L) :
    momentCoordinates μ q L (some j) = ∫ d, q.val d*(d:ℝ)^(2*j.val+1) ∂μ := by
  simp only [momentCoordinates,momentPolynomial,eval_pow,eval_X]

theorem momentCoordinates_match_iff (μ : Measure Gap) [IsFiniteMeasure μ]
    (qH qL : SignLaw) (N : ℕ) :
    (∀ j : Fin ((N+1)/2), momentCoordinates μ qH _ (some j) = momentCoordinates μ qL _ (some j)) ↔
      OddMomentMatch μ qH qL N := by
  have he (j : Fin ((N+1)/2)) := polynomial_moment_difference μ qH qL (X^(2*j.val+1))
  simp only [eval_pow,eval_X] at he
  simp only [OddMomentMatch,momentCoordinates_some,he,sub_eq_zero]

theorem momentCoordinates_mem (μ : Measure Gap) (ρ : ℝ) (q : SignLaw) (hq : RarePrior μ ρ q) (L : ℕ) :
    momentCoordinates μ q L ∈ polynomialMomentSet μ ρ (momentPolynomial L) := ⟨q,hq,fun _ => rfl⟩

theorem polynomialMomentSet_coordinates (μ : Measure Gap) (ρ : ℝ) (L : ℕ)
    (v : Option (Fin L) → ℝ) (hv : v ∈ polynomialMomentSet μ ρ (momentPolynomial L)) :
    ∃ q : SignLaw, RarePrior μ ρ q ∧ v = momentCoordinates μ q L := by
  obtain ⟨q,hq,hv⟩ := hv
  exact ⟨q,hq,funext hv⟩

end ThresholdHC.CapIdentification
