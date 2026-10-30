import ThresholdHC.Genie.Model
import ThresholdHC.StoppingProgram.MomentImage

/-! A single compact moment image simultaneously records the target and
every finite-cap count coefficient of an actual globally rare sign prior. -/

noncomputable section
open MeasureTheory Polynomial Set
namespace ThresholdHC.Genie
open ThresholdHC.Tier6 ThresholdHC.RareAboveTwo ThresholdHC.StoppingProgram
open ThresholdHC.CapIdentification

abbrev AllCountIndex := Option ((N : ℕ) × CountState N)

def allPriorCoordinates (μ : Measure Gap) (q : SignLaw) : AllCountIndex → ℝ
  | none => signMean μ q.val
  | some ⟨_,s⟩ => countCoefficient μ q s

def allPriorMomentImage (μ : Measure Gap) (ρ : ℝ) : Set (AllCountIndex → ℝ) :=
  {u | ∃ q : SignLaw, RarePrior μ ρ q ∧ u = allPriorCoordinates μ q}

theorem allPriorMomentImage_compact_convex (μ : Measure Gap) [IsProbabilityMeasure μ] (ρ : ℝ) :
    IsCompact (allPriorMomentImage μ ρ) ∧ Convex ℝ (allPriorMomentImage μ ρ) := by
  let P : AllCountIndex → ℝ[X] := fun i => match i with
    | none => 1
    | some ⟨_,s⟩ => countContrastPolynomial s
  let b : AllCountIndex → ℝ := fun i => match i with
    | none => 0
    | some ⟨_,s⟩ => countCoefficient μ nullSignLaw s
  have he (q : SignLaw) (i : AllCountIndex) :
      allPriorCoordinates μ q i = (∫ d, q.val d*polynomialL2 μ (P i) d ∂μ)+b i := by
    have hint : (∫ d, q.val d*polynomialL2 μ (P i) d ∂μ) =
        ∫ d, q.val d*(P i).eval (d:ℝ) ∂μ := by
      apply integral_congr_ae
      filter_upwards [polynomialL2_ae μ (P i)] with d hd
      rw [hd]
    rw [hint]
    cases i with
    | none => simp [P,b,allPriorCoordinates,signMean]
    | some i => exact countCoefficient_affine μ q i.2
  have heq : allPriorMomentImage μ ρ = rareMomentSet μ ρ (fun i => polynomialL2 μ (P i)) b := by
    ext u
    simp only [allPriorMomentImage,rareMomentSet,funext_iff,he]
  rw [heq]
  exact rareMomentSet_compact_convex μ ρ _ _

theorem allPriorMomentImage_nonempty (μ : Measure Gap) {ρ : ℝ} (hρ : 0 ≤ ρ) :
    (allPriorMomentImage μ ρ).Nonempty := by
  refine ⟨allPriorCoordinates μ nullSignLaw,nullSignLaw,?_,rfl⟩
  simpa [RarePrior,signMean,nullSignLaw] using hρ

abbrev AllFourCoordinates := ((AllCountIndex → ℝ) × (AllCountIndex → ℝ)) ×
  ((AllCountIndex → ℝ) × (AllCountIndex → ℝ))

def allFourPriorCoordinates (μ : Measure Gap) (Q : FourPriors) : AllFourCoordinates :=
  ((allPriorCoordinates μ Q.low,allPriorCoordinates μ Q.high),
    (allPriorCoordinates μ Q.variance,allPriorCoordinates μ Q.work))

def allFourPriorMomentImage (μ : Measure Gap) (ρ : ℝ) : Set AllFourCoordinates :=
  (allPriorMomentImage μ ρ ×ˢ allPriorMomentImage μ ρ) ×ˢ
    (allPriorMomentImage μ ρ ×ˢ allPriorMomentImage μ ρ)

theorem allFourPriorMomentImage_compact (μ : Measure Gap) [IsProbabilityMeasure μ] (ρ : ℝ) :
    IsCompact (allFourPriorMomentImage μ ρ) := by
  have h := (allPriorMomentImage_compact_convex μ ρ).1
  exact (h.prod h).prod (h.prod h)

theorem allFourPriorMomentImage_iff (μ : Measure Gap) (ρ : ℝ) (u : AllFourCoordinates) :
    u ∈ allFourPriorMomentImage μ ρ ↔
      ∃ Q : FourPriors, Admissible μ ρ Q ∧ u = allFourPriorCoordinates μ Q := by
  constructor
  · rintro ⟨⟨⟨q,hq,heq⟩,⟨r,hr,her⟩⟩,⟨⟨v,hv,hev⟩,⟨w,hw,hew⟩⟩⟩
    refine ⟨⟨q,r,v,w⟩,⟨hq,hr,hv,hw⟩,?_⟩
    exact Prod.ext (Prod.ext heq her) (Prod.ext hev hew)
  · rintro ⟨Q,hQ,rfl⟩
    exact ⟨⟨⟨Q.low,hQ.1,rfl⟩,⟨Q.high,hQ.2.1,rfl⟩⟩,
      ⟨⟨Q.variance,hQ.2.2.1,rfl⟩,⟨Q.work,hQ.2.2.2,rfl⟩⟩⟩

end ThresholdHC.Genie
