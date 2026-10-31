import ThresholdHC.StoppingProgram.FunctionMomentImage
import ThresholdHC.StoppingProgram.Slater

/-! An attained scalar multiplier for the global rarity constraint on an
arbitrary integrable bounded-function moment image. -/

noncomputable section
open MeasureTheory Set
open scoped BigOperators

namespace ThresholdHC.StoppingProgram
open ThresholdHC.Tier6 (Gap SignLaw signMean)
open ThresholdHC.RareAboveTwo

theorem rarity_function_multiplier (μ : Measure Gap) [IsProbabilityMeasure μ]
    {ρ : ℝ} (hρ : 0 < ρ) (f : Gap → ℝ) (hf : MemLp f 2 μ) :
    ∃ ell : ℝ, 0 ≤ ell ∧ ∀ q : SignLaw,
      (∫ d, q.val d*f d ∂μ)-ell*signMean μ q.val ≤ rareFunctional μ ρ f-ell*ρ := by
  let F : Fin 2 → Gap → ℝ := ![fun _ => 1,f]
  have hF : ∀ i, MemLp (F i) 2 μ := by
    intro i
    fin_cases i
    · exact memLp_const 1
    · exact hf
  let S := functionMomentImage μ 1 F (fun _ => 0)
  have hS : Convex ℝ S := (functionMomentImage_compact_convex μ 1 F _ hF).2
  let g : Option Unit → (Fin 2 → ℝ) → ℝ
    | none => fun u => -u 1
    | some _ => fun u => u 0-ρ
  have hg : ∀ i, ConvexOn ℝ S (g i) := by
    intro i
    refine ⟨hS,?_⟩
    intro x hx y hy a b ha hb hab
    cases i with
    | none => change -(a*x 1+b*y 1) ≤ a*(-x 1)+b*(-y 1); ring_nf; exact le_rfl
    | some i =>
      change a*x 0+b*y 0-ρ ≤ a*(x 0-ρ)+b*(y 0-ρ)
      nlinarith [congrArg (fun r : ℝ => r*ρ) hab]
  have hcoordinates (q : SignLaw) (u : Fin 2 → ℝ)
      (hu : ∀ i, u i = (∫ d, q.val d*F i d ∂μ)+0) :
      u 0 = signMean μ q.val ∧ u 1 = ∫ d, q.val d*f d ∂μ := by
    constructor
    · simpa [F,signMean] using hu 0
    · simpa [F] using hu 1
  have hlower : ∀ u ∈ S, (∀ i : Unit, g (some i) u ≤ 0) → -rareFunctional μ ρ f ≤ g none u := by
    rintro u ⟨q,hq,hu⟩ hh
    obtain ⟨hu0,hu1⟩ := hcoordinates q u hu
    have hqρ : RarePrior μ ρ q := by
      have h := hh ()
      change u 0-ρ ≤ 0 at h
      rw [hu0] at h
      change signMean μ q.val ≤ ρ
      linarith
    have h := prior_function_le_rareFunctional μ f hf q hqρ
    change -rareFunctional μ ρ f ≤ -u 1
    rw [hu1]
    linarith
  have hstrict : ∃ u ∈ S, ∀ i : Unit, g (some i) u < 0 := by
    let q0 : SignLaw := ⟨fun _ => 0,measurable_const,fun _ => ⟨le_rfl,by norm_num⟩⟩
    refine ⟨0,⟨q0,?_,?_⟩,?_⟩
    · simp [RarePrior,signMean,q0]
    · intro i
      simp [q0]
    · intro i
      change (0:ℝ)-ρ < 0
      linarith
  obtain ⟨w,hw,hh⟩ := finite_slater_multipliers S hS g hg (-rareFunctional μ ρ f) hlower hstrict
  refine ⟨w (),hw (),?_⟩
  intro q
  let u : Fin 2 → ℝ := ![signMean μ q.val,∫ d, q.val d*f d ∂μ]
  have hu : u ∈ S := by
    refine ⟨q,(ThresholdHC.Tier6.signMean_bounds μ q).2,?_⟩
    intro i
    fin_cases i <;> simp [u,F,signMean]
  have h := hh u hu
  simp only [Fintype.sum_unique] at h
  change -rareFunctional μ ρ f ≤ -(∫ d, q.val d*f d ∂μ)+w ()*(signMean μ q.val-ρ) at h
  nlinarith

end ThresholdHC.StoppingProgram
