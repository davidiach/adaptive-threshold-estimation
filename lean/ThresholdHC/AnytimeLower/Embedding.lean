import ThresholdHC.AnytimeLower.Segment
import ThresholdHC.ConfidenceTransfer.Observable
import ThresholdHC.Genie.Model
import ThresholdHC.Genie.CapMonotonicity
import ThresholdHC.StoppingProgram.AbsorptionRatio

noncomputable section
open MeasureTheory InformationTheory
open scoped ENNReal
namespace ThresholdHC.AnytimeLower
open ThresholdHC.Tier3 ThresholdHC.Tier6 ThresholdHC.RareAboveTwo
open ThresholdHC.StoppingProgram ThresholdHC.ConfidenceTransfer ThresholdHC.ObservableSimulation
open ThresholdHC.Genie

/-- Reversing quarter smoothing represents any two members of the central
quarter of a segment by valid endpoint priors. -/
theorem segment_quarter_identity (q r : SignLaw) (x y : ℝ)
    (hx : 3/8 ≤ x ∧ x ≤ 5/8) (hy : 3/8 ≤ y ∧ y ≤ 5/8) :
    let a := (3*x-y)/2
    let b := (3*y-x)/2
    let ha : 0 ≤ a ∧ a ≤ 1 := ⟨by dsimp [a]; linarith,by dsimp [a]; linarith⟩
    let hb : 0 ≤ b ∧ b ≤ 1 := ⟨by dsimp [b]; linarith,by dsimp [b]; linarith⟩
    smoothedSign (mixPrior q r a ha) (mixPrior q r b hb) =
      mixPrior q r x ⟨by linarith,by linarith⟩ := by
  dsimp only
  apply Subtype.ext
  funext d
  change (3*(((3*x-y)/2)*q.val d+(1-(3*x-y)/2)*r.val d)+
    (((3*y-x)/2)*q.val d+(1-(3*y-x)/2)*r.val d))/4 =
      x*q.val d+(1-x)*r.val d
  ring

/-- An actual observable prefix carries at most its physical length in work. -/
theorem prefix_expected_work_le {R : Type} [MeasurableSpace R]
    (μ : Measure Gap) [IsProbabilityMeasure μ] (A : AdaptiveEstimator R)
    (q : SignLaw) (n : ℕ) :
    (∫ z, ThresholdHC.workOf (processPrefix n z.2) ∂experimentLaw μ A q) ≤ n := by
  calc
    _ ≤ ∫ _ : PopulationSeed R × ProcessTape, (n:ℝ) ∂experimentLaw μ A q :=
      integral_mono (integrable_prefix_work _ _ observable_tape_measurable n)
        (integrable_const _) (fun _ => workOf_le_length _)
    _ = _ := by simp

/-- Quadratic KL control along a central prior segment, for every adaptive
controller, private seed and physical prefix. No independence of observations
across prefixes is assumed. -/
theorem segment_prefix_kl {R : Type} [MeasurableSpace R]
    (μ : Measure Gap) [IsProbabilityMeasure μ] (A : AdaptiveEstimator R)
    (q r : SignLaw) (J : ℝ) (hJ : 0 ≤ J)
    (hI : ∀ m, informationRatio μ m (midpointFourPriors q r) ≤ ENNReal.ofReal J)
    (x y : ℝ) (hx : 3/8 ≤ x ∧ x ≤ 5/8) (hy : 3/8 ≤ y ∧ y ≤ 5/8) (n : ℕ) :
    klDiv (observablePrefixLaw μ A (mixPrior q r x ⟨by linarith,by linarith⟩) n)
      (observablePrefixLaw μ A (mixPrior q r y ⟨by linarith,by linarith⟩) n) ≤
        ENNReal.ofReal ((64/3)*J*(x-y)^2*n) := by
  let a := (3*x-y)/2
  let b := (3*y-x)/2
  have ha : 0 ≤ a ∧ a ≤ 1 := ⟨by dsimp [a]; linarith,by dsimp [a]; linarith⟩
  have hb : 0 ≤ b ∧ b ≤ 1 := ⟨by dsimp [b]; linarith,by dsimp [b]; linarith⟩
  have hm : 1/2 ≤ a+b ∧ a+b ≤ 3/2 := by dsimp [a,b]; constructor <;> linarith
  let u := mixPrior q r a ha
  let v := mixPrior q r b hb
  have hr (m : ℕ) : informationRatio μ m (midpointFourPriors v u) ≤
      ENNReal.ofReal (4*(a-b)^2*J) := by
    have hi := (segment_informationRatio μ m q r b a hb ha ⟨by linarith,by linarith⟩).trans
      (mul_le_mul_right (hI m) _)
    rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ 4*(b-a)^2),
      show 4*(b-a)^2*J = 4*(a-b)^2*J by ring] at hi
    exact hi
  have hlocal : LocalReferenceWorkBound μ (gapParameter false) (gapParameter true)
      (signUnit u) (signUnit v) (4*(a-b)^2*J/2) :=
    ThresholdHC.ConfidenceProgram.midpoint_reference_bound μ v u
      (by positivity : 0 ≤ 4*(a-b)^2*J) hr
  have hk := observable_reference_work_kl μ A u v n (4*(a-b)^2*J/2)
    (by positivity) hlocal
  have hc : (8/3)*(4*(a-b)^2*J/2) = (64/3)*J*(x-y)^2 := by dsimp [a,b]; ring
  have hxid : smoothedSign u v = mixPrior q r x ⟨by linarith,by linarith⟩ :=
    segment_quarter_identity q r x y hx hy
  have hyid : smoothedSign v u = mixPrior q r y ⟨by linarith,by linarith⟩ :=
    segment_quarter_identity q r y x hy hx
  rw [hxid,hyid,hc] at hk
  exact hk.trans (ENNReal.ofReal_le_ofReal
    (mul_le_mul_of_nonneg_left
      (prefix_expected_work_le μ A (mixPrior q r x ⟨by linarith,by linarith⟩) n)
      (by positivity)))

end ThresholdHC.AnytimeLower
