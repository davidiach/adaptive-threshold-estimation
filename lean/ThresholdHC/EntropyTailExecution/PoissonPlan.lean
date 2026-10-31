import ThresholdHC.EntropyTailExecution.ActualPlan
import ThresholdHC.EntropyTailSampling.MultilevelPoisson
import ThresholdHC.BlindUpper.InfiniteArrays

/-! Poisson counts determine a finite list of distinct population labels.
Pair-number labels give exactly the independent marked multilevel law. -/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal BigOperators

namespace ThresholdHC.EntropyTailExecution
open ThresholdHC.BlindUpper ThresholdHC.EntropyTailSampling

def countLabels {N : ℕ} (n : Fin N → ℕ) : List ℕ := by
  classical
  exact (Finset.univ.image (fun x : (i : Fin N) × Fin (n i) => Nat.pair x.1.val x.2.val)).toList

theorem countLabels_nodup {N : ℕ} (n : Fin N → ℕ) : (countLabels n).Nodup := Finset.nodup_toList _

theorem countLabel_injective {N : ℕ} (n : Fin N → ℕ) :
    Function.Injective (fun x : (i : Fin N) × Fin (n i) => Nat.pair x.1.val x.2.val) := by
  rintro ⟨i,j⟩ ⟨i',j'⟩ h
  have hi : i = i' := Fin.ext (Nat.pair_eq_pair.mp h).1
  subst i'
  have hj : j = j' := Fin.ext (Nat.pair_eq_pair.mp h).2
  subst j'
  rfl

theorem sum_countLabels {N : ℕ} (n : Fin N → ℕ) {α : Type*} [AddCommMonoid α] (f : ℕ → α) :
    ((countLabels n).map f).sum = ∑ i : Fin N, ∑ j : Fin (n i), f (Nat.pair i.val j.val) := by
  classical
  unfold countLabels
  rw [Finset.sum_map_toList, Finset.sum_image (countLabel_injective n).injOn, Fintype.sum_sigma]

def countLaw {N : ℕ} (r : Fin N → ℝ≥0) : Measure (Fin N → ℕ) :=
  Measure.pi (fun i => poissonMeasure (r i))

instance countLaw_probability {N : ℕ} (r : Fin N → ℝ≥0) : IsProbabilityMeasure (countLaw r) := by
  unfold countLaw
  infer_instance

def pairedStreams {N : ℕ} {X : Type} (s : ℕ → X) : Fin N → ℕ → X :=
  fun i j => s (Nat.pair i.val j)

theorem pairedStreams_preserving {N : ℕ} {X : Type} [MeasurableSpace X]
    (ν : Measure X) [IsProbabilityMeasure ν] :
    MeasurePreserving (pairedStreams (N := N)) (Measure.infinitePi (fun _ : ℕ => ν))
      (Measure.pi (fun _ : Fin N => Measure.infinitePi (fun _ : ℕ => ν))) :=
  (prefix_projection_preserving (Measure.infinitePi (fun _ : ℕ => ν)) N).comp
    ⟨measurable_splitPairArray, splitPairArray_map ν⟩

def poissonPlanInput {N : ℕ} {X : Type} (z : (Fin N → ℕ) × (ℕ → X)) : Fin N → ℕ × (ℕ → X) :=
  fun i => (z.1 i, pairedStreams z.2 i)

theorem poissonPlanInput_preserving {N : ℕ} {X : Type} [MeasurableSpace X]
    (ν : Measure X) [IsProbabilityMeasure ν] (r : Fin N → ℝ≥0) :
    MeasurePreserving (poissonPlanInput (X := X))
      ((countLaw r).prod (Measure.infinitePi (fun _ : ℕ => ν))) (multilevelLaw ν r) := by
  let e := MeasurableEquiv.arrowProdEquivProdArrow ℕ (ℕ → X) (Fin N)
  have hz := (measurePreserving_arrowProdEquivProdArrow ℕ (ℕ → X) (Fin N)
    (fun i => poissonMeasure (r i)) (fun _ => Measure.infinitePi (fun _ : ℕ => ν))).symm e
  exact hz.comp ((MeasurePreserving.id (countLaw r)).prod (pairedStreams_preserving ν))

def indexedCall {J : ℕ} (A : Fin (J+1) → FiniteCall) (j : ℕ) : FiniteCall :=
  A ⟨min (Nat.unpair j).1 J, by omega⟩

theorem indexedCall_pair {J : ℕ} (A : Fin (J+1) → FiniteCall) (i : Fin (J+1)) (n : ℕ) :
    indexedCall A (Nat.pair i.val n) = A i := by
  unfold indexedCall
  congr 1
  apply Fin.ext
  simp only [Nat.unpair_pair]
  exact min_eq_left (by omega)

def poissonPlanEstimator {J : ℕ} (r : Fin (J+1) → ℝ≥0) (A : Fin (J+1) → FiniteCall) :
    ThresholdHC.Tier6.AdaptiveEstimator (Fin (J+1) → ℕ) :=
  finitePlanEstimator (countLaw r) (indexedCall A) countLabels

theorem plannedCost_counts {J : ℕ} (A : Fin (J+1) → FiniteCall)
    (n : Fin (J+1) → ℕ) (s : ℕ → ℕ → Bool) :
    (plannedCost (indexedCall A) (countLabels n) s : ℝ) =
      multilevelCost (fun i ω => ((A i).cost ω:ℝ)) (poissonPlanInput (n,s)) := by
  unfold plannedCost
  rw [sum_countLabels]
  push_cast
  simp only [indexedCall_pair, multilevelCost, countedSum, prefixSum, poissonPlanInput, pairedStreams]
  rfl

theorem plannedValue_counts {J : ℕ} (A : Fin (J+1) → FiniteCall)
    (r : Fin (J+1) → ℝ≥0) (n : Fin (J+1) → ℕ) (s : ℕ → ℕ → Bool)
    (Y : Fin (J+1) → (ℕ → Bool) → ℝ)
    (hY : ∀ i ω, (A i).value ω = (r i:ℝ)⁻¹*Y i ω) :
    plannedValue (indexedCall A) (countLabels n) s = multilevelValue r Y (poissonPlanInput (n,s)) := by
  unfold plannedValue
  rw [sum_countLabels]
  simp only [indexedCall_pair, hY, multilevelValue, poissonAverage, countedSum, prefixSum,
    poissonPlanInput, pairedStreams, Finset.mul_sum]
  rfl

end ThresholdHC.EntropyTailExecution
