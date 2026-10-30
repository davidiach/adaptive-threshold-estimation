import ThresholdHC.EntropyTailExecution.CoupledCall
import ThresholdHC.EntropyTailSampling.RaceMoments
import ThresholdHC.EntropyTailAssembly.CertificateAlgebra

/-! Finite-prefix bounds and telescoping identities for coupled calls. -/

noncomputable section
open MeasureTheory Real
open scoped BigOperators

namespace ThresholdHC.EntropyTailExecution
open ThresholdHC.EntropyTailAssembly ThresholdHC.RareAboveTwo ThresholdHC.Uniform713

theorem call_cost_integrable (ν : Measure (ℕ → Bool)) [IsFiniteMeasure ν]
    (A : FiniteCall) {K : ℝ} (hK : ∀ ω, (A.cost ω:ℝ) ≤ K) :
    Integrable (fun ω => (A.cost ω:ℝ)) ν := by
  apply Integrable.of_bound
    ((measurable_of_countable (fun n : ℕ => (n:ℝ))).comp A.measurable_cost).aestronglyMeasurable K
  exact ae_of_all _ (fun ω => by
    change ‖(A.cost ω:ℝ)‖ ≤ K
    rw [Real.norm_of_nonneg (Nat.cast_nonneg _)]
    exact hK ω)

theorem call_cost_mean_ge_one (ν : Measure (ℕ → Bool)) [IsProbabilityMeasure ν]
    (A : FiniteCall) {K : ℝ} (hK : ∀ ω, (A.cost ω:ℝ) ≤ K) :
    1 ≤ ∫ ω, (A.cost ω:ℝ) ∂ν := by
  have h := integral_mono (integrable_const (μ := ν) (1:ℝ)) (call_cost_integrable ν A hK)
    (fun ω => (show (1:ℝ) ≤ (A.cost ω:ℝ) by exact_mod_cast A.positive ω))
  simpa using h

theorem incrementCall_bounded (A : ℕ → FiniteCall)
    (hb : ∀ l ω, (A l).value ω = 0 ∨ (A l).value ω = 1) (l : ℕ) (ω : ℕ → Bool) :
    ‖(incrementCall A l).value ω‖ ≤ 1 := by
  cases l with
  | zero => rcases hb 0 ω with h | h <;> simp [incrementCall,h]
  | succ l =>
    rcases hb (l+1) ω with h | h <;> rcases hb l ω with h' | h' <;>
      simp [incrementCall, differenceCall, h, h']

theorem incrementCall_integrable (ν : Measure (ℕ → Bool)) [IsFiniteMeasure ν]
    (A : ℕ → FiniteCall) (hb : ∀ l ω, (A l).value ω = 0 ∨ (A l).value ω = 1) (l : ℕ) :
    Integrable (incrementCall A l).value ν :=
  Integrable.of_bound (incrementCall A l).measurable_value.aestronglyMeasurable 1
    (ae_of_all _ (incrementCall_bounded A hb l))

theorem incrementCall_mean_sum (ν : Measure (ℕ → Bool)) [IsFiniteMeasure ν]
    (A : ℕ → FiniteCall) (hb : ∀ l ω, (A l).value ω = 0 ∨ (A l).value ω = 1) (J : ℕ) :
    (∑ i : Fin (J+1), ∫ ω, (incrementCall A i.val).value ω ∂ν) = ∫ ω, (A J).value ω ∂ν := by
  rw [← integral_finsetSum _ (fun i _ => incrementCall_integrable ν A hb i.val)]
  apply integral_congr_ae
  apply ae_of_all
  intro ω
  simp only [incrementCall_value]
  rw [Fin.sum_univ_eq_sum_range, sum_increment]

theorem incrementCall_cost_bound (A : ℕ → FiniteCall) (K : ℕ → ℝ)
    (hK : ∀ l ω, ((A l).cost ω:ℝ) ≤ K l) (l : ℕ) (ω : ℕ → Bool) :
    ((incrementCall A l).cost ω:ℝ) ≤ adjacentCost K l := by
  apply (incrementCall_cost_le A l ω).trans
  unfold adjacentCost
  split_ifs with h
  · subst l; exact hK 0 ω
  · exact add_le_add (hK l ω) (hK (l-1) ω)

theorem incrementCall_work_bound (ν : Measure (ℕ → Bool)) [IsProbabilityMeasure ν]
    (A : ℕ → FiniteCall) (K C : ℕ → ℝ)
    (hK : ∀ l ω, ((A l).cost ω:ℝ) ≤ K l)
    (hC : ∀ l, (∫ ω, ((A l).cost ω:ℝ) ∂ν) ≤ C l) (l : ℕ) :
    (∫ ω, ((incrementCall A l).cost ω:ℝ) ∂ν) ≤ adjacentCost C l := by
  cases l with
  | zero => simpa [incrementCall, adjacentCost] using hC 0
  | succ l =>
    have hi := (call_cost_integrable ν (A (l+1)) (hK (l+1))).add
      (call_cost_integrable ν (A l) (hK l))
    have h := integral_mono
      (call_cost_integrable ν (incrementCall A (l+1)) (incrementCall_cost_bound A K hK (l+1)))
      hi (fun ω => by simpa using incrementCall_cost_le A (l+1) ω)
    dsimp only [Pi.add_apply] at h
    rw [integral_add (call_cost_integrable ν (A (l+1)) (hK (l+1)))
      (call_cost_integrable ν (A l) (hK l))] at h
    simpa [adjacentCost] using h.trans (add_le_add (hC (l+1)) (hC l))

theorem incrementCall_second_bound (ν : Measure (ℕ → Bool)) [IsProbabilityMeasure ν]
    (A : ℕ → FiniteCall) (hb : ∀ l ω, (A l).value ω = 0 ∨ (A l).value ω = 1)
    (ρ : ℝ) (hfirst : (∫ ω, (A 0).value ω ∂ν) ≤ ρ+levelAccuracy ρ 0)
    (hdiff : ∀ l, (∫ ω, ((A (l+1)).value ω-(A l).value ω)^2 ∂ν) ≤
      levelAccuracy ρ (l+1)+levelAccuracy ρ l) (l : ℕ) :
    (∫ ω, ((incrementCall A l).value ω)^2 ∂ν) ≤ 17*levelAccuracy ρ l := by
  cases l with
  | zero =>
    have he : (fun ω => ((incrementCall A 0).value ω)^2) = (A 0).value := by
      funext ω
      rcases hb 0 ω with h | h <;> simp [incrementCall,h]
    rw [he]
    have hδ := levelAccuracy_zero ρ
    linarith
  | succ l =>
    change (∫ ω, ((A (l+1)).value ω-(A l).value ω)^2 ∂ν) ≤ _
    have hδ := levelAccuracy_succ ρ l
    linarith [hdiff l]

end ThresholdHC.EntropyTailExecution
