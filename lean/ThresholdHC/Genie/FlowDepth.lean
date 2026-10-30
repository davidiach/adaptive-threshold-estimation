import ThresholdHC.Genie.ExtendedFlowConservation

/-! For every finite count flow, expected stopping depth equals the sum of
continuation probabilities, under any harmonic prefix law. -/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace ThresholdHC.Genie
open ThresholdHC.Tier6 ThresholdHC.StoppingProgram

theorem raw_stopping_depth {N : ℕ} (f : Flow N) (hf : FlowCone f)
    (u : ℕ → ℕ → ℝ) (hu : ∀ n k, k ≤ n → u (n+1) k+u (n+1) (k+1) = u n k) :
    (∑ n ∈ Finset.range (N+1), rawLayer f.stopWeight (fun n k => (n:ℝ)*u n k) n) =
      ∑ n ∈ Finset.range (N+1), rawLayer f.continueWeight u n := by
  have hc (n : ℕ) : rawChildren f.continueWeight (fun n k => (n:ℝ)*u n k) n =
      rawLayer f.continueWeight (fun n k => (n:ℝ)*u n k) n+rawLayer f.continueWeight u n := by
    unfold rawChildren rawLayer
    rw [←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k hk
    have he := hu n k (by have h := Finset.mem_range.mp hk; omega)
    push_cast
    nlinarith [congrArg (fun x : ℝ => rawArray f.continueWeight n k*((n:ℝ)+1)*x) he]
  have h := raw_weighted_telescope f hf (fun n k => (n:ℝ)*u n k)
  simp only [hc,Nat.cast_zero,zero_mul,mul_zero,Finset.sum_sub_distrib,Finset.sum_add_distrib] at h
  linarith

theorem stopping_depth_countMean {N : ℕ} (μ : Measure Gap) [IsProbabilityMeasure μ]
    (q : SignLaw) (f : Flow N) (hf : FlowCone f) :
    (∑ n ∈ Finset.range (N+1), rawLayer f.stopWeight (fun n k => (n:ℝ)*prefixCoefficient μ q n k) n) =
      countMean μ q f.continueWeight := by
  rw [raw_stopping_depth f hf _ (prefixCoefficient_add μ q),rawLayer_countMean]

end ThresholdHC.Genie
