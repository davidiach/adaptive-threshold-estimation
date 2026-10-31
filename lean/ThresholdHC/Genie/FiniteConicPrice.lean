import ThresholdHC.Genie.FiniteConicEnvelope

/-! Exact elimination of finite conic Bellman variables into a genie
information/work price, including singular variance references. -/

noncomputable section
open MeasureTheory
open scoped ENNReal BigOperators
namespace ThresholdHC.Genie
open ThresholdHC.Tier6 ThresholdHC.StoppingProgram
variable {I : Type*} [Fintype I]

theorem scaled_genie_root (μ : Measure Gap) (Q : FourPriors) (N : ℕ)
    (α η : ℝ) (hα : 0 < α) :
    rootBellman (fun n k => α^2/4*genieReward μ Q N n k) (prefixCoefficient μ Q.work) η (N-1) =
      α^2/4*rootBellman (genieReward μ Q N) (prefixCoefficient μ Q.work) (4*η/α^2) (N-1) := by
  have he : α^2/4*(4*η/α^2) = η := by field_simp
  calc
    _ = rootBellman (fun n k => α^2/4*genieReward μ Q N n k) (prefixCoefficient μ Q.work)
        (α^2/4*(4*η/α^2)) (N-1) :=
      congrArg (fun z => rootBellman (fun n k => α^2/4*genieReward μ Q N n k)
        (prefixCoefficient μ Q.work) z (N-1)) he.symm
    _ = _ := rootBellman_scale (genieReward μ Q N) (prefixCoefficient μ Q.work)
      (4*η/α^2) (α^2/4) (by positivity) (N-1)

theorem finiteGenieCones_iff_price (N : ℕ) (μ : Measure Gap) [IsProbabilityMeasure μ]
    (w : I → ℝ) (d : I → Gap) (hw : ∀ i, 0 < w i)
    (hμ : μ = ∑ i, ENNReal.ofReal (w i) • Measure.dirac (d i))
    (Q : FourPriors) (hN : 0 < N) (α η : ℝ) (hα : 0 < α) (hη : 0 ≤ η) :
    (∃ X rPlus rMinus, FiniteGenieCones (N := N) μ w d Q α η X rPlus rMinus) ↔
      genieInformationRatio μ N Q ≤ ENNReal.ofReal (4*η/α^2) := by
  have he (hC : latentDivergence μ Q ≠ ⊤) :
      (∃ X rPlus rMinus, FiniteGenieCones (N := N) μ w d Q α η X rPlus rMinus) ↔
        genieInformationRatio μ N Q ≤ ENNReal.ofReal (4*η/α^2) := by
    rw [finiteGenieCones_iff_bellman N μ w d hw hμ Q hC hN α η,scaled_genie_root μ Q N α η hα]
    have hc : 0 < α^2/4 := by positivity
    have hm (v : ℝ) : α^2/4*v ≤ 0 ↔ v ≤ 0 := by constructor <;> intro h <;> nlinarith
    rw [hm]
    exact (genieInformationRatio_bellman_certificate μ N Q hN hC (4*η/α^2) (by positivity)).symm
  constructor
  · rintro h
    obtain ⟨X,rp,rm,hX⟩ := h
    have hC := latentCones_finite μ w d hμ Q α hα rp rm hX.1
    exact (he hC).mp ⟨X,rp,rm,hX⟩
  · intro h
    have hK : genieInformationRatio μ N Q ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top h
    have hC : latentDivergence μ Q ≠ ⊤ := fun hc => hK ((genieInformationRatio_top_iff μ N hN Q).mpr hc)
    exact (he hC).mpr h

theorem finiteGenieCones_zero (N : ℕ) (μ : Measure Gap) (w : I → ℝ) (d : I → Gap)
    (Q : FourPriors) (η : ℝ) (hη : 0 ≤ η) :
    FiniteGenieCones (N := N) μ w d Q 0 η (fun _ => 0) (fun _ => 0) (fun _ => 0) := by
  have hz (n k : ℕ) : arrayAt (N := N) (fun _ => (0:ℝ)) n k = 0 := by
    simp [arrayAt]
  refine ⟨?_,?_,?_,?_⟩
  · intro i
    simp
  · intro n k hn hnN hk
    simp [hz,finiteRevealBound]
  · intro n k hn hnN hk
    simp only [hz,zero_add,zero_sub,neg_nonpos]
    exact mul_nonneg hη (prefixCoefficient_nonneg μ Q.work n k)
  · simpa only [hz,zero_add,zero_sub,neg_nonpos] using hη

end ThresholdHC.Genie
