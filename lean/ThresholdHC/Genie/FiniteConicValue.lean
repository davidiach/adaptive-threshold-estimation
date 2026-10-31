import ThresholdHC.Genie.FiniteConicPrice
import ThresholdHC.Genie.ScalarPrice

/-! Eliminating finite conic Bellman, latent, price and scale variables gives
exactly the squared optimized genie value. -/

noncomputable section
open MeasureTheory
open scoped ENNReal BigOperators
namespace ThresholdHC.Genie
open ThresholdHC.Tier6 ThresholdHC.StoppingProgram
variable {I : Type*} [Fintype I]

theorem genieDualRatio_real (μ : Measure Gap) (B : ℝ) (hB : 0 ≤ B) (N : ℕ) (Q : FourPriors)
    (hK : genieInformationRatio μ N Q ≠ ⊤) :
    genieDualRatio μ B N Q = ENNReal.ofReal (max (signMean μ Q.high.val-signMean μ Q.low.val) 0)^2/
      ENNReal.ofReal (4+B*(genieInformationRatio μ N Q).toReal) := by
  unfold genieDualRatio
  congr 1
  · simp
  · rw [ENNReal.ofReal_add (by norm_num) (by positivity),ENNReal.ofReal_mul hB,
      ENNReal.ofReal_toReal hK]
    norm_num

theorem finiteGenieCones_objective_le (N : ℕ) (μ : Measure Gap) [IsProbabilityMeasure μ]
    (w : I → ℝ) (d : I → Gap) (hw : ∀ i, 0 < w i)
    (hμ : μ = ∑ i, ENNReal.ofReal (w i) • Measure.dirac (d i))
    (B : ℝ) (hB : 0 ≤ B) (Q : FourPriors) (hN : 0 < N)
    (α η : ℝ) (hα : 0 ≤ α) (hη : 0 ≤ η) (X : CountState N → ℝ) (rp rm : I → ℝ)
    (hcone : FiniteGenieCones μ w d Q α η X rp rm) :
    ENNReal.ofReal (α*(signMean μ Q.high.val-signMean μ Q.low.val)-α^2-η*B) ≤ genieDualRatio μ B N Q := by
  by_cases hα0 : α = 0
  · subst α
    have he : 0*(signMean μ Q.high.val-signMean μ Q.low.val)-(0:ℝ)^2-η*B ≤ 0 := by nlinarith [mul_nonneg hη hB]
    rw [ENNReal.ofReal_eq_zero.mpr he]
    exact bot_le
  have hαp : 0 < α := lt_of_le_of_ne hα (Ne.symm hα0)
  have hprice := (finiteGenieCones_iff_price N μ w d hw hμ Q hN α η hαp hη).mp ⟨X,rp,rm,hcone⟩
  have hK := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hprice
  have hk := ENNReal.toReal_mono ENNReal.ofReal_ne_top hprice
  rw [ENNReal.toReal_ofReal (by positivity : 0 ≤ 4*η/α^2)] at hk
  have hpr : α^2*(genieInformationRatio μ N Q).toReal ≤ 4*η := by
    have hh := (le_div_iff₀ (sq_pos_of_pos hαp)).mp hk
    nlinarith
  rw [genieDualRatio_real μ B hB N Q hK]
  exact scale_objective_bound _ _ _ _ _ hB ENNReal.toReal_nonneg hα hη hpr

theorem finiteGenieCones_objective_attained (N : ℕ) (μ : Measure Gap) [IsProbabilityMeasure μ]
    (w : I → ℝ) (d : I → Gap) (hw : ∀ i, 0 < w i)
    (hμ : μ = ∑ i, ENNReal.ofReal (w i) • Measure.dirac (d i))
    (B : ℝ) (hB : 0 < B) (Q : FourPriors) (hN : 0 < N) :
    ∃ (α η : ℝ) (X : CountState N → ℝ) (rp rm : I → ℝ), 0 ≤ α ∧ 0 ≤ η ∧
      FiniteGenieCones μ w d Q α η X rp rm ∧
      ENNReal.ofReal (α*(signMean μ Q.high.val-signMean μ Q.low.val)-α^2-η*B) = genieDualRatio μ B N Q := by
  by_cases hK : genieInformationRatio μ N Q = ⊤
  · refine ⟨0,0,fun _ => 0,fun _ => 0,fun _ => 0,le_rfl,le_rfl,
      finiteGenieCones_zero N μ w d Q 0 le_rfl,?_⟩
    simp [genieDualRatio,hK,(ENNReal.ofReal_pos.mpr hB).ne']
  obtain ⟨α,η,hα,hη,hprice,he⟩ := scale_objective_attained
    (signMean μ Q.high.val-signMean μ Q.low.val) B (genieInformationRatio μ N Q).toReal hB.le ENNReal.toReal_nonneg
  rw [←genieDualRatio_real μ B hB.le N Q hK] at he
  by_cases hα0 : α = 0
  · subst α
    exact ⟨0,η,fun _ => 0,fun _ => 0,fun _ => 0,le_rfl,hη,finiteGenieCones_zero N μ w d Q η hη,he⟩
  have hαp : 0 < α := lt_of_le_of_ne hα (Ne.symm hα0)
  have hpr : genieInformationRatio μ N Q ≤ ENNReal.ofReal (4*η/α^2) := by
    rw [←ENNReal.ofReal_toReal hK]
    apply ENNReal.ofReal_le_ofReal
    apply (le_div_iff₀ (sq_pos_of_pos hαp)).mpr
    nlinarith [hprice]
  obtain ⟨X,rp,rm,hcone⟩ := (finiteGenieCones_iff_price N μ w d hw hμ Q hN α η hαp hη).mpr hpr
  exact ⟨α,η,X,rp,rm,hα,hη,hcone,he⟩

def finiteGenieConicValue (N : ℕ) (μ : Measure Gap) (w : I → ℝ) (d : I → Gap) (ρ B : ℝ) : ℝ≥0∞ :=
  ⨆ (Q : FourPriors) (_ : Admissible μ ρ Q) (α : ℝ) (η : ℝ) (_ : 0 ≤ α) (_ : 0 ≤ η)
    (X : CountState N → ℝ) (rp : I → ℝ) (rm : I → ℝ) (_ : FiniteGenieCones μ w d Q α η X rp rm),
      ENNReal.ofReal (α*(signMean μ Q.high.val-signMean μ Q.low.val)-α^2-η*B)

theorem finiteGenieConicValue_eq (N : ℕ) (μ : Measure Gap) [IsProbabilityMeasure μ]
    (w : I → ℝ) (d : I → Gap) (hw : ∀ i, 0 < w i)
    (hμ : μ = ∑ i, ENNReal.ofReal (w i) • Measure.dirac (d i))
    (ρ B : ℝ) (hB : 0 < B) (hN : 0 < N) :
    finiteGenieConicValue N μ w d ρ B = genieSquared μ ρ B N := by
  apply le_antisymm
  · apply iSup_le
    intro Q
    apply iSup_le
    intro hQ
    apply iSup_le
    intro α
    apply iSup_le
    intro η
    apply iSup_le
    intro hα
    apply iSup_le
    intro hη
    apply iSup_le
    intro X
    apply iSup_le
    intro rp
    apply iSup_le
    intro rm
    apply iSup_le
    intro hcone
    exact (finiteGenieCones_objective_le N μ w d hw hμ B hB.le Q hN α η hα hη X rp rm hcone).trans
      (le_iSup_of_le Q (le_iSup_of_le hQ le_rfl))
  · apply iSup_le
    intro Q
    apply iSup_le
    intro hQ
    obtain ⟨α,η,X,rp,rm,hα,hη,hcone,he⟩ := finiteGenieCones_objective_attained N μ w d hw hμ B hB Q hN
    rw [←he]
    exact le_iSup_of_le Q (le_iSup_of_le hQ (le_iSup_of_le α (le_iSup_of_le η
      (le_iSup_of_le hα (le_iSup_of_le hη (le_iSup_of_le X (le_iSup_of_le rp
        (le_iSup_of_le rm (le_iSup_of_le hcone le_rfl)))))))))

end ThresholdHC.Genie
