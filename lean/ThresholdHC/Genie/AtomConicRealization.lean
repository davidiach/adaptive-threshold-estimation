import ThresholdHC.Genie.AtomConicModel

/-! Every feasible atom SOCP point realizes admissible measurable priors,
including zero endpoint scale and zero work price. -/

noncomputable section
open MeasureTheory
open scoped ENNReal BigOperators
namespace ThresholdHC.Genie
open ThresholdHC.Tier6 ThresholdHC.RareAboveTwo ThresholdHC.StoppingProgram
variable {I : Type*} [Fintype I]

theorem atomConic_realization {N : ℕ} (μ : Measure Gap) [IsProbabilityMeasure μ]
    (w : I → ℝ) (d : I → Gap) (hw : ∀ i, 0 ≤ w i)
    (hμ : μ = ∑ i, ENNReal.ofReal (w i) • Measure.dirac (d i)) (hd : Function.Injective d)
    (ρ B : ℝ) (hρ : 0 ≤ ρ) (v : AtomConicPoint I N) (hv : AtomConicFeasible w d ρ v) :
    ∃ Q : FourPriors, Admissible μ ρ Q ∧
      FiniteGenieCones μ w d Q v.scale v.price v.bellman v.revealPlus v.revealMinus ∧
      atomConicObjective w B v ≤ v.scale*(signMean μ Q.high.val-signMean μ Q.low.val)-v.scale^2-v.price*B := by
  obtain ⟨hα,hη,hαsq,hL,hH,hV,hW,hlat,hstop,hcont,hroot⟩ := hv
  obtain ⟨qL,hqL,heL⟩ := exists_scaled_atom_prior μ w d hw hμ hd ρ v.scale hρ hα v.low hL.1 hL.2
  obtain ⟨qH,hqH,heH⟩ := exists_scaled_atom_prior μ w d hw hμ hd ρ v.scale hρ hα v.high hH.1 hH.2
  obtain ⟨qV,hqV,heV⟩ := exists_scaled_atom_prior μ w d hw hμ hd ρ 1 hρ (by norm_num) v.variance hV.1 hV.2
  obtain ⟨qW,hqW,heW⟩ := exists_scaled_atom_prior μ w d hw hμ hd ρ v.price hρ hη v.work hW.1 hW.2
  let Q : FourPriors := ⟨qL,qH,qV,qW⟩
  have hcoL := finite_scaled_prefixCoefficient μ w d hw hμ qL v.scale v.low heL
  have hcoH := finite_scaled_prefixCoefficient μ w d hw hμ qH v.scale v.high heH
  have hcoV := finite_scaled_prefixCoefficient μ w d hw hμ qV 1 v.variance heV
  have hcoW := finite_scaled_prefixCoefficient μ w d hw hμ qW v.price v.work heW
  simp only [one_mul] at heV hcoV
  refine ⟨Q,⟨hqL,hqH,hqV,hqW⟩,⟨?_,?_,?_,hroot⟩,?_⟩
  · intro i
    change 0 ≤ v.revealPlus i ∧ 0 ≤ v.revealMinus i ∧
      (v.scale*(qH.val (d i)-qL.val (d i)))^2 ≤ qV.val (d i)*v.revealPlus i ∧
      (v.scale*(qH.val (d i)-qL.val (d i)))^2 ≤ (1-qV.val (d i))*v.revealMinus i
    rw [mul_sub,heH,heL,heV]
    exact hlat i
  · intro n k hn hnN hk
    refine ⟨(hstop n k hn hnN hk).1,?_⟩
    by_cases he : n = N
    · simpa only [he,ite_true] using (hstop n k hn hnN hk).2
    · simp only [he,ite_false]
      change (v.scale*(prefixCoefficient μ qH n k-prefixCoefficient μ qL n k))^2 ≤
        4*prefixCoefficient μ qV n k*arrayAt v.bellman n k
      rw [mul_sub,hcoH,hcoL,hcoV]
      simpa only [he,ite_false] using (hstop n k hn hnN hk).2
  · intro n k hn hnN hk
    change arrayAt v.bellman (n+1) k+arrayAt v.bellman (n+1) (k+1)-v.price*prefixCoefficient μ qW n k ≤ _
    rw [hcoW]
    exact hcont n k hn hnN hk
  · have hh := finite_scaled_mean μ w d hw hμ qH v.scale v.high heH
    have hl := finite_scaled_mean μ w d hw hμ qL v.scale v.low heL
    unfold atomConicObjective
    simp_rw [mul_sub]
    rw [Finset.sum_sub_distrib,←hh,←hl]
    change _ ≤ v.scale*signMean μ qH.val-v.scale*signMean μ qL.val-v.scale^2-v.price*B
    nlinarith

theorem atomConicValue_eq_genieSquared (N : ℕ) (μ : Measure Gap) [IsProbabilityMeasure μ]
    (w : I → ℝ) (d : I → Gap) (hw : ∀ i, 0 < w i)
    (hμ : μ = ∑ i, ENNReal.ofReal (w i) • Measure.dirac (d i)) (hd : Function.Injective d)
    (ρ B : ℝ) (hρ : 0 ≤ ρ) (hB : 0 < B) (hN : 0 < N) :
    atomConicValue N w d ρ B = genieSquared μ ρ B N := by
  apply le_antisymm
  · apply iSup_le
    intro v
    apply iSup_le
    intro hv
    obtain ⟨Q,hQ,hcone,ho⟩ := atomConic_realization μ w d (fun i => (hw i).le) hμ hd ρ B hρ v hv
    apply (ENNReal.ofReal_le_ofReal ho).trans
    apply (finiteGenieCones_objective_le N μ w d hw hμ B hB.le Q hN v.scale v.price hv.1 hv.2.1
      v.bellman v.revealPlus v.revealMinus hcone).trans
    exact le_iSup_of_le Q (le_iSup_of_le hQ le_rfl)
  · apply iSup_le
    intro Q
    apply iSup_le
    intro hQ
    obtain ⟨α,η,X,rp,rm,hα,hη,hcone,he⟩ := finiteGenieCones_objective_attained N μ w d hw hμ B hB Q hN
    have hpoint := atomConicFeasible_of_priors μ w d (fun i => (hw i).le) hμ ρ Q hQ α η hα hη X rp rm hcone
    rw [←he,←atomConicObjective_of_priors μ w d (fun i => (hw i).le) hμ B Q α η X rp rm]
    exact le_iSup_of_le (atomPointOfPriors d Q α η X rp rm) (le_iSup_of_le hpoint le_rfl)

end ThresholdHC.Genie
