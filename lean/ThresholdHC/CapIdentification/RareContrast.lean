import ThresholdHC.CapIdentification.CountMatching

/-! A bounded moment contrast with positive integral produces actual
globally rare sign laws, with an explicit strictly positive target gap. -/

noncomputable section
open MeasureTheory

namespace ThresholdHC.CapIdentification
open ThresholdHC.Tier6 (Gap SignLaw signMean)
open ThresholdHC.RareAboveTwo

theorem rare_priors_of_bounded_contrast (μ : Measure Gap) [IsProbabilityMeasure μ]
    (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (N : ℕ) (h : Gap → ℝ)
    (hh : Measurable h) (M : ℝ) (hM : 0 < M) (hb : ∀ d, |h d| ≤ M)
    (hmom : ∀ j : Fin ((N+1)/2), ∫ d, h d*(d:ℝ)^(2*j.val+1) ∂μ = 0)
    (hi : 0 < ∫ d, h d ∂μ) :
    ∃ qH qL : SignLaw, RarePrior μ ρ qH ∧ RarePrior μ ρ qL ∧
      OddMomentMatch μ qH qL N ∧
      signMean μ qH.val-signMean μ qL.val = ρ/(2*M)*(∫ d, h d ∂μ) ∧
      0 < signMean μ qH.val-signMean μ qL.val := by
  let ε := ρ/(4*M)
  have he : 0 < ε := div_pos hρ (by positivity)
  have heM : ε*M = ρ/4 := by dsimp [ε]; field_simp
  have heb (d : Gap) : |ε*h d| ≤ ρ/4 := by
    rw [abs_mul,abs_of_pos he]
    exact (mul_le_mul_of_nonneg_left (hb d) he.le).trans_eq heM
  have hplus (d : Gap) : ρ/4 ≤ ρ/2+ε*h d ∧ ρ/2+ε*h d ≤ 3*ρ/4 := by
    have hd := abs_le.mp (heb d)
    constructor <;> linarith
  have hminus (d : Gap) : ρ/4 ≤ ρ/2-ε*h d ∧ ρ/2-ε*h d ≤ 3*ρ/4 := by
    have hd := abs_le.mp (heb d)
    constructor <;> linarith
  let qH : SignLaw := ⟨fun d => ρ/2+ε*h d,
    ⟨measurable_const.add (measurable_const.mul hh),fun d =>
      ⟨by linarith [(hplus d).1],by linarith [(hplus d).2]⟩⟩⟩
  let qL : SignLaw := ⟨fun d => ρ/2-ε*h d,
    ⟨measurable_const.sub (measurable_const.mul hh),fun d =>
      ⟨by linarith [(hminus d).1],by linarith [(hminus d).2]⟩⟩⟩
  have hInt : Integrable h μ := Integrable.of_bound hh.aestronglyMeasurable M
    (Filter.Eventually.of_forall (fun d => by simpa only [Real.norm_eq_abs] using hb d))
  have hHi : Integrable qH.val μ := (integrable_const _).add (hInt.const_mul ε)
  have hLi : Integrable qL.val μ := (integrable_const _).sub (hInt.const_mul ε)
  have hHrare : RarePrior μ ρ qH := by
    have hu := integral_mono hHi (integrable_const (3*ρ/4)) (fun d => (hplus d).2)
    simp only [integral_const,probReal_univ,smul_eq_mul,one_mul] at hu
    change (∫ d, qH.val d ∂μ) ≤ ρ
    linarith
  have hLrare : RarePrior μ ρ qL := by
    have hu := integral_mono hLi (integrable_const (3*ρ/4)) (fun d => (hminus d).2)
    simp only [integral_const,probReal_univ,smul_eq_mul,one_mul] at hu
    change (∫ d, qL.val d ∂μ) ≤ ρ
    linarith
  have hdiff (d : Gap) : qH.val d-qL.val d = (2*ε)*h d := by dsimp [qH,qL]; ring
  have hgap : signMean μ qH.val-signMean μ qL.val = (2*ε)*(∫ d, h d ∂μ) := by
    rw [signMean,signMean,← integral_sub hHi hLi]
    simp_rw [hdiff]
    exact integral_const_mul _ _
  refine ⟨qH,qL,hHrare,hLrare,?_,?_,?_⟩
  · intro j
    simp_rw [hdiff,mul_assoc,integral_const_mul,hmom j,mul_zero]
  · rw [hgap]
    congr 1
    dsimp [ε]
    field_simp
    ring
  · rw [hgap]
    exact mul_pos (mul_pos (by norm_num) he) hi

end ThresholdHC.CapIdentification
