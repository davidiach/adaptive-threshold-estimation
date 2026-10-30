import ThresholdHC.CapIdentification.MomentCoordinates
import ThresholdHC.CapIdentification.FiniteSupportTarget

/-! The cap-N moment-matching diameter is an attained maximum over actual
rare sign priors. Compactness is proved, rather than assumed as an oracle. -/

noncomputable section
open MeasureTheory Set

namespace ThresholdHC.CapIdentification
open ThresholdHC.Tier6 (Gap SignLaw signMean signMean_bounds)
open ThresholdHC.RareAboveTwo

def matchingCoordinatePairs (μ : Measure Gap) (ρ : ℝ) (N : ℕ) :
    Set ((Option (Fin ((N+1)/2)) → ℝ) × (Option (Fin ((N+1)/2)) → ℝ)) :=
  (polynomialMomentSet μ ρ (momentPolynomial ((N+1)/2)) ×ˢ
    polynomialMomentSet μ ρ (momentPolynomial ((N+1)/2))) ∩
    {z | ∀ j : Fin ((N+1)/2), z.1 (some j) = z.2 (some j)}

theorem matchingCoordinatePairs_compact (μ : Measure Gap) [IsProbabilityMeasure μ] (ρ : ℝ) (N : ℕ) :
    IsCompact (matchingCoordinatePairs μ ρ N) := by
  have hK := (polynomialMomentSet_compact_convex μ ρ (momentPolynomial ((N+1)/2))).1
  apply (hK.prod hK).inter_right
  simp only [ofPred_forall]
  apply isClosed_iInter
  intro j
  exact isClosed_eq ((continuous_apply (some j)).comp continuous_fst)
    ((continuous_apply (some j)).comp continuous_snd)

theorem matchingCoordinatePairs_nonempty (μ : Measure Gap) [IsProbabilityMeasure μ]
    {ρ : ℝ} (hρ : 0 ≤ ρ) (N : ℕ) : (matchingCoordinatePairs μ ρ N).Nonempty := by
  let q : SignLaw := ⟨fun _ => 0,measurable_const,fun _ => ⟨le_rfl,by norm_num⟩⟩
  have hq : RarePrior μ ρ q := by simpa only [RarePrior,signMean,q,integral_zero] using hρ
  let v := momentCoordinates μ q ((N+1)/2)
  have hv := momentCoordinates_mem μ ρ q hq ((N+1)/2)
  exact ⟨(v,v),⟨⟨hv,hv⟩,fun _ => rfl⟩⟩

theorem exists_max_matching_gap (μ : Measure Gap) [IsProbabilityMeasure μ]
    {ρ : ℝ} (hρ : 0 ≤ ρ) (N : ℕ) :
    ∃ qH qL : SignLaw, RarePrior μ ρ qH ∧ RarePrior μ ρ qL ∧ OddMomentMatch μ qH qL N ∧
      ∀ rH rL : SignLaw, RarePrior μ ρ rH → RarePrior μ ρ rL → OddMomentMatch μ rH rL N →
        signMean μ rH.val-signMean μ rL.val ≤ signMean μ qH.val-signMean μ qL.val := by
  have hc : Continuous (fun z : (Option (Fin ((N+1)/2)) → ℝ) × (Option (Fin ((N+1)/2)) → ℝ) =>
      z.1 none-z.2 none) := ((continuous_apply none).comp continuous_fst).sub
        ((continuous_apply none).comp continuous_snd)
  obtain ⟨z,hz,hmax⟩ := (matchingCoordinatePairs_compact μ ρ N).exists_isMaxOn
    (matchingCoordinatePairs_nonempty μ hρ N) hc.continuousOn
  obtain ⟨qH,hH,hvH⟩ := polynomialMomentSet_coordinates μ ρ ((N+1)/2) z.1 hz.1.1
  obtain ⟨qL,hL,hvL⟩ := polynomialMomentSet_coordinates μ ρ ((N+1)/2) z.2 hz.1.2
  have hm : OddMomentMatch μ qH qL N := by
    apply (momentCoordinates_match_iff μ qH qL N).mp
    intro j
    rw [← hvH,← hvL]
    exact hz.2 j
  refine ⟨qH,qL,hH,hL,hm,?_⟩
  intro rH rL hrH hrL hrm
  have hpair : (momentCoordinates μ rH ((N+1)/2),momentCoordinates μ rL ((N+1)/2)) ∈
      matchingCoordinatePairs μ ρ N :=
    ⟨⟨momentCoordinates_mem μ ρ rH hrH _,momentCoordinates_mem μ ρ rL hrL _⟩,
      (momentCoordinates_match_iff μ rH rL N).mpr hrm⟩
  have hh := hmax hpair
  change momentCoordinates μ rH ((N+1)/2) none-momentCoordinates μ rL ((N+1)/2) none ≤
    z.1 none-z.2 none at hh
  simpa only [hvH,hvL,momentCoordinates_none] using hh

def matchingTargetGaps (μ : Measure Gap) (ρ : ℝ) (N : ℕ) : Set ℝ :=
  {δ | ∃ qH qL : SignLaw, RarePrior μ ρ qH ∧ RarePrior μ ρ qL ∧ OddMomentMatch μ qH qL N ∧
    δ = signMean μ qH.val-signMean μ qL.val}

def capDiameter (μ : Measure Gap) (ρ : ℝ) (N : ℕ) : ℝ := sSup (matchingTargetGaps μ ρ N)

theorem capDiameter_attained (μ : Measure Gap) [IsProbabilityMeasure μ]
    {ρ : ℝ} (hρ : 0 ≤ ρ) (N : ℕ) :
    ∃ qH qL : SignLaw, RarePrior μ ρ qH ∧ RarePrior μ ρ qL ∧ OddMomentMatch μ qH qL N ∧
      capDiameter μ ρ N = signMean μ qH.val-signMean μ qL.val ∧
      ∀ rH rL : SignLaw, RarePrior μ ρ rH → RarePrior μ ρ rL → OddMomentMatch μ rH rL N →
        signMean μ rH.val-signMean μ rL.val ≤ capDiameter μ ρ N := by
  obtain ⟨qH,qL,hH,hL,hm,hmax⟩ := exists_max_matching_gap μ hρ N
  have hmem : signMean μ qH.val-signMean μ qL.val ∈ matchingTargetGaps μ ρ N := ⟨qH,qL,hH,hL,hm,rfl⟩
  have hbound : ∀ x ∈ matchingTargetGaps μ ρ N, x ≤ signMean μ qH.val-signMean μ qL.val := by
    rintro x ⟨rH,rL,hrH,hrL,hrm,rfl⟩
    exact hmax rH rL hrH hrL hrm
  have he : capDiameter μ ρ N = signMean μ qH.val-signMean μ qL.val :=
    le_antisymm (csSup_le ⟨_,hmem⟩ hbound) (le_csSup ⟨_,hbound⟩ hmem)
  exact ⟨qH,qL,hH,hL,hm,he,fun rH rL hrH hrL hrm => (hmax rH rL hrH hrL hrm).trans_eq he.symm⟩

theorem capDiameter_bounds (μ : Measure Gap) [IsProbabilityMeasure μ]
    {ρ : ℝ} (hρ : 0 ≤ ρ) (N : ℕ) : 0 ≤ capDiameter μ ρ N ∧ capDiameter μ ρ N ≤ ρ := by
  obtain ⟨qH,qL,hH,_,_,he,hmax⟩ := capDiameter_attained μ hρ N
  constructor
  · have hh := hmax qH qH hH hH (by intro j; simp)
    simpa only [sub_self] using hh
  · rw [he]
    have hn := (signMean_bounds μ qL).1
    change signMean μ qH.val ≤ ρ at hH
    linarith

end ThresholdHC.CapIdentification
