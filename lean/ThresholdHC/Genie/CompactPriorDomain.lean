import ThresholdHC.Genie.InfiniteCoordinates
import ThresholdHC.Genie.DualTopology

/-! Actual rare priors representing the common compact image of all finite
count moments. The chosen representatives need not vary continuously; their
observable moments do, which is exactly what the dual objective uses. -/

noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace ThresholdHC.Genie
open ThresholdHC.Tier6 ThresholdHC.RareAboveTwo ThresholdHC.StoppingProgram
open ThresholdHC.CapIdentification

abbrev PriorDomain (μ : Measure Gap) (ρ : ℝ) :=
  {u : AllFourCoordinates // u ∈ allFourPriorMomentImage μ ρ}

instance priorDomainCompact (μ : Measure Gap) [IsProbabilityMeasure μ] (ρ : ℝ) :
    CompactSpace (PriorDomain μ ρ) :=
  isCompact_iff_compactSpace.mp (allFourPriorMomentImage_compact μ ρ)

def priorPoint (μ : Measure Gap) (ρ : ℝ) (Q : FourPriors) (hQ : Admissible μ ρ Q) :
    PriorDomain μ ρ :=
  ⟨allFourPriorCoordinates μ Q,(allFourPriorMomentImage_iff μ ρ _).mpr ⟨Q,hQ,rfl⟩⟩

theorem priorDomain_nonempty (μ : Measure Gap) {ρ : ℝ} (hρ : 0 ≤ ρ) :
    Nonempty (PriorDomain μ ρ) := by
  have hq : RarePrior μ ρ nullSignLaw := by
    simpa [RarePrior,signMean,nullSignLaw] using hρ
  exact ⟨priorPoint μ ρ ⟨nullSignLaw,nullSignLaw,nullSignLaw,nullSignLaw⟩ ⟨hq,hq,hq,hq⟩⟩

def domainPriors (μ : Measure Gap) (ρ : ℝ) (x : PriorDomain μ ρ) : FourPriors :=
  Classical.choose ((allFourPriorMomentImage_iff μ ρ x.val).mp x.property)

theorem domainPriors_admissible (μ : Measure Gap) (ρ : ℝ) (x : PriorDomain μ ρ) :
    Admissible μ ρ (domainPriors μ ρ x) :=
  (Classical.choose_spec ((allFourPriorMomentImage_iff μ ρ x.val).mp x.property)).1

theorem domainPriors_coordinates (μ : Measure Gap) (ρ : ℝ) (x : PriorDomain μ ρ) :
    allFourPriorCoordinates μ (domainPriors μ ρ x) = x.val :=
  (Classical.choose_spec ((allFourPriorMomentImage_iff μ ρ x.val).mp x.property)).2.symm

theorem dualRatio_coordinates_congr (μ : Measure Gap) (B : ℝ) (N : ℕ)
    (Q R : FourPriors) (h : allFourPriorCoordinates μ Q = allFourPriorCoordinates μ R) :
    dualRatio μ B N Q = dualRatio μ B N R := by
  have hl := congrArg (fun u : AllFourCoordinates => u.1.1) h
  have hh := congrArg (fun u : AllFourCoordinates => u.1.2) h
  have hv := congrArg (fun u : AllFourCoordinates => u.2.1) h
  have hw := congrArg (fun u : AllFourCoordinates => u.2.2) h
  have hml : signMean μ Q.low.val = signMean μ R.low.val := congrFun hl none
  have hmh : signMean μ Q.high.val = signMean μ R.high.val := congrFun hh none
  have hcl (s : CountState N) : countCoefficient μ Q.low s = countCoefficient μ R.low s :=
    congrFun hl (some ⟨N,s⟩)
  have hch (s : CountState N) : countCoefficient μ Q.high s = countCoefficient μ R.high s :=
    congrFun hh (some ⟨N,s⟩)
  have hcv (s : CountState N) : countCoefficient μ Q.variance s = countCoefficient μ R.variance s :=
    congrFun hv (some ⟨N,s⟩)
  have hcw (s : CountState N) : countCoefficient μ Q.work s = countCoefficient μ R.work s :=
    congrFun hw (some ⟨N,s⟩)
  simp only [dualRatio,informationRatio,flowInformation,countMean,hml,hmh,hcl,hch,hcv,hcw]

theorem domain_dualRatio_upperSemicontinuous (μ : Measure Gap) [IsProbabilityMeasure μ]
    (ρ B : ℝ) (N : ℕ) :
    UpperSemicontinuous (fun x : PriorDomain μ ρ => dualRatio μ B N (domainPriors μ ρ x)) := by
  have hl (i : AllCountIndex) : Continuous (fun x : PriorDomain μ ρ =>
      allPriorCoordinates μ (domainPriors μ ρ x).low i) := by
    have he (x : PriorDomain μ ρ) := congrArg (fun u : AllFourCoordinates => u.1.1 i)
      (domainPriors_coordinates μ ρ x)
    simp only [allFourPriorCoordinates] at he
    simp_rw [he]
    exact (continuous_apply i).comp (continuous_fst.comp (continuous_fst.comp continuous_subtype_val))
  have hh (i : AllCountIndex) : Continuous (fun x : PriorDomain μ ρ =>
      allPriorCoordinates μ (domainPriors μ ρ x).high i) := by
    have he (x : PriorDomain μ ρ) := congrArg (fun u : AllFourCoordinates => u.1.2 i)
      (domainPriors_coordinates μ ρ x)
    simp only [allFourPriorCoordinates] at he
    simp_rw [he]
    exact (continuous_apply i).comp (continuous_snd.comp (continuous_fst.comp continuous_subtype_val))
  have hv (i : AllCountIndex) : Continuous (fun x : PriorDomain μ ρ =>
      allPriorCoordinates μ (domainPriors μ ρ x).variance i) := by
    have he (x : PriorDomain μ ρ) := congrArg (fun u : AllFourCoordinates => u.2.1 i)
      (domainPriors_coordinates μ ρ x)
    simp only [allFourPriorCoordinates] at he
    simp_rw [he]
    exact (continuous_apply i).comp (continuous_fst.comp (continuous_snd.comp continuous_subtype_val))
  have hw (i : AllCountIndex) : Continuous (fun x : PriorDomain μ ρ =>
      allPriorCoordinates μ (domainPriors μ ρ x).work i) := by
    have he (x : PriorDomain μ ρ) := congrArg (fun u : AllFourCoordinates => u.2.2 i)
      (domainPriors_coordinates μ ρ x)
    simp only [allFourPriorCoordinates] at he
    simp_rw [he]
    exact (continuous_apply i).comp (continuous_snd.comp (continuous_snd.comp continuous_subtype_val))
  exact dualRatio_upperSemicontinuous μ B N (domainPriors μ ρ)
    (hl none) (hh none) (fun s => hl (some ⟨N,s⟩)) (fun s => hh (some ⟨N,s⟩))
    (fun s => hv (some ⟨N,s⟩)) (fun s => hw (some ⟨N,s⟩))

theorem dualValue_eq_domain_sup (μ : Measure Gap) (ρ B : ℝ) (N : ℕ) :
    dualValue μ ρ B N = ⨆ x : PriorDomain μ ρ, dualRatio μ B N (domainPriors μ ρ x) := by
  unfold dualValue
  apply le_antisymm
  · apply iSup_le
    intro Q
    apply iSup_le
    intro hQ
    let x := priorPoint μ ρ Q hQ
    have he : dualRatio μ B N (domainPriors μ ρ x) = dualRatio μ B N Q :=
      dualRatio_coordinates_congr μ B N _ _ (domainPriors_coordinates μ ρ x)
    rw [←he]
    exact le_iSup (fun y : PriorDomain μ ρ => dualRatio μ B N (domainPriors μ ρ y)) x
  · apply iSup_le
    intro x
    exact le_iSup_of_le (domainPriors μ ρ x)
      (le_iSup_of_le (domainPriors_admissible μ ρ x) le_rfl)

end ThresholdHC.Genie
