import ThresholdHC.DepthLegendre.Pair
import ThresholdHC.DepthObstruction.Full

/-! `thm:cap` of `research/2026-10-27-nonlinear-population/upper/proof-body.tex`
(lines 87-151), self-contained: the explicit pair of `depthPair` matches odd
moments through depth `2K`, so part 1 (`DepthObstruction.capped_transcript`)
gives equal seed-and-transcript laws for every procedure with per-coin cap `2K`,
and `DepthObstruction.equal_law_floor` gives the RMS floor `Δ_K/2`. Both members
of the pair are rare, so the floor also bounds `RareAboveTwo.rareRisk`. -/

noncomputable section
namespace ThresholdHC.DepthLegendre
open MeasureTheory
open scoped ENNReal
open ThresholdHC.Tier6 (Gap SignLaw signMean AdaptiveEstimator experimentLaw rootMeanRisk
  populationOutput)
open ThresholdHC.RareAboveTwo (RarePrior rareRisk)

/-- `thm:cap`: equal laws and the floor `ρ/(2(K+1)(2K+1))` under the per-coin cap `2K`. -/
theorem depthCapFloor : DepthCapFloorStatement := by
  intro R _ μ _ a ρ K A ha ha2 hρ hρ4 hK hm hcap
  obtain ⟨qH, qL, hqH, hqL, hH, hL, -, -, hdiff, hodd, -, -⟩ :=
    depthPair μ a ρ K ha ha2 hρ hρ4 hK hm
  have hlaw := DepthObstruction.capped_transcript R μ qH qL (2*K) A hodd hcap
  have hfloor := DepthObstruction.equal_law_floor R μ A qH qL hlaw
  have hpos : 0 < ρ / (((K:ℝ)+1) * (2*K+1)) := by positivity
  have he : ρ / (((K:ℝ)+1) * (2*K+1)) / 2 = ρ / (2*((K:ℝ)+1)*(2*K+1)) := by
    field_simp
  rw [hdiff, abs_of_pos hpos, he] at hfloor
  refine ⟨⟨qH, qL, hqH, hqL, hH, hL, hlaw, hfloor⟩, hfloor.trans (max_le ?_ ?_)⟩
  · unfold rareRisk
    exact le_iSup₂ (f := fun (q : SignLaw) (_ : RarePrior μ ρ q) =>
      rootMeanRisk (experimentLaw μ A q) (populationOutput A) (signMean μ q.val)) qH hH
  · unfold rareRisk
    exact le_iSup₂ (f := fun (q : SignLaw) (_ : RarePrior μ ρ q) =>
      rootMeanRisk (experimentLaw μ A q) (populationOutput A) (signMean μ q.val)) qL hL

end ThresholdHC.DepthLegendre
