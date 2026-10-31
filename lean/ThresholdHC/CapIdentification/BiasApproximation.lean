import ThresholdHC.CapIdentification.AffineCentering
import ThresholdHC.CapIdentification.DiameterConsequences

/-! Uniform affine bias arbitrarily close to half the attained matching
diameter, over the actual full rarity class. -/

noncomputable section
open MeasureTheory Set
open scoped BigOperators

namespace ThresholdHC.CapIdentification
open ThresholdHC.Tier6 (Gap SignLaw signMean)
open ThresholdHC.RareAboveTwo

theorem affine_bias_approximation (μ : Measure Gap) [IsProbabilityMeasure μ]
    {ρ : ℝ} (hρ : 0 ≤ ρ) (N : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ c : ℝ, ∃ w : Fin ((N+1)/2) → ℝ, ∀ q : SignLaw, RarePrior μ ρ q →
      |c+(∑ j, w j*momentCoordinates μ q ((N+1)/2) (some j))-signMean μ q.val| ≤
        (capDiameter μ ρ N+ε)/2 := by
  let K := polynomialMomentSet μ ρ (momentPolynomial ((N+1)/2))
  have hK := polynomialMomentSet_compact_convex μ ρ (momentPolynomial ((N+1)/2))
  have hKn : K.Nonempty := by
    obtain ⟨z,hz⟩ := matchingCoordinatePairs_nonempty μ hρ N
    exact ⟨z.1,hz.1.1⟩
  have hδ : ∀ x ∈ K, ∀ y ∈ K, (∀ j, x (some j) = y (some j)) →
      x none-y none ≤ capDiameter μ ρ N := by
    intro x hx y hy hxy
    obtain ⟨qH,hH,rfl⟩ := polynomialMomentSet_coordinates μ ρ ((N+1)/2) x hx
    obtain ⟨qL,hL,rfl⟩ := polynomialMomentSet_coordinates μ ρ ((N+1)/2) y hy
    obtain ⟨_,_,_,_,_,_,hmax⟩ := capDiameter_attained μ hρ N
    simpa only [momentCoordinates_none] using hmax qH qL hH hL
      ((momentCoordinates_match_iff μ qH qL N).mp hxy)
  obtain ⟨c,w,hw⟩ := compact_affine_bias K hKn hK.1 hK.2 (capDiameter μ ρ N) hδ hε
  exact ⟨c,w,fun q hq => by
    simpa only [momentCoordinates_none] using hw (momentCoordinates μ q ((N+1)/2))
      (momentCoordinates_mem μ ρ q hq _)⟩

end ThresholdHC.CapIdentification
