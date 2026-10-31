import ThresholdHC.CriticalEntropy.PopulationCompactness
import ThresholdHC.RareAboveTwo.Model

/-! Compact convex moment images of the paper's actual rarity class
0 <= q <= 1, integral(q) <= rho. The half-bounded auxiliary dual geometry
is used only through the exact change of variables q -> q/2. -/

noncomputable section
open MeasureTheory Set

namespace ThresholdHC.StoppingProgram
open ThresholdHC.Tier6 (Gap SignLaw signMean)
open ThresholdHC.RareAboveTwo ThresholdHC.CriticalEntropy

def rareMomentSet {I : Type} (μ : Measure Gap) (ρ : ℝ) (g : I → Lp ℝ 2 μ) (b : I → ℝ) : Set (I → ℝ) :=
  {v | ∃ q : SignLaw, RarePrior μ ρ q ∧ ∀ i, v i = (∫ d, q.val d*g i d ∂μ)+b i}

theorem rareMomentSet_eq_half_image {I : Type} (μ : Measure Gap) [IsProbabilityMeasure μ]
    (ρ : ℝ) (g : I → Lp ℝ 2 μ) (b : I → ℝ) :
    rareMomentSet μ ρ g b = boundedPriorMomentSet μ (ρ/2) (fun i => (2:ℝ) • g i) b := by
  ext v
  constructor
  · rintro ⟨q,hq,hv⟩
    let qhalf : Gap → unitInterval := fun d => ⟨q.val d/2,
      by constructor <;> linarith [(q.property.2 d).1,(q.property.2 d).2]⟩
    refine ⟨qhalf,(q.property.1.div_const 2).subtype_mk,?_,?_,?_⟩
    · intro d
      change q.val d/2 ≤ 1/2
      linarith [(q.property.2 d).2]
    · change (∫ d, q.val d/2 ∂μ) ≤ ρ/2
      rw [integral_div]
      exact div_le_div_of_nonneg_right hq (by norm_num)
    · intro i
      rw [hv i]
      congr 1
      apply integral_congr_ae
      filter_upwards [Lp.coeFn_smul (2:ℝ) (g i)] with d hd
      rw [hd]
      change q.val d*g i d = q.val d/2*(2*g i d)
      ring
  · rintro ⟨q,hqm,hhalf,hq,hv⟩
    let qfull : SignLaw := ⟨fun d => 2*(q d:ℝ),
      ⟨measurable_const.mul (measurable_subtype_coe.comp hqm),fun d =>
        ⟨mul_nonneg (by norm_num) (q d).property.1,by linarith [hhalf d]⟩⟩⟩
    refine ⟨qfull,?_,?_⟩
    · change (∫ d, 2*(q d:ℝ) ∂μ) ≤ ρ
      rw [integral_const_mul]
      linarith
    · intro i
      rw [hv i]
      congr 1
      apply integral_congr_ae
      filter_upwards [Lp.coeFn_smul (2:ℝ) (g i)] with d hd
      rw [hd]
      change (q d:ℝ)*(2*g i d) = (2*(q d:ℝ))*g i d
      ring

theorem rareMomentSet_compact_convex {I : Type} (μ : Measure Gap) [IsProbabilityMeasure μ]
    (ρ : ℝ) (g : I → Lp ℝ 2 μ) (b : I → ℝ) :
    IsCompact (rareMomentSet μ ρ g b) ∧ Convex ℝ (rareMomentSet μ ρ g b) := by
  rw [rareMomentSet_eq_half_image]
  exact boundedPriorMomentSet_compact_convex μ (ρ/2) (fun i => (2:ℝ) • g i) b

end ThresholdHC.StoppingProgram
