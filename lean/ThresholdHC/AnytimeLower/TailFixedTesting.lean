import ThresholdHC.AnytimeLower.PrefixTesting
import ThresholdHC.AnytimeLower.TailFamily

noncomputable section
open MeasureTheory InformationTheory Real Set
open scoped ENNReal
namespace ThresholdHC.AnytimeLower
open ThresholdHC.Tier3 ThresholdHC.Tier6 ThresholdHC.RareAboveTwo

/-- A single capped inverse-gap perturbation gives a fixed-prefix test within
the same online experiment. -/
theorem tail_fixed_radius {R : Type} [MeasurableSpace R]
    (μ : Measure Gap) [IsProbabilityMeasure μ] (A : AdaptiveEstimator R)
    (H : ∀ n, R × Prefix n → ℝ) (hH : ∀ n, Measurable (H n))
    {τ ρ δ ε : ℝ} (hτq : τ ≤ 1/4) (hε : 0 ≤ ε)
    (hrare : μ.real {d : Gap | (d:ℝ) ≤ τ} ≤ ρ)
    (hd : δ ≤ 1/4) (t : ℕ → ℝ) (hacc : OnlineAccuracy μ A H ρ δ t)
    (n : ℕ) (hn : (n:ℝ)*ε^2 < 1/2) :
    profileMass μ τ ε/64 ≤ t n := by
  let r := tailAlternative τ ε 0 (by norm_num) hε
  have hk : klDiv (observablePrefixLaw μ A r n) (observablePrefixLaw μ A (tailBase τ) n) ≤
      ENNReal.ofReal ((n:ℝ)*ε^2) := by
    apply tail_observable_prefix_kl μ A r (tailBase τ) hε
    · intro d
      by_cases hd : (d:ℝ) ≤ τ
      · right
        have hc := tailAlternative_central τ (show (0:ℝ) ≤ 0 by norm_num) hε d hd
        refine ⟨hd.trans hτq,⟨hc.1,by linarith [hc.2]⟩,?_⟩
        norm_num [tailBase,hd]
      · left
        simp [r,tailAlternative,tailBase,tailProfile,hd]
    · exact tailAlternative_contrast τ _ hε
  have ht := prefix_two_point_radius μ A H hH hd t hacc (tailBase τ) r
    (tailBase_rare μ hrare) (tailAlternative_rare μ _ hε hrare) n
    (hk.trans_lt ((ENNReal.ofReal_lt_ofReal_iff (by norm_num : (0:ℝ) < 1/2)).mpr hn))
  have hm := tailAlternative_mean μ τ (show (0:ℝ) ≤ 0 by norm_num) hε
  have hz : profileMass μ τ 0 = 0 := by simp [profileMass,tailProfile]
  change signMean μ r.val-signMean μ (tailBase τ).val = _ at hm
  rw [hm,hz] at ht
  linarith

end ThresholdHC.AnytimeLower
