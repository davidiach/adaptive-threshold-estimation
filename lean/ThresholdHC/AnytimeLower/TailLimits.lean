
import ThresholdHC.AnytimeLower.TailProfiles
import ThresholdHC.StoppingProgram.RaritySupport
import Mathlib.MeasureTheory.Integral.DominatedConvergence

noncomputable section
open MeasureTheory Real Set Filter
open scoped ENNReal Topology
namespace ThresholdHC.AnytimeLower
open ThresholdHC.Tier6 ThresholdHC.RareAboveTwo ThresholdHC.StoppingProgram

theorem profileMass_pos (μ : Measure Gap) [IsFiniteMeasure μ]
    {τ h : ℝ} (hh : 0 < h) (hμ : 0 < μ {d : Gap | (d:ℝ) ≤ τ}) :
    0 < profileMass μ τ h := by
  apply (integral_pos_iff_support_of_nonneg (fun d => (tailProfile_bounds τ hh.le d).1)
    (integrable_tailProfile μ τ hh.le)).mpr
  apply hμ.trans_le
  apply measure_mono
  intro d hd
  change (d:ℝ) ≤ τ at hd
  change tailProfile τ h d ≠ 0
  rw [tailProfile,ite_eq_left hd]
  exact (lt_min (by norm_num : (0:ℝ) < 1) (div_pos hh d.property.1)).ne'

theorem profileMass_tendsto_zero (μ : Measure Gap) [IsFiniteMeasure μ]
    (τ : ℝ) (h : ℕ → ℝ) (hh : ∀ k, 0 ≤ h k) (hlim : Tendsto h atTop (𝓝 0)) :
    Tendsto (fun k => profileMass μ τ (h k)) atTop (𝓝 0) := by
  have hb (k : ℕ) : ∀ᵐ d ∂μ, ‖tailProfile τ (h k) d‖ ≤ (1:ℝ) :=
    ae_of_all _ (fun d => by
      rw [Real.norm_of_nonneg (tailProfile_bounds τ (hh k) d).1]
      exact (tailProfile_bounds τ (hh k) d).2)
  have hl : ∀ᵐ d ∂μ, Tendsto (fun k => tailProfile τ (h k) d) atTop (𝓝 (0:ℝ)) := by
    apply ae_of_all
    intro d
    by_cases hd : (d:ℝ) ≤ τ
    · simp only [tailProfile,ite_eq_left hd]
      have hz := ((tendsto_const_nhds : Tendsto (fun _ : ℕ => (1:ℝ)) atTop (𝓝 1)).min (hlim.div_const (d:ℝ)))
      simpa only [zero_div,min_eq_right (by norm_num : (0:ℝ) ≤ 1)] using hz
    · simpa only [tailProfile,ite_eq_right hd] using
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0:ℝ)) atTop (𝓝 0))
  have ht := tendsto_integral_of_dominated_convergence (fun _ : Gap => (1:ℝ))
    (fun k => (measurable_tailProfile τ (h k)).aestronglyMeasurable)
    (integrable_const 1) hb hl
  simpa only [profileMass,integral_zero] using ht

def geometricScale (τ : ℝ) (k : ℕ) : ℝ := τ*(1/4:ℝ)^k

theorem geometricScale_pos {τ : ℝ} (hτ : 0 < τ) (k : ℕ) :
    0 < geometricScale τ k := by unfold geometricScale; positivity

theorem geometricScale_antitone {τ : ℝ} (hτ : 0 ≤ τ) : Antitone (geometricScale τ) := by
  intro i j hij
  exact mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one (by norm_num) (by norm_num) hij) hτ

theorem geometricScale_tendsto_zero (τ : ℝ) :
    Tendsto (geometricScale τ) atTop (𝓝 0) := by
  change Tendsto (fun k : ℕ => τ*(1/4:ℝ)^k) atTop (𝓝 0)
  simpa only [mul_zero] using
    (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0:ℝ) ≤ 1/4)
      (by norm_num : (1/4:ℝ) < 1)).const_mul τ

theorem supported_prior_rare (μ : Measure Gap) [IsFiniteMeasure μ]
    (q : SignLaw) {τ ρ : ℝ} (hout : ∀ d : Gap, ¬(d:ℝ) ≤ τ → q.val d = 0)
    (hm : μ.real {d : Gap | (d:ℝ) ≤ τ} ≤ ρ) : RarePrior μ ρ q := by
  let S := {d : Gap | (d:ℝ) ≤ τ}
  have hs : MeasurableSet S := measurableSet_le measurable_subtype_coe measurable_const
  have hp : ∀ d, q.val d ≤ S.indicator (fun _ => (1:ℝ)) d := by
    intro d
    by_cases hd : d ∈ S
    · simpa only [indicator_of_mem hd] using (q.property.2 d).2
    · rw [indicator_of_notMem hd,hout d hd]
  have hi := integral_mono (integrable_sign_prior μ q)
    ((integrable_const (1:ℝ)).indicator hs) hp
  rw [integral_indicator_const _ hs] at hi
  change (∫ d, q.val d ∂μ) ≤ ρ
  simpa only [smul_eq_mul,mul_one] using hi.trans (by simpa only [smul_eq_mul,mul_one] using hm)

theorem tailBase_rare (μ : Measure Gap) [IsFiniteMeasure μ] {τ ρ : ℝ}
    (hm : μ.real {d : Gap | (d:ℝ) ≤ τ} ≤ ρ) : RarePrior μ ρ (tailBase τ) :=
  supported_prior_rare μ (tailBase τ) (fun d hd => by simp [tailBase,hd]) hm

theorem tailAlternative_rare (μ : Measure Gap) [IsFiniteMeasure μ] {τ a b ρ : ℝ}
    (hb : 0 ≤ b) (hab : b ≤ a) (hm : μ.real {d : Gap | (d:ℝ) ≤ τ} ≤ ρ) :
    RarePrior μ ρ (tailAlternative τ a b hb hab) :=
  supported_prior_rare μ _ (tailAlternative_outside τ hb hab) hm

end ThresholdHC.AnytimeLower
