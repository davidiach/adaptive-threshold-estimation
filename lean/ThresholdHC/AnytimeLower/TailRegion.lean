
import ThresholdHC.AnytimeLower.TailLimits

noncomputable section
open MeasureTheory Real Set Filter
open scoped ENNReal Topology
namespace ThresholdHC.AnytimeLower
open ThresholdHC.Tier6 ThresholdHC.EntropyTailQuantile

theorem smallGapMass_tendsto_zero (μ : Measure Gap) [IsFiniteMeasure μ] :
    Tendsto (fun j => μ.real {d : Gap | (d:ℝ) ≤ geometricScale (1/4) j}) atTop (𝓝 0) := by
  let S (j : ℕ) := {d : Gap | (d:ℝ) ≤ geometricScale (1/4) j}
  have hS (j : ℕ) : MeasurableSet (S j) := measurableSet_le measurable_subtype_coe measurable_const
  let F (j : ℕ) := (S j).indicator (fun _ : Gap => (1:ℝ))
  have hm (j : ℕ) : Measurable (F j) := measurable_const.indicator (hS j)
  have hb (j : ℕ) : ∀ᵐ d ∂μ, ‖F j d‖ ≤ (1:ℝ) := by
    apply ae_of_all
    intro d
    by_cases hd : d ∈ S j <;> simp [F,hd]
  have hl (d : Gap) : Tendsto (fun j => F j d) atTop (𝓝 (0:ℝ)) := by
    have he := (geometricScale_tendsto_zero (1/4)).eventually (gt_mem_nhds d.property.1)
    apply tendsto_congr' (he.mono (fun j hj => show F j d = (0:ℝ) by
      exact indicator_of_notMem (show d ∉ S j from not_le_of_gt hj) _)) |>.mpr
    exact tendsto_const_nhds
  have ht := tendsto_integral_of_dominated_convergence (μ:=μ) (fun _ : Gap => (1:ℝ))
    (F:=F) (f:=fun _ => (0:ℝ)) (fun j => (hm j).aestronglyMeasurable)
    (integrable_const 1) hb (ae_of_all _ hl)
  have hi (j : ℕ) : (∫ d, F j d ∂μ) = μ.real (S j) := by
    simpa only [smul_eq_mul,mul_one] using integral_indicator_const (μ:=μ) (1:ℝ) (hS j)
  simpa only [hi,integral_zero] using ht

theorem smallGapMass_pos_of_not_integrable (μ : Measure Gap) [IsFiniteMeasure μ]
    (hI : ¬Integrable (fun d : Gap => (d:ℝ)⁻¹) μ) {τ : ℝ} (hτ : 0 < τ) :
    0 < μ {d : Gap | (d:ℝ) ≤ τ} := by
  by_contra hh
  have hz : μ {d : Gap | (d:ℝ) ≤ τ} = 0 := le_antisymm (not_lt.mp hh) bot_le
  apply hI
  apply inverse_integrable_of_support μ hτ
  have ha : ∀ᵐ d : Gap ∂μ, ¬(d:ℝ) ≤ τ := by
    simpa only [ae_iff,not_not] using hz
  exact ha.mono (fun d hd => (not_le.mp hd).le)

theorem exists_smallGapRegion (μ : Measure Gap) [IsFiniteMeasure μ]
    (hI : ¬Integrable (fun d : Gap => (d:ℝ)⁻¹) μ) {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ τ : ℝ, 0 < τ ∧ τ ≤ 1/4 ∧ 0 < μ {d : Gap | (d:ℝ) ≤ τ} ∧
      μ.real {d : Gap | (d:ℝ) ≤ τ} ≤ ρ := by
  have he := (smallGapMass_tendsto_zero μ).eventually (gt_mem_nhds hρ)
  obtain ⟨j,hj⟩ := he.exists
  refine ⟨geometricScale (1/4) j,geometricScale_pos (by norm_num) j,?_,
    smallGapMass_pos_of_not_integrable μ hI (geometricScale_pos (by norm_num) j),hj.le⟩
  have hm := geometricScale_antitone (by norm_num : (0:ℝ) ≤ 1/4) (Nat.zero_le j)
  simpa [geometricScale] using hm

end ThresholdHC.AnytimeLower
