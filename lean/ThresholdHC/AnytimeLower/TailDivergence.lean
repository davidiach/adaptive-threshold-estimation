
import ThresholdHC.AnytimeLower.TailLimits

noncomputable section
open MeasureTheory Real Set Filter
open scoped ENNReal Topology
namespace ThresholdHC.AnytimeLower
open ThresholdHC.Tier6

def inverseTail (τ : ℝ) (d : Gap) : ℝ := if (d:ℝ) ≤ τ then (d:ℝ)⁻¹ else 0

theorem measurable_inverseTail (τ : ℝ) : Measurable (inverseTail τ) :=
  Measurable.ite (measurableSet_le measurable_subtype_coe measurable_const)
    measurable_subtype_coe.inv measurable_const

theorem inverseTail_nonneg (τ : ℝ) (d : Gap) : 0 ≤ inverseTail τ d := by
  unfold inverseTail
  split_ifs
  · exact inv_nonneg.mpr d.property.1.le
  · exact le_rfl

theorem inverseTail_not_integrable (μ : Measure Gap) [IsFiniteMeasure μ]
    (hI : ¬Integrable (fun d : Gap => (d:ℝ)⁻¹) μ) {τ : ℝ} (hτ : 0 < τ) :
    ¬Integrable (inverseTail τ) μ := by
  intro hi
  let G : Gap → ℝ := fun d => if (d:ℝ) ≤ τ then 0 else (d:ℝ)⁻¹
  have hm : Measurable G := Measurable.ite
    (measurableSet_le measurable_subtype_coe measurable_const) measurable_const measurable_subtype_coe.inv
  have hg : Integrable G μ := by
    apply (integrable_const τ⁻¹).mono' hm.aestronglyMeasurable
    apply ae_of_all
    intro d
    by_cases hd : (d:ℝ) ≤ τ
    · simp [G,hd,inv_nonneg.mpr hτ.le]
    · simp only [G,ite_eq_right hd,Real.norm_of_nonneg (inv_nonneg.mpr d.property.1.le)]
      exact inv_anti₀ hτ (not_le.mp hd).le
  apply hI
  convert hi.add hg using 1
  funext d
  dsimp [inverseTail,G]
  split_ifs <;> simp

theorem normalized_profile_eq {τ h : ℝ} (hh : 0 < h) (d : Gap) :
    tailProfile τ h d/h = if (d:ℝ) ≤ τ then min h⁻¹ (d:ℝ)⁻¹ else 0 := by
  unfold tailProfile
  split_ifs
  · rw [← min_div_div_right hh.le]
    congr 1
    · exact one_div h
    · field_simp
  · simp

theorem normalized_profile_mono (τ : ℝ) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (d : Gap) :
    tailProfile τ b d/b ≤ tailProfile τ a d/a := by
  rw [normalized_profile_eq (ha.trans_le hab),normalized_profile_eq ha]
  split_ifs
  · exact min_le_min_right _ (inv_anti₀ ha hab)
  · rfl

theorem normalized_mass_mono (μ : Measure Gap) [IsFiniteMeasure μ]
    (τ : ℝ) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    profileMass μ τ b/b ≤ profileMass μ τ a/a := by
  have hi := integral_mono ((integrable_tailProfile μ τ (ha.trans_le hab).le).div_const b)
    ((integrable_tailProfile μ τ ha.le).div_const a) (normalized_profile_mono τ ha hab)
  simpa only [profileMass,integral_div] using hi

/-- Infinite inverse moment makes the normalized small-gap mass eventually
exceed every fixed coefficient. This is an arbitrary-law limit, not a finite
profile regression. -/
theorem profileMass_dominates_linear (μ : Measure Gap) [IsFiniteMeasure μ]
    (hI : ¬Integrable (fun d : Gap => (d:ℝ)⁻¹) μ) {τ : ℝ} (hτ : 0 < τ) (C : ℝ) :
    ∃ h₀ : ℝ, 0 < h₀ ∧ ∀ h : ℝ, 0 < h → h ≤ h₀ → C*h ≤ profileMass μ τ h := by
  let s := geometricScale τ
  let F (j : ℕ) (d : Gap) := tailProfile τ (s j) d/s j
  have hs (j : ℕ) : 0 < s j := geometricScale_pos hτ j
  have hf (j : ℕ) : Integrable (F j) μ :=
    (integrable_tailProfile μ τ (hs j).le).div_const _
  have hnn (j : ℕ) (d : Gap) : 0 ≤ F j d :=
    div_nonneg (tailProfile_bounds τ (hs j).le d).1 (hs j).le
  have hmono (d : Gap) : Monotone (fun j => ENNReal.ofReal (F j d)) := by
    intro i j hij
    exact ENNReal.ofReal_le_ofReal (normalized_profile_mono τ (hs j)
      (geometricScale_antitone hτ.le hij) d)
  have hlim (d : Gap) : Tendsto (fun j => F j d) atTop (𝓝 (inverseTail τ d)) := by
    have he := (geometricScale_tendsto_zero τ).eventually (gt_mem_nhds d.property.1)
    apply tendsto_congr' (he.mono (fun j hj => show F j d = inverseTail τ d by
      dsimp [F]
      rw [normalized_profile_eq (hs j)]
      unfold inverseTail
      split_ifs
      · exact min_eq_right (inv_anti₀ (hs j) hj.le)
      · rfl)) |>.mpr
    exact tendsto_const_nhds
  have ht := lintegral_tendsto_of_tendsto_of_monotone
    (fun j => (hf j).aestronglyMeasurable.aemeasurable.ennreal_ofReal)
    (ae_of_all μ hmono) (ae_of_all μ (fun d => (ENNReal.continuous_ofReal.tendsto _).comp (hlim d)))
  have hinf : (∫⁻ d, ENNReal.ofReal (inverseTail τ d) ∂μ) = ∞ := by
    by_contra hh
    apply inverseTail_not_integrable μ hI hτ
    refine ⟨(measurable_inverseTail τ).aestronglyMeasurable,?_⟩
    exact (hasFiniteIntegral_iff_ofReal (ae_of_all _ (inverseTail_nonneg τ))).mpr (lt_top_iff_ne_top.mpr hh)
  have heq (j : ℕ) : (∫⁻ d, ENNReal.ofReal (F j d) ∂μ) =
      ENNReal.ofReal (profileMass μ τ (s j)/s j) := by
    rw [← ofReal_integral_eq_lintegral_ofReal (hf j) (ae_of_all _ (hnn j))]
    congr 1
    exact integral_div _ _
  rw [hinf] at ht
  simp only [heq] at ht
  obtain ⟨j,hj⟩ := (ht.eventually (lt_mem_nhds (ENNReal.ofReal_lt_top (r:=C)))).exists
  have hb : C ≤ profileMass μ τ (s j)/s j :=
    (ENNReal.ofReal_le_ofReal_iff (div_nonneg (profileMass_nonneg μ τ (hs j).le) (hs j).le)).mp hj.le
  refine ⟨s j,hs j,?_⟩
  intro h hh hhj
  exact (le_div_iff₀ hh).mp (hb.trans (normalized_mass_mono μ τ hh hhj))

end ThresholdHC.AnytimeLower
