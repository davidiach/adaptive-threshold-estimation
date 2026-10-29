import ThresholdHC.RareAboveTwo.Margin
import ThresholdHC.Tier3.Optimizer

/-! The variational rate above the critical exponent. The upper bound holds
for the whole margin class; only the lower bound needs bounded support. -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace ThresholdHC.RareAboveTwo
open ThresholdHC.Tier6 ThresholdHC.Tier3

theorem rareObjective_le_rarity (μ : Measure Gap) [IsProbabilityMeasure μ]
    (ρ h : ℝ) (hh : 0 ≤ h) (v : Gap → ℝ) (hv : FeasibleAllocation μ ρ v) :
    rareObjective μ (fun d => (d : ℝ)) h v ≤ ρ := by
  apply le_trans _ hv.2.2
  exact integral_mono_ae
    (objective_integrable measurable_subtype_coe (ae_of_all _ (fun d => d.property.1)) hv.1 hv.2.1 hh)
    (integrable_feasible hv) (ae_of_all _ (fun _ => min_le_left _ _))

theorem rarePsi_supported_lower (μ : Measure Gap) [IsProbabilityMeasure μ]
    (a ρ h : ℝ) (_ha : 0 < a) (hρ : 0 ≤ ρ) (hρ1 : ρ ≤ 1) (hh : 0 ≤ h)
    (hs : ∀ᵐ d : Gap ∂μ, (d : ℝ) ≤ a) :
    ENNReal.ofReal (min ρ (h*Real.sqrt ρ/a)) ≤ rarePsi μ ρ h := by
  have hv : FeasibleAllocation μ ρ (fun _ => ρ) :=
    ⟨measurable_const,ae_of_all _ (fun _ => ⟨hρ,hρ1⟩),by simp⟩
  refine le_trans (b := ENNReal.ofReal (rareObjective μ (fun d => (d : ℝ)) h (fun _ => ρ))) ?_ ?_
  swap
  · unfold rarePsi
    exact le_iSup_of_le (fun _ : Gap => ρ) (le_iSup_of_le hv le_rfl)
  apply ENNReal.ofReal_le_ofReal
  have hi := objective_integrable measurable_subtype_coe (ae_of_all μ (fun d : Gap => d.property.1))
    hv.1 hv.2.1 hh
  calc
    _ = ∫ _d : Gap, min ρ (h*Real.sqrt ρ/a) ∂μ := by simp
    _ ≤ _ := integral_mono_ae (integrable_const _) hi (by
      filter_upwards [hs] with d hd
      exact min_le_min_left _ (div_le_div_of_nonneg_left (by positivity) d.property.1 hd))

theorem sqrt_allocation_memLp (μ : Measure Gap) [IsProbabilityMeasure μ]
    (ρ : ℝ) (v : Gap → ℝ) (hv : FeasibleAllocation μ ρ v) :
    MemLp (fun d => Real.sqrt (v d)) 2 μ := by
  apply (memLp_two_iff_integrable_sq hv.1.sqrt.aestronglyMeasurable).2
  exact (integrable_feasible hv).congr (by
    filter_upwards [hv.2.1] with d hd
    exact (Real.sq_sqrt hd.1).symm)

theorem inverse_gap_memLp (μ : Measure Gap) [IsProbabilityMeasure μ]
    (α a : ℝ) (hα : 2 < α) (ha : 0 < a) (hm : PowerMargin μ α a) :
    MemLp (fun d : Gap => a/(d : ℝ)) 2 μ := by
  apply (memLp_two_iff_integrable_sq
    (show Measurable (fun d : Gap => a/(d : ℝ)) by fun_prop).aestronglyMeasurable).2
  simpa only [Real.rpow_two] using margin_inverse_integrable μ α a 2 ha (by norm_num) hα hm

theorem rareObjective_margin_bound (μ : Measure Gap) [IsProbabilityMeasure μ]
    (α a ρ h : ℝ) (hα : 2 < α) (ha : 0 < a) (hh : 0 ≤ h)
    (hm : PowerMargin μ α a) (v : Gap → ℝ) (hv : FeasibleAllocation μ ρ v) :
    rareObjective μ (fun d => (d : ℝ)) h v ≤
      (h/a)*Real.sqrt ρ*Real.sqrt (1+1/(α/2-1)) := by
  have hf := sqrt_allocation_memLp μ ρ v hv
  have hg := inverse_gap_memLp μ α a hα ha hm
  have hc := integral_mul_le_Lp_mul_Lq_of_nonneg Real.HolderConjugate.two_two
    (ae_of_all μ (fun d => Real.sqrt_nonneg (v d)))
    (ae_of_all μ (fun d : Gap => (div_pos ha d.property.1).le))
    (by simpa using hf) (by simpa using hg)
  simp only [Real.rpow_two,← Real.sqrt_eq_rpow] at hc
  have hs : (∫ d, (Real.sqrt (v d))^2 ∂μ) = ∫ d, v d ∂μ :=
    integral_congr_ae (by filter_upwards [hv.2.1] with d hd; exact Real.sq_sqrt hd.1)
  rw [hs] at hc
  have hi := objective_integrable measurable_subtype_coe (ae_of_all μ (fun d : Gap => d.property.1))
    hv.1 hv.2.1 hh
  have hprod := hf.integrable_mul hg
  have hmom : (∫ d : Gap, (a/(d : ℝ))^2 ∂μ) ≤ 1+1/(α/2-1) := by
    simpa only [Real.rpow_two] using margin_inverse_integral μ α a 2 ha (by norm_num) hα hm
  calc
    _ ≤ ∫ d : Gap, (h/a)*(Real.sqrt (v d)*(a/(d : ℝ))) ∂μ :=
      integral_mono_ae hi (hprod.const_mul _) (ae_of_all _ (fun d => by
        have he : (h/a)*(Real.sqrt (v d)*(a/(d : ℝ))) = h*Real.sqrt (v d)/(d : ℝ) := by
          field_simp
        dsimp only
        rw [he]
        exact min_le_right _ _))
    _ = (h/a)*(∫ d : Gap, Real.sqrt (v d)*(a/(d : ℝ)) ∂μ) := integral_const_mul _ _
    _ ≤ (h/a)*(Real.sqrt ρ*Real.sqrt (1+1/(α/2-1))) := by
      apply mul_le_mul_of_nonneg_left _ (div_nonneg hh ha.le)
      exact hc.trans (mul_le_mul (Real.sqrt_le_sqrt hv.2.2) (Real.sqrt_le_sqrt hmom)
        (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
    _ = _ := by ring

theorem above_two_psi : AboveTwoPsiStatement := by
  intro α hα
  let C := Real.sqrt (1+1/(α/2-1))
  have hM : 1 ≤ 1+1/(α/2-1) := by
    have : 0 < α/2-1 := by linarith
    have : 0 ≤ 1/(α/2-1) := by positivity
    linarith
  have hC : 1 ≤ C := by simpa [C] using Real.sqrt_le_sqrt hM
  refine ⟨C,by linarith,?_⟩
  intro a ρ h ha _ hρ hρ' hh μ _ hμ
  refine ⟨rarePsi_supported_lower μ a ρ h ha hρ.le (by linarith) hh.le
    (exactPower_support μ α a ha hμ),?_⟩
  apply iSup_le
  intro v
  apply iSup_le
  intro hv
  apply ENNReal.ofReal_le_ofReal
  have h₀ := rareObjective_le_rarity μ ρ h hh.le v hv
  have h₁ := rareObjective_margin_bound μ α a ρ h hα ha hh.le (exactPower_margin μ α a hμ) v hv
  change rareObjective μ (fun d => (d : ℝ)) h v ≤ C*min ρ (h*Real.sqrt ρ/a)
  rw [mul_min_of_nonneg _ _ (by linarith : 0 ≤ C)]
  refine le_min (h₀.trans (by nlinarith)) ?_
  convert h₁ using 1; dsimp [C]; ring

end ThresholdHC.RareAboveTwo
