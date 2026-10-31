import ThresholdHC.CapIdentification.TerminalMoments
import ThresholdHC.CapIdentification.BiasApproximation

/-! Exact infinite-budget fixed-cap bias floor. A direct affine recovery
construction supplies the upper limit; the attained matching pair supplies
the lower limit. Four-prior strong duality is not a premise. -/

noncomputable section
open MeasureTheory Filter
open scoped BigOperators ENNReal Topology

namespace ThresholdHC.CapIdentification
open ThresholdHC.Tier6 (Gap SignLaw signMean)
open ThresholdHC.StoppingProgram ThresholdHC.RareAboveTwo

theorem approximate_diameter_program_upper (μ : Measure Gap) [IsProbabilityMeasure μ]
    {ρ : ℝ} (hρ : 0 ≤ ρ) {N : ℕ} (hN : 0 < N) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ B : ℝ, 0 < B →
      programSquared μ ρ B N ≤ ENNReal.ofReal (((capDiameter μ ρ N+ε)/2)^2+C/B) := by
  obtain ⟨c,w,hw⟩ := affine_bias_approximation μ hρ N hε
  let P := oddMomentRepresentative N w
  obtain ⟨y,hy⟩ := terminal_polynomial_representation μ N P (oddMomentRepresentative_degree N w)
  have hb : 0 ≤ (capDiameter μ ρ N+ε)/2 :=
    div_nonneg (add_nonneg (capDiameter_bounds μ hρ N).1 hε.le) (by norm_num)
  apply full_output_program_upper μ ρ hN y (c-nullPolynomialMean μ P) _ hb
  intro q hq
  rw [hy,populationPolynomialMean_odd]
  dsimp only [P]
  convert hw q hq using 1
  congr 1
  ring

theorem programSquared_budget_limit (μ : Measure Gap) [IsProbabilityMeasure μ]
    {ρ : ℝ} (hρ : 0 ≤ ρ) {N : ℕ} (hN : 0 < N) :
    Tendsto (fun B : ℝ => programSquared μ ρ B N) atTop
      (𝓝 (ENNReal.ofReal ((capDiameter μ ρ N/2)^2))) := by
  have hlower : ENNReal.ofReal ((capDiameter μ ρ N/2)^2) ≤
      liminf (fun B : ℝ => programSquared μ ρ B N) atTop :=
    le_liminf_of_le (by isBoundedDefault) (Eventually.of_forall (fun B => capDiameter_program_floor μ hρ B N))
  have hupper (ε : ℝ) (hε : 0 < ε) : limsup (fun B : ℝ => programSquared μ ρ B N) atTop ≤
      ENNReal.ofReal (((capDiameter μ ρ N+ε)/2)^2) := by
    obtain ⟨C,_,hC⟩ := approximate_diameter_program_upper μ hρ hN hε
    have hlim : Tendsto (fun B : ℝ => ENNReal.ofReal (((capDiameter μ ρ N+ε)/2)^2+C/B)) atTop
        (𝓝 (ENNReal.ofReal (((capDiameter μ ρ N+ε)/2)^2))) := by
      apply ENNReal.continuous_ofReal.tendsto _ |>.comp
      simpa only [div_eq_mul_inv,mul_zero,add_zero] using
        (tendsto_const_nhds.add (tendsto_inv_atTop_zero.const_mul C))
    have hh := limsup_le_limsup ((eventually_gt_atTop (0:ℝ)).mono (fun B hB => hC B hB))
    rwa [hlim.limsup_eq] at hh
  have hεlim : Tendsto (fun n : ℕ => ENNReal.ofReal
      (((capDiameter μ ρ N+1/((n:ℝ)+1))/2)^2)) atTop
        (𝓝 (ENNReal.ofReal ((capDiameter μ ρ N/2)^2))) := by
    apply ENNReal.continuous_ofReal.tendsto _ |>.comp
    have he : Tendsto (fun n : ℕ => 1/((n:ℝ)+1)) atTop (𝓝 (0:ℝ)) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    simpa only [add_zero] using (((tendsto_const_nhds.add he).div_const 2).pow 2)
  have hsup : limsup (fun B : ℝ => programSquared μ ρ B N) atTop ≤
      ENNReal.ofReal ((capDiameter μ ρ N/2)^2) :=
    ge_of_tendsto hεlim (Eventually.of_forall (fun n => hupper _ (by positivity)))
  exact tendsto_of_le_liminf_of_limsup_le hlower hsup

end ThresholdHC.CapIdentification
