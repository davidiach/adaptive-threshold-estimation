import ThresholdHC.EntropyTailLower.FiniteBandApprox
import ThresholdHC.EntropyTail.Bridge
import ThresholdHC.EntropyTail.Objective

noncomputable section
namespace ThresholdHC.EntropyTailLower
open MeasureTheory Real Filter
open ThresholdHC.Tier6 ThresholdHC.EntropyTailQuantile
open scoped BigOperators ENNReal Topology

def finiteCanonicalScore (μ : Measure Gap) (ρ B : ℝ) (n : ℕ) (S : Finset ℕ) : ℝ :=
  ((1/sqrt B)*sqrt ρ)*sqrt (costEntropy (fun i : Fin n => if i.val ∈ S then
    μ.real (ThresholdHC.EntropyTail.band i.val)/((1/2:ℝ)^(i.val+1))^2 else 0)) +
    ∑ j ∈ Finset.range n, if j ∈ S then 0 else
      μ.real (ThresholdHC.EntropyTail.band j)*min 1 ((1/sqrt B)/((1/2:ℝ)^(j+1)))

theorem finite_canonical_selection_bound (μ : Measure Gap) [IsFiniteMeasure μ]
    (ρ B : ℝ) (hρ : 0 ≤ ρ) (n : ℕ) (S : Finset ℕ) (hS : ∀ j ∈ S, j < n) :
    ThresholdHC.EntropyTail.selection μ ρ B ≤
      ENNReal.ofReal (2*min ρ (finiteCanonicalScore μ ρ B n S)) +
      μ ((selectedCanonicalBands (Finset.range n))ᶜ) := by
  classical
  let h := 1/sqrt B
  let σ := μ.restrict (selectedCanonicalBands S)
  let W := (selectedCanonicalBands (Finset.range n))ᶜ
  let F := costEntropy (fun i : Fin n => if i.val ∈ S then
    μ.real (ThresholdHC.EntropyTail.band i.val)/((1/2:ℝ)^(i.val+1))^2 else 0)
  let E := ∑ j ∈ Finset.range n, if j ∈ S then 0 else
    μ.real (ThresholdHC.EntropyTail.band j)*min 1 (h/((1/2:ℝ)^(j+1)))
  let Q := (h*sqrt ρ)*sqrt F+E
  have hh : 0 ≤ h := by dsimp [h]; positivity
  have hF : 0 ≤ F := by
    apply costEntropy_nonneg
    intro i
    split_ifs
    · exact div_nonneg measureReal_nonneg (sq_nonneg _)
    · exact le_rfl
  have hE : 0 ≤ E := by
    apply Finset.sum_nonneg
    intro j _
    split_ifs
    · exact le_rfl
    · exact mul_nonneg measureReal_nonneg (le_min (by norm_num) (div_nonneg hh (by positivity)))
  have hgamma := selectedCanonicalBands_gamma_upper μ n S hS
  have hentr : ENNReal.ofReal h*(ENNReal.ofReal ρ*ThresholdHC.EntropyTail.gamma σ)^(1/2:ℝ) ≤
      ENNReal.ofReal (2*(h*sqrt ρ)*sqrt F) := by
    calc
      _ ≤ ENNReal.ofReal h*(ENNReal.ofReal ρ*ENNReal.ofReal (4*F))^(1/2:ℝ) := by
        gcongr <;> exact hgamma
      _ = ENNReal.ofReal (h*sqrt (ρ*(4*F))) :=
        ThresholdHC.EntropyTail.entropyTerm_ofReal hh hρ (by positivity)
      _ = _ := by
        have he : sqrt (ρ*(4*F)) = 2*sqrt ρ*sqrt F := by
          rw [show ρ*(4*F) = 4*(ρ*F) by ring,sqrt_mul (by norm_num : (0:ℝ) ≤ 4),sqrt_mul hρ]
          norm_num <;> ring
        rw [he]
        congr 1
        ring
  have htail : ThresholdHC.EntropyTail.tailCost (μ-σ) h ≤ ENNReal.ofReal (2*E)+μ W := by
    rw [← ThresholdHC.EntropyTail.quantile_tailModulus_eq _ hh]
    have hb := canonical_selected_tail_upper μ n S h hh
    change tailModulus (μ-σ) h ≤ 2*E+μ.real W at hb
    calc
      _ ≤ ENNReal.ofReal (2*E+μ.real W) := ENNReal.ofReal_le_ofReal hb
      _ = ENNReal.ofReal (2*E)+μ W := by
        rw [ENNReal.ofReal_add (by positivity) measureReal_nonneg]
        rw [measureReal_def,ENNReal.ofReal_toReal (measure_ne_top μ W)]
  have hobj : ThresholdHC.EntropyTail.selectionObjective μ ρ B σ ≤ ENNReal.ofReal (2*Q)+μ W := by
    have hb := add_le_add hentr htail
    change ENNReal.ofReal h*(ENNReal.ofReal ρ*ThresholdHC.EntropyTail.gamma σ)^(1/2:ℝ)+
      ThresholdHC.EntropyTail.tailCost (μ-σ) h ≤ _
    calc
      _ ≤ (ENNReal.ofReal (2*(h*sqrt ρ)*sqrt F)+ENNReal.ofReal (2*E))+μ W := by
        simpa only [add_assoc] using hb
      _ = _ := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 2
        dsimp [Q]
        ring
  change ThresholdHC.EntropyTail.selection μ ρ B ≤ ENNReal.ofReal (2*min ρ Q)+μ W
  rcases le_total ρ Q with hq | hq
  · rw [min_eq_left hq]
    calc
      _ ≤ ENNReal.ofReal ρ := ThresholdHC.EntropyTail.selection_le_rho μ ρ B
      _ ≤ ENNReal.ofReal (2*ρ) := ENNReal.ofReal_le_ofReal (by linarith)
      _ ≤ _ := le_self_add
  · rw [min_eq_right hq]
    exact (ThresholdHC.EntropyTail.selection_le_objective Measure.restrict_le_self ρ B).trans hobj

theorem finite_canonical_uniform_limit (μ : Measure Gap) [IsFiniteMeasure μ]
    (ρ B M : ℝ) (hρ : 0 ≤ ρ)
    (hfinite : ∀ n : ℕ, ∃ S : Finset ℕ, (∀ j ∈ S, j < n) ∧
      min ρ (finiteCanonicalScore μ ρ B n S) ≤ M) :
    ThresholdHC.EntropyTail.selection μ ρ B ≤ ENNReal.ofReal (2*M) := by
  have hn (n : ℕ) : ThresholdHC.EntropyTail.selection μ ρ B ≤ ENNReal.ofReal (2*M)+
      μ ((selectedCanonicalBands (Finset.range n))ᶜ) := by
    obtain ⟨S,hS,hbound⟩ := hfinite n
    apply (finite_canonical_selection_bound μ ρ B hρ n S hS).trans
    exact add_le_add (ENNReal.ofReal_le_ofReal (by linarith only [hbound])) le_rfl
  have ht : Tendsto (fun n : ℕ => ENNReal.ofReal (2*M)+
      μ ((selectedCanonicalBands (Finset.range n))ᶜ)) atTop (𝓝 (ENNReal.ofReal (2*M))) := by
    simpa only [add_zero] using tendsto_const_nhds.add (canonical_prefix_remainder_tendsto_zero μ)
  exact ge_of_tendsto ht (Eventually.of_forall hn)

end ThresholdHC.EntropyTailLower
