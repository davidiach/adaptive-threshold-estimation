import ThresholdHC.HardBudget.Application
import ThresholdHC.Tier5.CreationFresh

/-! Attainment in the original hidden-gap population experiment. -/
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace ThresholdHC.SharpRMS
open Tier3 Tier5 Tier6

def endpointGap : Gap := ⟨1/2, by norm_num⟩

private def outputFour (w : Prefix 4) : ℝ :=
  ((∑ i, if w i = some true then (1:ℝ) else 0) + 1) / 6

def fourFlips : AdaptiveEstimator Unit where
  randomLaw := Measure.dirac ()
  probability := inferInstance
  policy := fun _ => freshPolicy 3
  policy_measurable := fun _ _ => measurableSet_eq_fun measurable_const measurable_const
  output := fun z => outputFour (processPrefix 4 z.2)
  output_measurable := (measurable_of_countable outputFour).comp
    (Measurable.of_eval fun i => (measurable_pi_apply i.val).comp measurable_snd)

theorem four_flips_budget (μ : Measure Gap) [IsProbabilityMeasure μ] : UniformBudget μ fourFlips 4 := by
  intro q
  apply HardBudget.pathwise_expected μ fourFlips q (by norm_num)
  rw [show ⌊(4:ℝ)⌋₊ = 4 by norm_num]
  exact HardBudget.stopAt_pathwise_cap fourFlips 4 (fun _ xs => xs.length) (fun _ => rfl)

private theorem sum_bool_words {n : ℕ} (f : (Fin (n+1) → Bool) → ℝ) :
    ∑ s, f s = (∑ t, f (Fin.cons false t)) + ∑ t, f (Fin.cons true t) := by
  rw [← (Fin.consEquiv (fun _ : Fin (n+1) => Bool)).sum_comp, Fintype.sum_prod_type,
    Fintype.sum_bool]
  exact add_comm ..

private def mass {n : ℕ} (p : ℝ) (b : Fin n → Bool) : ℝ := ∏ i, if b i then p else 1-p
private def heads {n : ℕ} (b : Fin n → Bool) : ℝ := ∑ i, if b i then 1 else 0

private theorem moment (n : ℕ) (p c : ℝ) :
    ∑ b : Fin n → Bool, mass p b * (heads b + c)^2 =
      n*p*(1-p) + (n*p+c)^2 := by
  induction n generalizing c with
  | zero => simp [mass, heads]
  | succ n ih =>
    rw [sum_bool_words]
    have split (a : Bool) (t : Fin n → Bool) :
        mass p (Fin.cons a t) * (heads (Fin.cons a t) + c)^2 =
        (if a then p else 1-p) * (mass p t * (heads t + (c + if a then 1 else 0))^2) := by
      simp only [mass, heads, Fin.prod_univ_succ, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ]
      cases a <;> simp <;> ring
    simp only [split, Bool.false_eq_true, ite_false, ite_true, add_zero, ← Finset.mul_sum, ih,
      Nat.cast_succ]
    ring

private theorem fresh_risk_sum (p : ℝ) :
    (∑ w : Prefix 4, creationLaw (freshPolicy 3) (fun _ => 1/2) (fun _ => p) w *
      (outputFour w - p)^2) = 1/36 := by
  rw [fresh_transcript_expect]
  let wordPrefix := fun b : Fin 5 → Bool => freshTruncatedPrefix 3 4 (Nat.le_succ 4) b
  have hword (t : Fin 4 → Bool) (b : Bool) :
      outputFour (wordPrefix (Fin.snoc t b)) = (heads t + 1)/6 := by
    unfold outputFour heads
    congr 2
    apply Finset.sum_congr rfl
    intro i _
    change (if (if i.val < 4 then some ((Fin.snoc t b : Fin 5 → Bool) i.castSucc) else none) = some true
      then (1:ℝ) else 0) = _
    simp [i.isLt]
  have weight (t : Fin 4 → Bool) (b : Bool) :
      mass p (Fin.snoc t b) = mass p t * (if b then p else 1-p) := by
    rw [mass, Fin.prod_univ_castSucc]
    have hlast : (Fin.snoc t b : Fin 5 → Bool) 4 = b := Fin.snoc_last ..
    simp [mass, hlast]
  change (∑ s : Fin 5 → Bool, mass p s * (outputFour (wordPrefix s) - p)^2) = _
  rw [← (Fin.snocEquiv (fun _ : Fin 5 => Bool)).sum_comp, Fintype.sum_prod_type]
  simp only [Fin.snocEquiv_apply, Fintype.sum_bool, hword, weight, ite_true,
    Bool.false_eq_true, ite_false]
  have reduced (t : Fin 4 → Bool) :
      mass p t*p*((heads t+1)/6-p)^2 + mass p t*(1-p)*((heads t+1)/6-p)^2 =
      (1/36)*(mass p t*(heads t+(1-6*p))^2) := by ring
  rw [← Finset.sum_add_distrib]
  simp_rw [reduced]
  rw [← Finset.mul_sum, moment]
  push_cast
  ring

theorem four_flips_squared_risk (q : SignLaw) :
    squaredRisk (experimentLaw (Measure.dirac endpointGap) fourFlips q)
      (populationOutput fourFlips) (signMean (Measure.dirac endpointGap) q.val) =
        ENNReal.ofReal (1/36 : ℝ) := by
  classical
  let p := q.val endpointGap
  let f := fun w : Prefix 4 => (outputFour w - p)^2
  let P := experimentLaw (Measure.dirac endpointGap) fourFlips q
  have hm : Measurable (fun z : PopulationSeed Unit × ProcessTape => f (processPrefix 4 z.2)) :=
    (measurable_of_countable f).comp
      (Measurable.of_eval fun i => (measurable_pi_apply i.val).comp measurable_snd)
  obtain ⟨C,hC⟩ := (Set.finite_range fun w => |f w|).bddAbove
  have hbound (w) : |f w| ≤ C := hC ⟨w,rfl⟩
  have hi : Integrable (fun z : PopulationSeed Unit × ProcessTape => f (processPrefix 4 z.2)) P :=
    (integrable_const C).mono' hm.aestronglyMeasurable (ae_of_all _ fun z => hbound _)
  have hr := (population_realization Unit (Measure.dirac endpointGap) fourFlips q).2
    4 (fun _ => f) (fun _ => measurable_const) ⟨C, fun _ w => hbound w⟩
  have hseed : populationSeedLaw (Measure.dirac endpointGap) fourFlips =
      Measure.dirac ((), fun _ => endpointGap) := by
    simp [populationSeedLaw, fourFlips, Measure.infinitePi_dirac, Measure.dirac_prod_dirac]
  rw [hseed, integral_dirac] at hr
  change (∫ z, f (processPrefix 4 z.2) ∂P) =
      ∑ w, creationLaw (freshPolicy 3) (fun _ => 1/2) (fun _ => p) w * f w at hr
  rw [fresh_risk_sum] at hr
  rw [show signMean (Measure.dirac endpointGap) q.val = p by simp [signMean,p]]
  change (∫⁻ z, ENNReal.ofReal (f (processPrefix 4 z.2)) ∂P) = _
  rw [← ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ fun _ => sq_nonneg _), hr]

/-- The endpoint example gives an upper bound on the repository's minimax
risk, over its full class of measurable adaptive estimators. -/
theorem endpoint_minimax_upper :
    minimaxRisk (Measure.dirac endpointGap) 4 ≤ ENNReal.ofReal (1/6:ℝ) := by
  unfold minimaxRisk
  refine le_trans (sInf_le (a := maximalRMSRisk (Measure.dirac endpointGap) fourFlips) ?_) ?_
  · exact ⟨Unit, inferInstance, fourFlips, four_flips_budget _, rfl⟩
  apply iSup_le
  intro q
  apply HardBudget.rms_from_square _ _ _ _ (by norm_num)
  rw [four_flips_squared_risk]
  norm_num

end ThresholdHC.SharpRMS
