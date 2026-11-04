import ThresholdHC.HardBudget.Inputs
import ThresholdHC.HardBudget.Recurrence
import ThresholdHC.HardBudget.Rate
import Mathlib.Probability.Independence.InfinitePi

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace ThresholdHC.HardBudget
open ThresholdHC.Tier3 ThresholdHC.Tier6 ThresholdHC.ObservableSimulation
variable {R : ℕ → Type} [∀ j, MeasurableSpace (R j)]

private theorem retained_stage_inputs (base : ∀ j, AdaptiveEstimator (R j)) (M : ℝ)
    (r : ∀ j, R j) (s : Table) (k : ℕ) :
    retained M (fun j => outcome (base j) (stageCap j) M (stageInputs (r,s) j)) k =
      idealFallback base M r s k := by
  induction k with
  | zero => rfl
  | succ j ih =>
    let x := populationPath ((base j).policy (r j)) (fun c => s (Nat.pair j c))
    rw [retained,ih,idealFallback]
    change (if ((base j).policy (r j) (processHistory x (stageCap j))).isSome then _
      else clipEstimate M ((base j).output (r j,x))) =
      (if (base j).policy (r j) (processHistory x (stageCap j)) = none then
        some (clipEstimate M ((base j).output (r j,x))) else none).getD _
    cases (base j).policy (r j) (processHistory x (stageCap j)) <;> rfl

/-- Squared error in the actual observable experiment equals that of the
last-success statistic of independent local inputs. -/
theorem estimator_squared_loss (base : ∀ j, AdaptiveEstimator (R j)) (M θ : ℝ) (k : ℕ)
    (μ : Measure Gap) [IsProbabilityMeasure μ] (q : SignLaw) :
    squaredRisk (experimentLaw μ (estimator base M k) q) (populationOutput (estimator base M k)) θ =
      ∫⁻ u, loss θ (retained M (fun j => outcome (base j) (stageCap j) M (u j)) k)
        ∂Measure.infinitePi (fun j => originalSimulationLaw μ (base j) q) := by
  let A := estimator base M k
  let F (z : ∀ j, R j × Table) := loss θ (retained M (fun j => outcome (base j) (stageCap j) M (z j)) k)
  have hm : Measurable F := (measurable_loss _).comp ((measurable_retained _ _).comp
    (Measurable.of_eval fun j => (measurable_outcome _ _ _).comp (measurable_pi_apply j)))
  have h := original_observable_lintegral μ A q (fun z => loss θ (A.output z))
    ((measurable_loss _).comp A.output_measurable)
  calc _ = ∫⁻ z, loss θ (A.output (z.1,populationPath (A.policy z.1) z.2)) ∂originalSimulationLaw μ A q := h
       _ = ∫⁻ z, F (stageInputs z) ∂originalSimulationLaw μ A q := by
         apply lintegral_congr
         intro z; dsimp only [F,A]; rw [estimator_output,retained_stage_inputs]
       _ = _ := (stageInputs_preserving base M k μ q).lintegral_comp hm

theorem observable_fallback : ObservableFallbackStatement := by
  intro R mR base M hM
  refine ⟨fun B => estimator base M (stageCount B),?_⟩
  intro B hB
  dsimp only
  refine ⟨rfl,?_,?_,?_,?_⟩
  · intro r x hx
    exact (estimator_cap base M (stageCount B) r x hx).trans (Nat.cast_le.mpr (paid_fits B))
  · intro hsmall; rw [count_zero_of_small hB hsmall]; refine ⟨estimator_cap base M 0,?_⟩
    intro r s; exact estimator_output base M 0 r s
  · intro m hlo hhi r s; rw [count_at_checkpoint hB m hlo hhi]; exact estimator_output _ _ _ _ _
  · intro μ _ q C f hb hθ hθ' hC hf hhalf hs hbase
    let θ := signMean μ q.val
    let P (i : ℕ) := originalSimulationLaw μ (base i) q
    let _ (i : ℕ) : IsProbabilityMeasure (P i) := by dsimp [P,originalSimulationLaw]; infer_instance
    let ν := Measure.infinitePi P
    let X (i : ℕ) (u : ∀ j, R j × Table) := outcome (base i) (stageCap i) M (u i)
    have hm (i : ℕ) : Measurable (X i) := (measurable_outcome _ _ _).comp (measurable_pi_apply _)
    have hi : iIndepFun X ν := iIndepFun_infinitePi (fun i => measurable_outcome (base i) (stageCap i) M)
    have he (i : ℕ) : MeasurePreserving (fun u : ∀ j, R j × Table => u i) ν (P i) :=
      ⟨measurable_pi_apply _,Measure.infinitePi_map_eval P i⟩
    let D (j : ℕ) := ∫⁻ u, loss θ (retained M (fun i => X i u) j) ∂ν
    rw [estimator_squared_loss]
    apply fallback_rate hb hC ⟨hθ,hθ'⟩ f hf hhalf hs D
    · change (∫⁻ _ : ∀ j, R j × Table, loss θ (M/2) ∂ν) ≤ _
      simp [loss,ν,θ]
    · intro j
      have h1 : (∫⁻ u, loss θ (X j u).2 ∂ν) ≤ ENNReal.ofReal (C^2*(f (stageAllowance j))^2) :=
        ((he j).lintegral_comp ((measurable_loss θ).comp (measurable_outcome (base j) (stageCap j) M).snd)).le.trans
          ((stage_loss_le μ q (base j) M θ ⟨hθ,hθ'⟩ _).trans (hbase j).2)
      have h2 : (∫⁻ u, timedOut (X j u) ∂ν) ≤ 1/4 :=
        ((he j).lintegral_comp (measurable_timedOut.comp (measurable_outcome (base j) (stageCap j) M))).le.trans
          (timeout_quarter μ q (base j) M j (hbase j).1)
      exact (expected_loss_step ν X hm hi M θ j).trans (add_le_add h1 (mul_le_mul_left h2 _))

end ThresholdHC.HardBudget
