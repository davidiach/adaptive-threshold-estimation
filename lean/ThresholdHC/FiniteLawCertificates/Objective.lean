import ThresholdHC.FiniteLawCertificates.Data
import ThresholdHC.DeterministicCertificates.Entropy

/-! Finite rational data connected to the original measure-level definitions. -/
noncomputable section
open MeasureTheory
open scoped BigOperators ENNReal Classical
namespace ThresholdHC.FiniteLawCertificates
open ThresholdHC.Tier6

def objectiveExpr {n m : ℕ} (g w s : Fin n → ℚ) (labels : Fin m → ℕ) (ρ B : ℚ) :
    ThresholdHC.DeterministicCertificates.Expr :=
  .minimum (.rational ρ) (.add
    (.sqrt (.scale (ρ/B) (ThresholdHC.DeterministicCertificates.entropyExpr
      (costs g (fun i => w i*s i) labels))))
    (ThresholdHC.DeterministicCertificates.sumExpr (List.ofFn fun i =>
      .scale (w i*(1-s i)) (.minimum (.rational 1)
        (.sqrt (.rational (1/(B*(g i)^2))))))))

theorem objectiveExpr_eval {n m : ℕ} (g w s : Fin n → ℚ) (labels : Fin m → ℕ) (ρ B : ℚ)
    (hw : ∀ i, 0 ≤ w i) (hs : ∀ i, 0 ≤ s i ∧ s i ≤ 1) :
    (objectiveExpr g w s labels ρ B).eval = min (ρ:ℝ)
      (Real.sqrt ((ρ:ℝ)*ThresholdHC.EntropyTailQuantile.costEntropy
          (fun j => (costs g (fun i => w i*s i) labels j:ℝ))/(B:ℝ)) +
        ∑ i, (w i:ℝ)*(1-(s i:ℝ))*min 1 (Real.sqrt (1/((B:ℝ)*(g i:ℝ)^2)))) := by
  simp only [objectiveExpr, ThresholdHC.DeterministicCertificates.Expr.eval,
    ThresholdHC.DeterministicCertificates.sumExpr_eval, List.map_ofFn, List.sum_ofFn]
  rw [ThresholdHC.DeterministicCertificates.entropyExpr_eval _
    (costs_nonneg g _ labels (fun i => mul_nonneg (hw i) (hs i).1))]
  push_cast
  simp only [Function.comp_apply, ThresholdHC.DeterministicCertificates.Expr.eval]
  push_cast
  congr 3
  ring


theorem selected_le {n : ℕ} (d : Fin n → Gap) (w s : Fin n → ℚ)
    (hw : ∀ i, 0 ≤ w i) (hs : ∀ i, 0 ≤ s i ∧ s i ≤ 1) :
    atomicMeasure d (fun i => w i*s i) ≤ atomicMeasure d w :=
  atomicMeasure_le d w _ (fun i => by nlinarith [hw i, (hs i).2])

theorem sqrt_reciprocal {B g : ℝ} (hB : 0 ≤ B) (hg : 0 ≤ g) :
    Real.sqrt (1/(B*g^2)) = (1/Real.sqrt B)/g := by
  rw [Real.sqrt_div (by norm_num), Real.sqrt_one, Real.sqrt_mul hB, Real.sqrt_sq hg]
  ring

theorem objectiveExpr_nonneg {n m : ℕ} (g w s : Fin n → ℚ) (labels : Fin m → ℕ)
    (ρ B : ℚ) (hρ : 0 ≤ ρ) (hw : ∀ i, 0 ≤ w i) (hs : ∀ i, 0 ≤ s i ∧ s i ≤ 1) :
    0 ≤ (objectiveExpr g w s labels ρ B).eval := by
  rw [objectiveExpr_eval g w s labels ρ B hw hs]
  apply le_min (by exact_mod_cast hρ)
  apply add_nonneg (Real.sqrt_nonneg _)
  apply Finset.sum_nonneg
  intro i _
  exact mul_nonneg (mul_nonneg (by exact_mod_cast hw i)
    (sub_nonneg.mpr (by exact_mod_cast (hs i).2))) (le_min zero_le_one (Real.sqrt_nonneg _))

theorem capped_objective_eq {n m : ℕ} (g w s : Fin n → ℚ) (labels : Fin m → ℕ)
    (ρ B : ℚ) (hg : ∀ i, 0 < g i ∧ g i ≤ 1/2) (hw : ∀ i, 0 ≤ w i)
    (hs : ∀ i, 0 ≤ s i ∧ s i ≤ 1) (hρ : 0 ≤ ρ) (hB : 0 < B)
    (hinj : Function.Injective labels) (hcover : ∀ i, ∃ j, inBand (g i) (labels j) = true) :
    min (ENNReal.ofReal (ρ:ℝ)) (ThresholdHC.EntropyTail.selectionObjective
      (atomicMeasure (points g hg) w) (ρ:ℝ) (B:ℝ)
      (atomicMeasure (points g hg) (fun i => w i*s i))) =
      ENNReal.ofReal (objectiveExpr g w s labels ρ B).eval := by
  have hws (i : Fin n) : 0 ≤ w i*s i := mul_nonneg (hw i) (hs i).1
  have hle (i : Fin n) : w i*s i ≤ w i := by nlinarith [hw i, (hs i).2]
  have hr (i : Fin n) : 0 ≤ w i-w i*s i := sub_nonneg.mpr (hle i)
  have hΓ : 0 ≤ ThresholdHC.EntropyTailQuantile.costEntropy
      (fun j => (costs g (fun i => w i*s i) labels j:ℝ)) :=
    ThresholdHC.EntropyTailQuantile.costEntropy_nonneg (fun j => by
      exact_mod_cast costs_nonneg g _ labels hws j)
  have hh : (0:ℝ) ≤ 1/Real.sqrt (B:ℝ) := by positivity
  rw [ThresholdHC.EntropyTail.selectionObjective, gamma_rational g _ labels hg hws hinj hcover,
    ThresholdHC.EntropyTail.entropyTerm_ofReal hh (by exact_mod_cast hρ) hΓ,
    atomicMeasure_sub _ w _ hws hle, tailCost_atomic _ _ hr hh,
    ← ENNReal.ofReal_add (mul_nonneg hh (Real.sqrt_nonneg _)) (by
      apply Finset.sum_nonneg
      intro i _
      exact mul_nonneg (by exact_mod_cast hr i)
        (le_min zero_le_one (div_nonneg hh (points g hg i).property.1.le))),
    ← ENNReal.ofReal_min, objectiveExpr_eval g w s labels ρ B hw hs]
  congr 2
  congr 1
  · rw [Real.sqrt_div (mul_nonneg (by exact_mod_cast hρ) hΓ)]
    ring
  · apply Finset.sum_congr rfl
    intro i _
    rw [sqrt_reciprocal (by exact_mod_cast hB.le) (by exact_mod_cast (hg i).1.le)]
    simp only [points, Rat.cast_sub, Rat.cast_mul]
    ring

theorem objective_accepted_sound {n m : ℕ} (g w s : Fin n → ℚ) (labels : Fin m → ℕ)
    (ρ B : ℚ) (hg : ∀ i, 0 < g i ∧ g i ≤ 1/2) (hw : ∀ i, 0 ≤ w i)
    (hs : ∀ i, 0 ≤ s i ∧ s i ≤ 1) (hρ : 0 ≤ ρ) (hB : 0 < B)
    (hinj : Function.Injective labels) (hcover : ∀ i, ∃ j, inBand (g i) (labels j) = true)
    {claimed : ThresholdHC.DeterministicCertificates.Interval}
    {c : ThresholdHC.DeterministicCertificates.Evidence}
    (h : ThresholdHC.DeterministicCertificates.accepted (objectiveExpr g w s labels ρ B) claimed c = true) :
    ThresholdHC.DeterministicCertificates.Contains claimed
      (min (ENNReal.ofReal (ρ:ℝ)) (ThresholdHC.EntropyTail.selectionObjective
        (atomicMeasure (points g hg) w) (ρ:ℝ) (B:ℝ)
        (atomicMeasure (points g hg) (fun i => w i*s i)))).toReal := by
  rw [capped_objective_eq g w s labels ρ B hg hw hs hρ hB hinj hcover,
    ENNReal.toReal_ofReal (objectiveExpr_nonneg g w s labels ρ B hρ hw hs)]
  exact ThresholdHC.DeterministicCertificates.accepted_sound h

theorem selection_upper {n m : ℕ} (g w s : Fin n → ℚ) (labels : Fin m → ℕ)
    (ρ B : ℚ) (hg : ∀ i, 0 < g i ∧ g i ≤ 1/2) (hw : ∀ i, 0 ≤ w i)
    (hs : ∀ i, 0 ≤ s i ∧ s i ≤ 1) (hρ : 0 ≤ ρ) (hB : 0 < B)
    (hinj : Function.Injective labels) (hcover : ∀ i, ∃ j, inBand (g i) (labels j) = true)
    {claimed : ThresholdHC.DeterministicCertificates.Interval}
    {c : ThresholdHC.DeterministicCertificates.Evidence}
    (h : ThresholdHC.DeterministicCertificates.accepted (objectiveExpr g w s labels ρ B) claimed c = true) :
    (ThresholdHC.EntropyTail.selection (atomicMeasure (points g hg) w) (ρ:ℝ) (B:ℝ)).toReal ≤
      (claimed.upper:ℝ) := by
  have he := capped_objective_eq g w s labels ρ B hg hw hs hρ hB hinj hcover
  have hle := le_min (ThresholdHC.EntropyTail.selection_le_rho (atomicMeasure (points g hg) w) (ρ:ℝ) (B:ℝ))
    (ThresholdHC.EntropyTail.selection_le_objective (selected_le (points g hg) w s hw hs) (ρ:ℝ) (B:ℝ))
  rw [he] at hle
  have ht := ENNReal.toReal_mono ENNReal.ofReal_ne_top hle
  rw [ENNReal.toReal_ofReal (objectiveExpr_nonneg g w s labels ρ B hρ hw hs)] at ht
  exact ht.trans (ThresholdHC.DeterministicCertificates.accepted_sound h).2

end ThresholdHC.FiniteLawCertificates
