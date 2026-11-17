import ThresholdHC.DeterministicCertificates.Checker
import ThresholdHC.EntropyTailQuantile.CostEntropy
import Mathlib.Algebra.BigOperators.Fin

namespace ThresholdHC.DeterministicCertificates

def sumExpr : List Expr → Expr
  | [] => .rational 0
  | x :: xs => .add x (sumExpr xs)

theorem sumExpr_eval (xs : List Expr) :
    (sumExpr xs).eval = (xs.map Expr.eval).sum := by
  induction xs with
  | nil => simp [sumExpr, Expr.eval]
  | cons x xs ih => simp [sumExpr, Expr.eval, ih]

/-- The same homogeneous entropy as the frozen mathematical development.
Zero coordinates are omitted before taking logarithms. -/
def entropyExpr {n : ℕ} (a : Fin n → ℚ) : Expr :=
  .add (.rational (∑ i, a i)) (sumExpr (List.ofFn fun i =>
    if a i = 0 then .rational 0 else .scale (a i) (.log (.rational ((∑ j, a j)/a i)))))

theorem entropyExpr_eval {n : ℕ} (a : Fin n → ℚ) (ha : ∀ i, 0 ≤ a i) :
    (entropyExpr a).eval =
      ThresholdHC.EntropyTailQuantile.costEntropy (fun i => (a i : ℝ)) := by
  rw [ThresholdHC.EntropyTailQuantile.costEntropy_eq_log_sum
    (fun i => by exact_mod_cast ha i)]
  simp only [entropyExpr, Expr.eval, sumExpr_eval, List.map_ofFn, List.sum_ofFn,
    Rat.cast_sum, ThresholdHC.EntropyTailQuantile.costTotal]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  dsimp only [Function.comp_apply]
  split_ifs with hz
  · simp [Expr.eval, hz]
  · simp [Expr.eval, Rat.cast_div, Rat.cast_sum]

theorem entropy_accepted_sound {n : ℕ} (a : Fin n → ℚ) (ha : ∀ i, 0 ≤ a i)
    {claimed : Interval} {c : Evidence} (h : accepted (entropyExpr a) claimed c = true) :
    Contains claimed (ThresholdHC.EntropyTailQuantile.costEntropy (fun i => (a i : ℝ))) := by
  rw [← entropyExpr_eval a ha]
  exact accepted_sound h

end ThresholdHC.DeterministicCertificates
