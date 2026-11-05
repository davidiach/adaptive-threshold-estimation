import ThresholdHC.Anytime.Intervals

noncomputable section
open MeasureTheory Set
namespace ThresholdHC.Anytime
open ThresholdHC.Tier6 ThresholdHC.HardBudget

variable {R : ℕ → Type} [∀ j, MeasurableSpace (R j)]

theorem interval_nested (base : ∀ j, AdaptiveEstimator (R j)) (M : ℝ) (radius : ℕ → ℝ)
    (r : ∀ j, R j) (s : Table) {k l : ℕ} (h : k ≤ l) :
    (tableInterval base M radius r s k).1 ≤ (tableInterval base M radius r s l).1 ∧
      (tableInterval base M radius r s l).2 ≤ (tableInterval base M radius r s k).2 := by
  have hlo : Monotone (fun n => (tableInterval base M radius r s n).1) :=
    monotone_nat_of_le_succ (fun _ => le_max_left _ _)
  have hhi : Antitone (fun n => (tableInterval base M radius r s n).2) :=
    antitone_nat_of_succ_le (fun _ => min_le_left _ _)
  exact ⟨hlo h,hhi h⟩

theorem interval_coverage (base : ∀ j, AdaptiveEstimator (R j)) (M θ : ℝ) (radius : ℕ → ℝ)
    (r : ∀ j, R j) (s : Table) (hθ : 0 ≤ θ ∧ θ ≤ M)
    (h : ∀ j, |(stageResult (base j) (stageCap j) M (r j) (s ∘ Nat.pair j)).getD (M/2)-θ| ≤ radius j)
    (k : ℕ) :
    (tableInterval base M radius r s k).1 ≤ θ ∧ θ ≤ (tableInterval base M radius r s k).2 := by
  induction k with
  | zero => exact hθ
  | succ k ih =>
    have hball := abs_le.mp (h k)
    exact ⟨max_le ih.1 (by linarith only [hball.2]),le_min ih.2 (by linarith only [hball.1])⟩

def halfWidth (I : ℝ × ℝ) : ℝ := max 0 (I.2-I.1)/2

theorem interval_width (base : ∀ j, AdaptiveEstimator (R j)) (M : ℝ) (radius : ℕ → ℝ)
    (r : ∀ j, R j) (s : Table) (k : ℕ) (hr : 0 ≤ radius k) :
    halfWidth (tableInterval base M radius r s (k+1)) ≤ radius k := by
  unfold halfWidth
  apply (div_le_iff₀ (by norm_num : (0:ℝ)<2)).mpr
  apply max_le (by linarith)
  have hl := le_max_right (tableInterval base M radius r s k).1
    ((stageResult (base k) (stageCap k) M (r k) (s ∘ Nat.pair k)).getD (M/2)-radius k)
  have hu := min_le_right (tableInterval base M radius r s k).2
    ((stageResult (base k) (stageCap k) M (r k) (s ∘ Nat.pair k)).getD (M/2)+radius k)
  change min _ _ - max _ _ ≤ _
  linarith only [hl,hu]

end ThresholdHC.Anytime
