import ThresholdHC.GlobalCut.Cut
import ThresholdHC.FiniteLawCertificates.Objective

/-! The counterexample to exactness of the global cut (certified-selection note,
after Corollary 6; `evidence/not_one_global_threshold.json`). Masses
`9999/10000` at `1/4` and `1/10000` at `1/2`, `ρ = 1/4`, `B = 10^8`. Selecting
only the smaller gap costs at most `2.0001·10⁻⁴`, while each of the three
global cuts costs at least `2.00011·10⁻⁴`: rejecting the gap `1/4` leaves a
remainder cost near `4·10⁻⁴`, and selecting both atoms has entropy at least
`16.002`, using `log 39997 ≥ 8`. Hand bounds replace the unverified Python
certificate. -/
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace ThresholdHC.GlobalCut
open ThresholdHC.Tier6 (Gap)
open ThresholdHC.EntropyTail
open ThresholdHC.FiniteLawCertificates

theorem twoAtom_gaps_valid : ∀ i : Fin 2, 0 < (![1/4, 1/2] : Fin 2 → ℚ) i ∧ (![1/4, 1/2] : Fin 2 → ℚ) i ≤ 1/2 := by
  intro i
  fin_cases i <;> norm_num

theorem twoAtom_masses_nonneg : ∀ i : Fin 2, 0 ≤ (![9999/10000, 1/10000] : Fin 2 → ℚ) i := by
  intro i
  fin_cases i <;> norm_num

theorem twoAtom_labels_injective : Function.Injective (![0, 1] : Fin 2 → ℕ) := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all

theorem twoAtom_labels_cover : ∀ i : Fin 2, ∃ j, inBand ((![1/4, 1/2] : Fin 2 → ℚ) i) ((![0, 1] : Fin 2 → ℕ) j) = true := by
  intro i
  fin_cases i
  · exact ⟨1, by simp [inBand]; norm_num⟩
  · exact ⟨0, by simp [inBand]; norm_num⟩

theorem twoAtom_points_strictMono : StrictMono (points (![1/4, 1/2] : Fin 2 → ℚ) twoAtom_gaps_valid) := by
  rw [Fin.strictMono_iff_lt_succ]
  intro i
  fin_cases i
  rw [← Subtype.coe_lt_coe]
  simp [points]
  norm_num

/-- The capped objective of a fractional selection, in closed form. -/
theorem twoAtom_capped_eq (s : Fin 2 → ℚ) (hs : ∀ i, 0 ≤ s i ∧ s i ≤ 1) :
    min (ENNReal.ofReal (1/4)) (selectionObjective (atomicMeasure (points (![1/4, 1/2] : Fin 2 → ℚ) twoAtom_gaps_valid) (![9999/10000, 1/10000] : Fin 2 → ℚ)) (1/4) (10^8)
      (atomicMeasure (points (![1/4, 1/2] : Fin 2 → ℚ) twoAtom_gaps_valid) (fun i => (![9999/10000, 1/10000] : Fin 2 → ℚ) i * s i))) =
    ENNReal.ofReal (min (1/4)
      (Real.sqrt ((1/4) * EntropyTailQuantile.costEntropy
          (fun j => (costs (![1/4, 1/2] : Fin 2 → ℚ) (fun i => (![9999/10000, 1/10000] : Fin 2 → ℚ) i * s i) (![0, 1] : Fin 2 → ℕ) j : ℝ)) / 10^8) +
        ∑ i, ((![9999/10000, 1/10000] : Fin 2 → ℚ) i : ℝ) * (1 - (s i : ℝ)) *
          min 1 (Real.sqrt (1 / (10^8 * ((![1/4, 1/2] : Fin 2 → ℚ) i : ℝ)^2))))) := by
  have h := capped_objective_eq (![1/4, 1/2] : Fin 2 → ℚ) (![9999/10000, 1/10000] : Fin 2 → ℚ) s (![0, 1] : Fin 2 → ℕ) (1/4) (10^8) twoAtom_gaps_valid twoAtom_masses_nonneg hs
    (by norm_num) (by norm_num) twoAtom_labels_injective twoAtom_labels_cover
  rw [objectiveExpr_eval (![1/4, 1/2] : Fin 2 → ℚ) (![9999/10000, 1/10000] : Fin 2 → ℚ) s (![0, 1] : Fin 2 → ℕ) (1/4) (10^8) twoAtom_masses_nonneg hs] at h
  push_cast at h
  exact h

theorem twoAtom_sqrt_quarter : Real.sqrt (1 / (10^8 * ((1/4 : ℚ) : ℝ)^2)) = 4/10^4 := by
  rw [show (1 / (10^8 * ((1/4 : ℚ) : ℝ)^2)) = (4/10^4)^2 by norm_num]
  exact Real.sqrt_sq (by norm_num)

theorem twoAtom_sqrt_half : Real.sqrt (1 / (10^8 * ((1/2 : ℚ) : ℝ)^2)) = 2/10^4 := by
  rw [show (1 / (10^8 * ((1/2 : ℚ) : ℝ)^2)) = (2/10^4)^2 by norm_num]
  exact Real.sqrt_sq (by norm_num)

/-- Band costs: the gap `1/2` lies in band `0`, the gap `1/4` in band `1`. -/
theorem twoAtom_costs_eq (v : Fin 2 → ℚ) :
    (fun j => (costs (![1/4, 1/2] : Fin 2 → ℚ) v (![0, 1] : Fin 2 → ℕ) j : ℝ)) = ![4 * (v 1 : ℝ), 16 * (v 0 : ℝ)] := by
  funext j
  fin_cases j
  · simp [costs, inBand, Fin.sum_univ_two]
    norm_num
    ring
  · simp [costs, inBand, Fin.sum_univ_two]
    norm_num
    ring

/-- `log 39997 ≥ 8`, from `e < 3`. -/
theorem eight_le_log_39997 : (8 : ℝ) ≤ Real.log 39997 := by
  rw [Real.le_log_iff_exp_le (by norm_num)]
  have h : Real.exp 8 = Real.exp 1 ^ 8 := by
    rw [← Real.exp_nat_mul]
    norm_num
  rw [h]
  calc Real.exp 1 ^ 8 ≤ 3 ^ 8 :=
        pow_le_pow_left₀ (Real.exp_pos 1).le
          (Real.exp_one_lt_d9.le.trans (by norm_num)) 8
    _ ≤ 39997 := by norm_num

/-- The entropy of the full law is at least `16.002`. -/
theorem twoAtom_entropy_full_ge :
    (16002/1000 : ℝ) ≤ EntropyTailQuantile.costEntropy ![(1/2500 : ℝ), 9999/625] := by
  have ha : ∀ i, 0 ≤ (![(1/2500 : ℝ), 9999/625] : Fin 2 → ℝ) i := by
    intro i
    fin_cases i <;> norm_num
  rw [EntropyTailQuantile.costEntropy_eq_log_sum ha]
  simp only [EntropyTailQuantile.costTotal, Fin.sum_univ_two, Matrix.cons_val_zero,
    Matrix.cons_val_one]
  have h0 : ((1/2500 : ℝ) + 9999/625) / (1/2500) = 39997 := by norm_num
  have h1 : 0 ≤ Real.log (((1/2500 : ℝ) + 9999/625) / (9999/625)) :=
    Real.log_nonneg (by norm_num)
  rw [h0]
  nlinarith [eight_le_log_39997]

/-- Selecting only the gap `1/4` costs at most `2.0001·10⁻⁴`. -/
theorem twoAtom_witness_le :
    selection (atomicMeasure (points (![1/4, 1/2] : Fin 2 → ℚ) twoAtom_gaps_valid) (![9999/10000, 1/10000] : Fin 2 → ℚ)) (1/4) (10^8) ≤ ENNReal.ofReal (20001/10^8) := by
  have hs : ∀ i, 0 ≤ (![1, 0] : Fin 2 → ℚ) i ∧ (![1, 0] : Fin 2 → ℚ) i ≤ 1 := by
    intro i
    fin_cases i <;> norm_num
  have hle := le_min (selection_le_rho (atomicMeasure (points (![1/4, 1/2] : Fin 2 → ℚ) twoAtom_gaps_valid) (![9999/10000, 1/10000] : Fin 2 → ℚ)) (1/4) (10^8))
    (selection_le_objective (selected_le (points (![1/4, 1/2] : Fin 2 → ℚ) twoAtom_gaps_valid) (![9999/10000, 1/10000] : Fin 2 → ℚ) _ twoAtom_masses_nonneg hs) (1/4) (10^8))
  rw [twoAtom_capped_eq _ hs, twoAtom_costs_eq] at hle
  refine hle.trans (ENNReal.ofReal_le_ofReal ((min_le_right _ _).trans ?_))
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, twoAtom_sqrt_quarter,
    twoAtom_sqrt_half]
  norm_num
  have hE : EntropyTailQuantile.costEntropy ![(0 : ℝ), 9999/625] = 9999/625 := by
    simp [EntropyTailQuantile.costEntropy, EntropyTailQuantile.costTotal]
  have hr : Real.sqrt (9999/625) ≤ 39998/10000 :=
    Real.sqrt_le_iff.2 ⟨by norm_num, by norm_num⟩
  rw [hE]
  linarith

/-- Each of the three global cuts costs at least `2.00011·10⁻⁴`. -/
theorem twoAtom_cut_ge (k : Fin 3) :
    ENNReal.ofReal (200011/10^9) ≤ selectionObjective (atomicMeasure (points (![1/4, 1/2] : Fin 2 → ℚ) twoAtom_gaps_valid) (![9999/10000, 1/10000] : Fin 2 → ℚ)) (1/4) (10^8)
      (∑ i : Fin 2, (if 2 ≤ i.val + k.val then ENNReal.ofReal ((![9999/10000, 1/10000] : Fin 2 → ℚ) i : ℝ) else 0) •
        Measure.dirac ((points (![1/4, 1/2] : Fin 2 → ℚ) twoAtom_gaps_valid) i)) := by
  have hs : ∀ i : Fin 2, 0 ≤ (if 2 ≤ i.val + k.val then (1 : ℚ) else 0) ∧
      (if 2 ≤ i.val + k.val then (1 : ℚ) else 0) ≤ 1 := by
    intro i
    split_ifs <;> norm_num
  have hm : (∑ i : Fin 2, (if 2 ≤ i.val + k.val then ENNReal.ofReal ((![9999/10000, 1/10000] : Fin 2 → ℚ) i : ℝ) else 0) •
        Measure.dirac ((points (![1/4, 1/2] : Fin 2 → ℚ) twoAtom_gaps_valid) i)) =
      atomicMeasure (points (![1/4, 1/2] : Fin 2 → ℚ) twoAtom_gaps_valid) (fun i => (![9999/10000, 1/10000] : Fin 2 → ℚ) i * if 2 ≤ i.val + k.val then (1 : ℚ) else 0) := by
    unfold atomicMeasure
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases h : 2 ≤ i.val + k.val
    · simp only [h, ↓reduceIte, mul_one]
    · simp [h]
  rw [hm]
  refine le_trans ?_ (min_le_right (ENNReal.ofReal (1/4)) _)
  rw [twoAtom_capped_eq _ hs, twoAtom_costs_eq]
  refine ENNReal.ofReal_le_ofReal ?_
  fin_cases k <;>
    simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, twoAtom_sqrt_quarter,
      twoAtom_sqrt_half] <;> norm_num
  · linarith [Real.sqrt_nonneg (EntropyTailQuantile.costEntropy ![(0 : ℝ), 0])]
  · linarith [Real.sqrt_nonneg (EntropyTailQuantile.costEntropy ![(1/2500 : ℝ), 0])]
  · have h : (400022/100000 : ℝ) ≤
        Real.sqrt (EntropyTailQuantile.costEntropy ![(1/2500 : ℝ), 9999/625]) :=
      (Real.le_sqrt (by norm_num) (by linarith [twoAtom_entropy_full_ge])).2
        (by nlinarith [twoAtom_entropy_full_ge])
    linarith

/-- The global cut is not exact: on the two-atom law of the note, `K < V`. -/
theorem not_exact : NotExactStatement := by
  refine ⟨(points (![1/4, 1/2] : Fin 2 → ℚ) twoAtom_gaps_valid) 0, (points (![1/4, 1/2] : Fin 2 → ℚ) twoAtom_gaps_valid) 1, by simp [points], by simp [points], ?_⟩
  intro μ
  have hμ : μ = atomicMeasure (points (![1/4, 1/2] : Fin 2 → ℚ) twoAtom_gaps_valid) (![9999/10000, 1/10000] : Fin 2 → ℚ) := by
    simp only [μ, atomicMeasure, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
    norm_num
  rw [hμ]
  refine ⟨atomicMeasure_probability (points (![1/4, 1/2] : Fin 2 → ℚ) twoAtom_gaps_valid) (![9999/10000, 1/10000] : Fin 2 → ℚ) twoAtom_masses_nonneg
    (by norm_num [Fin.sum_univ_two]), ?_⟩
  have hV : globalCutValue (atomicMeasure (points (![1/4, 1/2] : Fin 2 → ℚ) twoAtom_gaps_valid) (![9999/10000, 1/10000] : Fin 2 → ℚ)) (1/4) (10^8) =
      min (ENNReal.ofReal (1/4)) (⨅ k : Fin 3,
        selectionObjective (atomicMeasure (points (![1/4, 1/2] : Fin 2 → ℚ) twoAtom_gaps_valid) (![9999/10000, 1/10000] : Fin 2 → ℚ)) (1/4) (10^8)
          (∑ i : Fin 2, (if 2 ≤ i.val + k.val then ENNReal.ofReal ((![9999/10000, 1/10000] : Fin 2 → ℚ) i : ℝ) else 0) •
            Measure.dirac ((points (![1/4, 1/2] : Fin 2 → ℚ) twoAtom_gaps_valid) i))) :=
    finite_cut (points (![1/4, 1/2] : Fin 2 → ℚ) twoAtom_gaps_valid) (fun i => ENNReal.ofReal ((![9999/10000, 1/10000] : Fin 2 → ℚ) i : ℝ)) twoAtom_points_strictMono (1/4) (10^8)
  rw [hV]
  calc selection (atomicMeasure (points (![1/4, 1/2] : Fin 2 → ℚ) twoAtom_gaps_valid) (![9999/10000, 1/10000] : Fin 2 → ℚ)) (1/4) (10^8) ≤ ENNReal.ofReal (20001/10^8) :=
        twoAtom_witness_le
    _ < ENNReal.ofReal (200011/10^9) :=
        (ENNReal.ofReal_lt_ofReal_iff (by norm_num)).2 (by norm_num)
    _ ≤ _ := le_min (ENNReal.ofReal_le_ofReal (by norm_num)) (le_iInf twoAtom_cut_ge)

end ThresholdHC.GlobalCut
