import ThresholdHC.BandCostExample.Instance

/-! The capped objective of a hard mask in closed form. With `k` retained atoms,
`h = 2^{-16}` and `c = 1/∑ d_j^2`, the capped inner cost is
`min (1/4) (h √c √((k + k log k)/4) + T - S)`, where `T` is the total weighted
tail cost and `S` the part removed by the mask. Every lemma is uniform in the
64 atoms. -/
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace ThresholdHC.BandCostExample
open ThresholdHC.Tier6 (Gap)
open ThresholdHC.EntropyTail ThresholdHC.FiniteLawCertificates
open ThresholdHC.GlobalSelectionCertificates

/-- The capped objective of the hard mask `s`, as a checker expression. -/
def J (s : Fin 64 → Bool) : ℝ :=
  (objectiveExpr gaps weights (fractions s) labels (1/4) 4294967296).eval

theorem J_nonneg (s : Fin 64 → Bool) : 0 ≤ J s :=
  objectiveExpr_nonneg _ _ _ _ _ _ (by norm_num) weights_nonneg (fractions_valid s)

/-- The capped inner cost of a hard mask is the checker expression. -/
theorem capped_eq (s : Fin 64 → Bool) :
    min (ENNReal.ofReal (1/4)) (selectionObjective law (1/4) 4294967296 (retained s)) =
      ENNReal.ofReal (J s) := by
  have h := capped_objective_eq gaps weights (fractions s) labels (1/4) 4294967296 gaps_valid
    weights_nonneg (fractions_valid s) (by norm_num) (by norm_num) labels_injective labels_cover
  rw [← retained_eq, ← law_eq] at h
  have h1 : ((1/4 : ℚ) : ℝ) = 1/4 := by norm_num
  have h2 : ((4294967296 : ℚ) : ℝ) = 4294967296 := by norm_num
  rw [h1, h2] at h
  exact h

/-- Below the cap, the inner cost of a hard mask is the checker expression. -/
theorem objective_eq (s : Fin 64 → Bool) (hs : J s < 1/4) :
    selectionObjective law (1/4) 4294967296 (retained s) = ENNReal.ofReal (J s) := by
  have h := capped_eq s
  rcases le_total (ENNReal.ofReal (1/4)) (selectionObjective law (1/4) 4294967296 (retained s)) with
    hle | hle
  · rw [min_eq_left hle] at h
    have := (ENNReal.ofReal_eq_ofReal_iff (by norm_num) (J_nonneg s)).1 h
    linarith
  · rw [min_eq_right hle] at h
    exact h

/-- The original functional is attained by a hard mask (bandwise suffix theorem). -/
theorem selection_attained :
    ∃ s : Fin 64 → Bool, (selection law (1/4) 4294967296).toReal = J s := by
  obtain ⟨s, -, hs⟩ := suffix_attains gaps weights labels labels (1/4) 4294967296 gaps_valid
    weights_positive weights_sum labels_injective labels_cover labels_valid
    (by norm_num) (by norm_num) (by norm_num)
  rw [← law_eq] at hs
  have h1 : ((1/4 : ℚ) : ℝ) = 1/4 := by norm_num
  have h2 : ((4294967296 : ℚ) : ℝ) = 4294967296 := by norm_num
  rw [h1, h2] at hs
  exact ⟨s, hs⟩

/-- Every restriction of the law is the hard retained part of a mask. -/
theorem restrict_eq (S : Set Gap) :
    ∃ m : Fin 64 → Bool, law.restrict S = retained m ∧ ∀ i, (m i = true ↔ atoms i ∈ S) := by
  classical
  refine ⟨fun i => decide (atoms i ∈ S), ?_, fun i => by simp⟩
  rw [law_eq, atomicMeasure_restrict, retained_eq]
  congr 1
  funext i
  rw [← atoms_eq]
  by_cases h : atoms i ∈ S <;> simp [h, fractions]

/-! ### The closed form -/

/-- The scale `h = B^{-1/2} = 2^{-16}`. -/
def hh : ℝ := 1/65536

/-- The set of retained atoms of a mask. -/
def chosen (s : Fin 64 → Bool) : Finset (Fin 64) := Finset.univ.filter (fun i => s i = true)

/-- The number of retained atoms. -/
def kc (s : Fin 64 → Bool) : ℕ := (chosen s).card

/-- The cost entropy `k + k log k` of `k` equal unit costs. -/
def ent (k : ℕ) : ℝ := (k : ℝ) + (k : ℝ) * Real.log k

/-- The weighted ordinary tail cost of atom `i`. -/
def tt (i : Fin 64) : ℝ := (weights i : ℝ) * min 1 (hh / (atoms i : ℝ))

/-- The total weighted ordinary tail cost. -/
def TT : ℝ := ∑ i, tt i

/-- The tail cost removed by the mask. -/
def saved (s : Fin 64 → Bool) : ℝ := ∑ i ∈ chosen s, tt i

/-- The uncapped inner cost of a mask in closed form. -/
def V (s : Fin 64 → Bool) : ℝ :=
  hh * (Real.sqrt cc * Real.sqrt (ent (kc s) / 4)) + TT - saved s

theorem ent_nonneg (k : ℕ) : 0 ≤ ent k :=
  add_nonneg (Nat.cast_nonneg _) (mul_nonneg (Nat.cast_nonneg _) (Real.log_natCast_nonneg k))

theorem costs_eq (s : Fin 64 → Bool) (j : Fin 64) :
    costs gaps (fun i => weights i * fractions s i) labels j = fractions s j / zq := by
  unfold costs
  rw [Finset.sum_eq_single j]
  · rw [ite_eq_left (labels_valid j)]
    unfold weights
    have hg := (gaps_pos j).ne'
    have hz := zq_pos.ne'
    field_simp
  · intro i _ hij
    rw [ite_eq_right]
    rw [inBand_iff]
    intro h
    exact hij (Fin.ext h)
  · intro h
    exact absurd (Finset.mem_univ j) h

theorem fractions_cast (s : Fin 64 → Bool) (j : Fin 64) :
    ((fractions s j : ℚ) : ℝ) = if s j = true then 1 else 0 := by
  unfold fractions
  split_ifs <;> simp

theorem costEntropy_mask (s : Fin 64 → Bool) :
    ThresholdHC.EntropyTailQuantile.costEntropy (fun j => ((fractions s j : ℚ) : ℝ)) =
      ent (kc s) := by
  have htot : ThresholdHC.EntropyTailQuantile.costTotal (fun j => ((fractions s j : ℚ) : ℝ)) =
      (kc s : ℝ) := by
    unfold ThresholdHC.EntropyTailQuantile.costTotal
    simp only [fractions_cast]
    rw [Finset.sum_boole]
    rfl
  have hneg : ∑ j, Real.negMulLog ((fractions s j : ℚ) : ℝ) = 0 := by
    apply Finset.sum_eq_zero
    intro j _
    rw [fractions_cast]
    split_ifs <;> simp
  unfold ThresholdHC.EntropyTailQuantile.costEntropy
  rw [htot, hneg, ent, Real.negMulLog]
  ring

theorem costs_entropy (s : Fin 64 → Bool) :
    ThresholdHC.EntropyTailQuantile.costEntropy
      (fun j => ((costs gaps (fun i => weights i * fractions s i) labels j : ℚ) : ℝ)) =
      cc * ent (kc s) := by
  have he : (fun j => ((costs gaps (fun i => weights i * fractions s i) labels j : ℚ) : ℝ)) =
      fun j => cc * ((fractions s j : ℚ) : ℝ) := by
    funext j
    rw [costs_eq, Rat.cast_div, zq_cast, cc]
    ring
  rw [he, ThresholdHC.EntropyTailQuantile.costEntropy_smul, costEntropy_mask]

theorem sqrt_part (s : Fin 64 → Bool) :
    Real.sqrt (1/4 * (cc * ent (kc s)) / 4294967296) =
      hh * (Real.sqrt cc * Real.sqrt (ent (kc s) / 4)) := by
  rw [show 1/4 * (cc * ent (kc s)) / 4294967296 = hh^2 * (cc * (ent (kc s) / 4)) by
      unfold hh; ring,
    Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (by norm_num [hh]), Real.sqrt_mul cc_pos.le]

theorem tail_term (s : Fin 64 → Bool) (i : Fin 64) :
    (weights i : ℝ) * (1 - ((fractions s i : ℚ) : ℝ)) *
        min 1 (Real.sqrt (1 / (4294967296 * ((gaps i : ℚ) : ℝ)^2))) =
      tt i - (if s i = true then tt i else 0) := by
  rw [sqrt_reciprocal (by norm_num) (by rw [gaps_cast]; positivity), sqrt_budget, fractions_cast,
    gaps_cast, tt, atoms_val, hh]
  split_ifs <;> ring

theorem tail_part (s : Fin 64 → Bool) :
    ∑ i, (weights i : ℝ) * (1 - ((fractions s i : ℚ) : ℝ)) *
        min 1 (Real.sqrt (1 / (4294967296 * ((gaps i : ℚ) : ℝ)^2))) = TT - saved s := by
  simp only [tail_term]
  rw [Finset.sum_sub_distrib, saved, chosen, Finset.sum_filter]
  rfl

/-- The closed form of the capped objective. -/
theorem J_eq (s : Fin 64 → Bool) : J s = min (1/4) (V s) := by
  rw [J, objectiveExpr_eval _ _ _ _ _ _ weights_nonneg (fractions_valid s)]
  have h1 : ((1/4 : ℚ) : ℝ) = 1/4 := by norm_num
  have h2 : ((4294967296 : ℚ) : ℝ) = 4294967296 := by norm_num
  rw [h1, h2, costs_entropy, sqrt_part, tail_part, V]
  ring_nf

/-! ### Bounds on the tail terms -/

theorem hh_pos : 0 < hh := by norm_num [hh]

theorem tt_nonneg (i : Fin 64) : 0 ≤ tt i :=
  mul_nonneg (by exact_mod_cast weights_nonneg i)
    (le_min zero_le_one (div_nonneg hh_pos.le (atoms i).property.1.le))

theorem tt_le (i : Fin 64) : tt i ≤ cc * hh * (atoms i : ℝ) := by
  have hg := (atoms i).property.1
  have hw : (0:ℝ) ≤ weights i := by exact_mod_cast weights_nonneg i
  calc tt i ≤ (weights i : ℝ) * (hh / (atoms i : ℝ)) :=
        mul_le_mul_of_nonneg_left (min_le_right _ _) hw
    _ = cc * hh * (atoms i : ℝ) := by
        rw [weights_div]
        field_simp

theorem tt_eq_of_le (i : Fin 64) (hi : hh ≤ (atoms i : ℝ)) :
    tt i = cc * hh * (atoms i : ℝ) := by
  have hg := (atoms i).property.1
  rw [tt, min_eq_right ((div_le_one hg).mpr hi), weights_div]
  field_simp

theorem chosen_topTwo : chosen topTwo = {0, 1} := by
  ext i
  simp only [chosen, topTwo, Finset.mem_filter, Finset.mem_univ, true_and, decide_eq_true_eq,
    Finset.mem_insert, Finset.mem_singleton, Fin.ext_iff]
  constructor
  · intro h
    change i.val = 0 ∨ i.val = 1
    omega
  · rintro (h | h) <;> simp_all

theorem kc_topTwo : kc topTwo = 2 := by
  rw [kc, chosen_topTwo]
  rfl

theorem saved_topTwo : saved topTwo = cc * hh * (3/4) := by
  rw [saved, chosen_topTwo, Finset.sum_pair (by decide),
    tt_eq_of_le 0 (by norm_num [atoms_val, hh]), tt_eq_of_le 1 (by norm_num [atoms_val, hh]),
    atoms_val, atoms_val]
  norm_num
  ring

/-- The retained atoms' gap sum. -/
def X (s : Fin 64 → Bool) : ℝ := ∑ i ∈ chosen s, (atoms i : ℝ)

theorem saved_le (s : Fin 64 → Bool) : saved s ≤ cc * hh * X s := by
  rw [saved, X, Finset.mul_sum]
  exact Finset.sum_le_sum (fun i _ => tt_le i)

theorem TT_le_sum : TT ≤ cc * hh * ∑ i, (atoms i : ℝ) := by
  rw [TT, Finset.mul_sum]
  exact Finset.sum_le_sum (fun i _ => tt_le i)

end ThresholdHC.BandCostExample
