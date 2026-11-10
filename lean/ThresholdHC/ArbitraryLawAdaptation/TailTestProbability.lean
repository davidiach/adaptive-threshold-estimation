import ThresholdHC.ArbitraryLawAdaptation.TailTest
import ThresholdHC.ObservableSimulation.OriginalExperiment

/-! Single-coin probability bounds for the sign-neutral tail test.

For a coin with heads probability `1/2 + d`:

* if `d ≤ 2^{-J}` the coin is unresolved with probability at least `1/2`;
* if `d ≥ 4·2^{-J}` it is unresolved with probability at most `exp(-4^J d²/2)`;
* its expected work is at most `min{4^J, 1024 d^{-2} (1 + log₂⁺(d 2^J))}`.

Only Hoeffding bounds at single checkpoints and union bounds are used. The
checkpoints share one coin and are not treated as independent samples. The
negative sign follows from flip symmetry in the next module. -/

noncomputable section
open MeasureTheory Real
namespace ThresholdHC.ArbitraryLawAdaptation
open ThresholdHC.Tier2 ThresholdHC.Tier6 ThresholdHC.Uniform713 ThresholdHC.EntropyTailUpper
open ThresholdHC.ObservableSimulation

theorem gapParameter_true_coe (d : Gap) :
    ((gapParameter true d : unitInterval) : ℝ) = 1 / 2 + (d : ℝ) := by
  simp [gapParameter]

/-- `log₂⁺(d/t)` at the scale `t = 2^{-J}`. -/
def tailLog (J : ℕ) (d : ℝ) : ℝ := max 0 (Real.logb 2 (d * 2 ^ J))

/-- The bounded work envelope `w_J(d) = min{N, 1024 d^{-2} (1 + log₂⁺(d/t))}`. -/
def tailWorkEnvelope (J : ℕ) (d : ℝ) : ℝ := min (4 ^ J) (1024 / d ^ 2 * (1 + tailLog J d))

theorem exp_neg_one_le : exp (-1) ≤ 10 / 27 := by
  rw [exp_neg, inv_le_comm₀ (exp_pos 1) (by norm_num)]
  have h := Real.exp_one_gt_d9
  norm_num at h ⊢
  linarith

theorem exp_neg_nat_le (m : ℕ) : exp (-(m : ℝ)) ≤ (10 / 27) ^ m := by
  have h : exp (-(m : ℝ)) = exp (-1) ^ m := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  rw [h]
  exact pow_le_pow_left₀ (exp_nonneg _) exp_neg_one_le m

theorem tail_geometric_sum (J : ℕ) :
    ∑ k ∈ Finset.range (J + 1), ((10 : ℝ) / 27) ^ (J - k) ≤ 27 / 17 := by
  induction J with
  | zero => norm_num
  | succ J ih =>
    rw [Finset.sum_range_succ, Nat.sub_self, pow_zero]
    have he : ∑ k ∈ Finset.range (J + 1), ((10 : ℝ) / 27) ^ (J + 1 - k) =
        (10 / 27) * ∑ k ∈ Finset.range (J + 1), ((10 : ℝ) / 27) ^ (J - k) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      have hk' : k ≤ J := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
      rw [show J + 1 - k = (J - k) + 1 by omega, pow_succ]
      ring
    rw [he]
    linarith

theorem tailThreshold_ge (J k : ℕ) : 2 * (2 : ℝ) ^ k ≤ (tailThreshold J k : ℝ) := by
  have h := tailScale_le_threshold_sq J k
  have hs : (2 * (2 : ℝ) ^ k) ^ 2 ≤ (tailScale J k : ℝ) := by
    unfold tailScale
    push_cast
    have h4 : (4 : ℝ) ^ k = ((2 : ℝ) ^ k) ^ 2 := by
      rw [← pow_mul, mul_comm, pow_mul]
      norm_num
    rw [h4]
    have h2 : (0 : ℝ) ≤ ((J - k : ℕ) : ℝ) := Nat.cast_nonneg _
    nlinarith [sq_nonneg ((2 : ℝ) ^ k)]
  exact (pow_le_pow_iff_left₀ (by positivity) (Nat.cast_nonneg _) two_ne_zero).1 (hs.trans h)

theorem tailScale_cast (J k : ℕ) :
    (tailScale J k : ℝ) = 2 * 4 ^ k * ((J - k + 2 : ℕ) : ℝ) := by
  unfold tailScale
  push_cast
  ring

/-- A failed check is a one-sided deviation of at least `d/2` once `h_k/n_k ≤ d/2`. -/
theorem tail_not_resolved_le_exp (J k : ℕ) (d : Gap)
    (hr : 2 * (tailThreshold J k : ℝ) ≤ 4 ^ k * (d : ℝ)) :
    (tapeMeasure (gapParameter true d)).real {ω | ¬ tailResolvedAt J k ω} ≤
      exp (-(4 ^ k * (d : ℝ) ^ 2 / 2)) := by
  have hn : 0 < 4 ^ k := by positivity
  have hnR : (0 : ℝ) < 4 ^ k := by positivity
  have hd := d.property.1
  have hsub : {ω | ¬ tailResolvedAt J k ω} ⊆
      {ω | (d : ℝ) / 2 ≤
        ((gapParameter true d : unitInterval) : ℝ) - prefixMean observations (4 ^ k) ω} := by
    intro ω hω
    have hω' : ¬ tailResolvedAt J k ω := hω
    rw [tailResolvedAt_iff, not_lt] at hω'
    have hle : prefixMean observations (4 ^ k) ω - 1 / 2 ≤ (tailThreshold J k : ℝ) / 4 ^ k :=
      (le_abs_self _).trans hω'
    have hrk : (tailThreshold J k : ℝ) / 4 ^ k ≤ (d : ℝ) / 2 := by
      rw [div_le_div_iff₀ hnR (by norm_num)]
      linarith
    change (d : ℝ) / 2 ≤ _
    rw [gapParameter_true_coe]
    linarith
  have h := tape_prefix_lower_tail (gapParameter true d) hn
    (by positivity : (0 : ℝ) ≤ (d : ℝ) / 2)
  calc (tapeMeasure (gapParameter true d)).real {ω | ¬ tailResolvedAt J k ω}
      ≤ (tapeMeasure (gapParameter true d)).real {ω | (d : ℝ) / 2 ≤
          ((gapParameter true d : unitInterval) : ℝ) - prefixMean observations (4 ^ k) ω} :=
        measureReal_mono hsub
    _ ≤ exp (-2 * ((4 ^ k : ℕ) : ℝ) * ((d : ℝ) / 2) ^ 2) := h
    _ = exp (-(4 ^ k * (d : ℝ) ^ 2 / 2)) := by
        congr 1
        push_cast
        ring

/-- A resolving check is a two-sided deviation of at least `h_k/(2 n_k)` once
`d ≤ h_k/(2 n_k)`. -/
theorem tail_resolved_le_exp (J k : ℕ) (d : Gap)
    (hd : 2 * (4 ^ k * (d : ℝ)) ≤ (tailThreshold J k : ℝ)) :
    (tapeMeasure (gapParameter true d)).real {ω | tailResolvedAt J k ω} ≤
      2 * exp (-((tailThreshold J k : ℝ) ^ 2 / (2 * 4 ^ k))) := by
  have hn : 0 < 4 ^ k := by positivity
  have hnR : (0 : ℝ) < 4 ^ k := by positivity
  set r : ℝ := (tailThreshold J k : ℝ) / 4 ^ k with hrdef
  have hr0 : 0 ≤ r := by positivity
  have hdr : (d : ℝ) ≤ r / 2 := by
    rw [hrdef, div_div, le_div_iff₀ (by positivity)]
    linarith
  have hsub : {ω | tailResolvedAt J k ω} ⊆
      {ω | r / 2 ≤ prefixMean observations (4 ^ k) ω -
          ((gapParameter true d : unitInterval) : ℝ)} ∪
      {ω | r / 2 ≤ ((gapParameter true d : unitInterval) : ℝ) -
          prefixMean observations (4 ^ k) ω} := by
    intro ω hω
    have hω' : tailResolvedAt J k ω := hω
    rw [tailResolvedAt_iff, lt_abs] at hω'
    rcases hω' with h | h
    · left
      change r / 2 ≤ _
      rw [gapParameter_true_coe]
      linarith
    · right
      change r / 2 ≤ _
      rw [gapParameter_true_coe]
      have hd0 := d.property.1
      linarith
  have hu := tape_prefix_upper_tail (gapParameter true d) hn (by positivity : (0 : ℝ) ≤ r / 2)
  have hl := tape_prefix_lower_tail (gapParameter true d) hn (by positivity : (0 : ℝ) ≤ r / 2)
  have he : -2 * ((4 ^ k : ℕ) : ℝ) * (r / 2) ^ 2 =
      -((tailThreshold J k : ℝ) ^ 2 / (2 * 4 ^ k)) := by
    rw [hrdef]
    push_cast
    field_simp
  rw [he] at hu hl
  calc (tapeMeasure (gapParameter true d)).real {ω | tailResolvedAt J k ω}
      ≤ (tapeMeasure (gapParameter true d)).real
          ({ω | r / 2 ≤ prefixMean observations (4 ^ k) ω -
              ((gapParameter true d : unitInterval) : ℝ)} ∪
           {ω | r / 2 ≤ ((gapParameter true d : unitInterval) : ℝ) -
              prefixMean observations (4 ^ k) ω}) := measureReal_mono hsub
    _ ≤ _ + _ := measureReal_union_le _ _
    _ ≤ 2 * exp (-((tailThreshold J k : ℝ) ^ 2 / (2 * 4 ^ k))) := by linarith

/-- Small gaps: every check resolves with probability at most `2 e^{-(J-k+2)}`. -/
theorem tail_resolved_small_gap (J k : ℕ) (hk : k ≤ J) (d : Gap)
    (hd : (d : ℝ) ≤ (1 / 2) ^ J) :
    (tapeMeasure (gapParameter true d)).real {ω | tailResolvedAt J k ω} ≤
      2 * (10 / 27 : ℝ) ^ (J - k + 2) := by
  have hnR : (0 : ℝ) < 4 ^ k := by positivity
  have h1 : (4 : ℝ) ^ k * (1 / 2) ^ J ≤ 2 ^ k := by
    have ha : (1 / 2 : ℝ) ^ J ≤ (1 / 2) ^ k :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) hk
    have hb : (4 : ℝ) ^ k * (1 / 2) ^ k = 2 ^ k := by
      rw [← mul_pow]
      norm_num
    calc (4 : ℝ) ^ k * (1 / 2) ^ J ≤ 4 ^ k * (1 / 2) ^ k := by gcongr
      _ = 2 ^ k := hb
  have hd' : 2 * (4 ^ k * (d : ℝ)) ≤ (tailThreshold J k : ℝ) := by
    have h2 : (4 : ℝ) ^ k * (d : ℝ) ≤ 4 ^ k * (1 / 2) ^ J := by gcongr
    linarith [tailThreshold_ge J k]
  have hexp : ((J - k + 2 : ℕ) : ℝ) ≤ (tailThreshold J k : ℝ) ^ 2 / (2 * 4 ^ k) := by
    rw [le_div_iff₀ (by positivity)]
    have h := tailScale_le_threshold_sq J k
    rw [tailScale_cast] at h
    linarith
  calc (tapeMeasure (gapParameter true d)).real {ω | tailResolvedAt J k ω}
      ≤ 2 * exp (-((tailThreshold J k : ℝ) ^ 2 / (2 * 4 ^ k))) := tail_resolved_le_exp J k d hd'
    _ ≤ 2 * exp (-((J - k + 2 : ℕ) : ℝ)) := by
        gcongr
    _ ≤ 2 * (10 / 27 : ℝ) ^ (J - k + 2) := by
        gcongr
        exact exp_neg_nat_le _

/-- Small gaps are unresolved with probability at least one half. The bound is a
union bound over the checks of one coin; no independence between checks is used. -/
theorem tail_unresolved_ge_half (J : ℕ) (d : Gap) (hd : (d : ℝ) ≤ (1 / 2) ^ J) :
    1 / 2 ≤ (tapeMeasure (gapParameter true d)).real {ω | tailUnresolved J ω} := by
  set P := tapeMeasure (gapParameter true d) with hP
  have hcompl : {ω | tailUnresolved J ω}ᶜ ⊆
      ⋃ k ∈ Finset.range (J + 1), {ω | tailResolvedAt J k ω} := by
    intro ω hω
    have hω' : ¬ tailUnresolved J ω := hω
    unfold tailUnresolved at hω'
    push Not at hω'
    obtain ⟨k, hk, hr⟩ := hω'
    exact Set.mem_iUnion₂.mpr ⟨k, Finset.mem_range.mpr (Nat.lt_succ_of_le hk), hr⟩
  have hsum : P.real (⋃ k ∈ Finset.range (J + 1), {ω | tailResolvedAt J k ω}) ≤
      ∑ k ∈ Finset.range (J + 1), P.real {ω | tailResolvedAt J k ω} :=
    measureReal_biUnion_finset_le _ _
  have hterm : ∑ k ∈ Finset.range (J + 1), P.real {ω | tailResolvedAt J k ω} ≤
      ∑ k ∈ Finset.range (J + 1), 2 * (10 / 27 : ℝ) ^ 2 * (10 / 27 : ℝ) ^ (J - k) := by
    apply Finset.sum_le_sum
    intro k hk
    have hk' : k ≤ J := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    have h := tail_resolved_small_gap J k hk' d hd
    rw [pow_add] at h
    linarith
  have hgeo := tail_geometric_sum J
  rw [← Finset.mul_sum] at hterm
  have hc : P.real {ω | tailUnresolved J ω}ᶜ = 1 - P.real {ω | tailUnresolved J ω} := by
    rw [measureReal_compl (measurableSet_tailUnresolved J)]
    simp
  have hmono : P.real {ω | tailUnresolved J ω}ᶜ ≤
      P.real (⋃ k ∈ Finset.range (J + 1), {ω | tailResolvedAt J k ω}) :=
    measureReal_mono hcompl (measure_ne_top _ _)
  nlinarith

/-- Large gaps: the terminal check alone leaves the coin unresolved with
probability at most `exp(-N d²/2)`. -/
theorem tail_unresolved_le_exp (J : ℕ) (d : Gap) (hd : 4 * (1 / 2 : ℝ) ^ J ≤ (d : ℝ)) :
    (tapeMeasure (gapParameter true d)).real {ω | tailUnresolved J ω} ≤
      exp (-(4 ^ J * (d : ℝ) ^ 2 / 2)) := by
  have hr : 2 * (tailThreshold J J : ℝ) ≤ 4 ^ J * (d : ℝ) := by
    rw [tailThreshold_terminal]
    push_cast
    have h4 : (4 : ℝ) ^ J * (1 / 2) ^ J = 2 ^ J := by
      rw [← mul_pow]
      norm_num
    calc 2 * (2 : ℝ) ^ (J + 1) = 4 ^ J * (4 * (1 / 2) ^ J) := by
          rw [pow_succ]
          linear_combination (-4 : ℝ) * h4
      _ ≤ 4 ^ J * (d : ℝ) := by gcongr
  have hsub : {ω | tailUnresolved J ω} ⊆ {ω | ¬ tailResolvedAt J J ω} :=
    fun ω hω => hω J le_rfl
  exact (measureReal_mono hsub).trans (tail_not_resolved_le_exp J J d hr)

/-- Once `n_k d² ≥ 36 (J-k+2)` the check radius is at most `d/2`. -/
theorem tailThreshold_le_of_scale (J k : ℕ) {d : ℝ} (hd : 0 ≤ d)
    (hC : 36 * ((J - k + 2 : ℕ) : ℝ) ≤ 4 ^ k * d ^ 2) :
    2 * (tailThreshold J k : ℝ) ≤ 4 ^ k * d := by
  have hlt := tailThreshold_lt J k
  have hmval := tailScale_cast J k
  have h4k : (1 : ℝ) ≤ 4 ^ k := one_le_pow₀ (by norm_num)
  have hL : (2 : ℝ) ≤ ((J - k + 2 : ℕ) : ℝ) := by
    push_cast
    linarith [Nat.cast_nonneg (α := ℝ) (J - k)]
  have hm4 : (4 : ℝ) ≤ (tailScale J k : ℝ) := by
    rw [hmval]
    nlinarith
  have hs2 : (2 : ℝ) ≤ Real.sqrt (tailScale J k) := by
    have h := Real.sqrt_le_sqrt hm4
    rwa [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)] at h
  have hs3 : Real.sqrt (tailScale J k) ≤ 4 ^ k * d / 3 := by
    rw [Real.sqrt_le_iff]
    refine ⟨by positivity, ?_⟩
    rw [hmval]
    have h1 : (4 : ℝ) ^ k * (36 * ((J - k + 2 : ℕ) : ℝ)) ≤ 4 ^ k * (4 ^ k * d ^ 2) :=
      mul_le_mul_of_nonneg_left hC (by positivity)
    have h2 : (0 : ℝ) ≤ 4 ^ k * ((J - k + 2 : ℕ) : ℝ) := by positivity
    nlinarith
  linarith

/-- Geometric decay of the work increments after the first decisive check. -/
theorem tail_work_term (k0 j : ℕ) {d : ℝ} (hk0 : 72 ≤ 4 ^ k0 * d ^ 2) :
    3 * (4 : ℝ) ^ (k0 + j) * exp (-(4 ^ (k0 + j) * d ^ 2 / 2)) ≤ 4 ^ k0 * (1 / 2) ^ j / 2 := by
  have hj : ((j : ℝ) + 1) ≤ 4 ^ j := by
    have h : j + 1 ≤ 4 ^ j := Nat.succ_le_of_lt (Nat.lt_pow_self (by norm_num))
    exact_mod_cast h
  have h4j : (0 : ℝ) < 4 ^ j := by positivity
  have hy : (((3 * j + 3 : ℕ)) : ℝ) ≤ 4 ^ (k0 + j) * d ^ 2 / 2 := by
    rw [pow_add]
    push_cast
    nlinarith
  have he : exp (-(4 ^ (k0 + j) * d ^ 2 / 2)) ≤ (1 / 2 : ℝ) ^ (3 * j + 3) := by
    calc exp (-(4 ^ (k0 + j) * d ^ 2 / 2)) ≤ exp (-(((3 * j + 3 : ℕ)) : ℝ)) :=
          exp_le_exp.mpr (neg_le_neg hy)
      _ ≤ (10 / 27 : ℝ) ^ (3 * j + 3) := exp_neg_nat_le _
      _ ≤ (1 / 2 : ℝ) ^ (3 * j + 3) :=
          pow_le_pow_left₀ (by norm_num) (by norm_num) _
  have e1 : (4 : ℝ) ^ j * (1 / 2) ^ (3 * j) = (1 / 2) ^ j := by
    rw [pow_mul, ← mul_pow]
    norm_num
  calc 3 * (4 : ℝ) ^ (k0 + j) * exp (-(4 ^ (k0 + j) * d ^ 2 / 2))
      ≤ 3 * (4 : ℝ) ^ (k0 + j) * (1 / 2 : ℝ) ^ (3 * j + 3) := by gcongr
    _ = 4 ^ k0 * ((4 : ℝ) ^ j * (1 / 2) ^ (3 * j)) * (3 / 8) := by
        rw [pow_add, pow_add]
        ring
    _ = 4 ^ k0 * (1 / 2) ^ j * (3 / 8) := by rw [e1]
    _ ≤ 4 ^ k0 * (1 / 2) ^ j / 2 := by
        have : (0 : ℝ) ≤ 4 ^ k0 * (1 / 2) ^ j := by positivity
        linarith

/-- The layer-cake form of `4^s` over the checks below `J`. -/
theorem four_pow_layer (J s : ℕ) (hs : s ≤ J) :
    (4 : ℝ) ^ s = 1 + ∑ k ∈ Finset.range J, 3 * 4 ^ k * (if k < s then (1 : ℝ) else 0) := by
  induction J generalizing s with
  | zero =>
    obtain rfl : s = 0 := Nat.le_zero.mp hs
    simp
  | succ J ih =>
    rw [Finset.sum_range_succ]
    rcases Nat.lt_or_ge s (J + 1) with hlt | hge
    · have hsJ : s ≤ J := Nat.lt_succ_iff.mp hlt
      rw [← add_assoc, ← ih s hsJ, ite_eq_right (by omega)]
      ring
    · obtain rfl : s = J + 1 := le_antisymm hs hge
      have hc : ∑ k ∈ Finset.range J, 3 * (4 : ℝ) ^ k * (if k < J + 1 then (1 : ℝ) else 0) =
          ∑ k ∈ Finset.range J, 3 * (4 : ℝ) ^ k * (if k < J then (1 : ℝ) else 0) :=
        Finset.sum_congr rfl fun k hk => by
          have hk' := Finset.mem_range.mp hk
          rw [ite_eq_left (by omega), ite_eq_left hk']
      rw [hc, ← add_assoc, ← ih J le_rfl, ite_eq_left (by omega), pow_succ]
      ring

theorem tailWork_sum (J : ℕ) (ω : ℕ → Bool) :
    (tailWork J ω : ℝ) =
      1 + ∑ k ∈ Finset.range J, 3 * 4 ^ k * (if k < tailStop J ω then (1 : ℝ) else 0) := by
  unfold tailWork
  push_cast
  exact four_pow_layer J _ (tailStop_le J ω)

theorem integrable_tailWork (J : ℕ) (P : Measure (ℕ → Bool)) [IsFiniteMeasure P] :
    Integrable (fun ω => (tailWork J ω : ℝ)) P := by
  refine (integrable_const ((4 : ℝ) ^ J)).mono'
    ((measurable_of_countable (Nat.cast : ℕ → ℝ)).comp (measurable_tailWork J)).aestronglyMeasurable
    (ae_of_all _ fun ω => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _)]
  exact_mod_cast tailWork_le J ω

theorem measurableSet_stop_gt (J k : ℕ) : MeasurableSet {ω | k < tailStop J ω} :=
  measurable_tailStop J (MeasurableSet.of_discrete (s := {s : ℕ | k < s}))

/-- Expected work as a sum over the checks that were passed. -/
theorem tail_expected_work_eq (J : ℕ) (P : Measure (ℕ → Bool)) [IsProbabilityMeasure P] :
    ∫ ω, (tailWork J ω : ℝ) ∂P =
      1 + ∑ k ∈ Finset.range J, 3 * 4 ^ k * P.real {ω | k < tailStop J ω} := by
  have hind : ∀ k, (fun ω => if k < tailStop J ω then (1 : ℝ) else 0) =
      Set.indicator {ω | k < tailStop J ω} (fun _ => (1 : ℝ)) := by
    intro k
    funext ω
    by_cases h : k < tailStop J ω
    · rw [ite_eq_left h, Set.indicator_of_mem (show ω ∈ {ω | k < tailStop J ω} from h)]
    · rw [ite_eq_right h, Set.indicator_of_notMem (show ω ∉ {ω | k < tailStop J ω} from h)]
  have hint : ∀ k, Integrable
      (fun ω => 3 * (4 : ℝ) ^ k * (if k < tailStop J ω then (1 : ℝ) else 0)) P := by
    intro k
    apply Integrable.const_mul
    rw [hind k]
    exact (integrable_const (1 : ℝ)).indicator (measurableSet_stop_gt J k)
  simp_rw [tailWork_sum]
  rw [integral_add (integrable_const _) (integrable_finsetSum _ fun k _ => hint k),
    integral_finsetSum _ fun k _ => hint k]
  simp only [integral_const, probReal_univ, smul_eq_mul, mul_one]
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  rw [integral_const_mul, hind k, integral_indicator (measurableSet_stop_gt J k),
    setIntegral_const]
  simp

/-- The single-coin work bound `E_d T ≤ w_J(d)` for a positive sign. -/
theorem tail_expected_work_le (J : ℕ) (d : Gap) :
    ∫ ω, (tailWork J ω : ℝ) ∂tapeMeasure (gapParameter true d) ≤ tailWorkEnvelope J d := by
  set P := tapeMeasure (gapParameter true d) with hP
  have hd0 : (0 : ℝ) < d := d.property.1
  have hd2 : (d : ℝ) ≤ 1 / 2 := d.property.2
  have hT0 : 0 ≤ tailLog J d := le_max_left _ _
  have hN : ∫ ω, (tailWork J ω : ℝ) ∂P ≤ 4 ^ J := by
    calc ∫ ω, (tailWork J ω : ℝ) ∂P ≤ ∫ _ω, (4 : ℝ) ^ J ∂P :=
          integral_mono (integrable_tailWork J P) (integrable_const _)
            fun ω => by exact_mod_cast tailWork_le J ω
      _ = 4 ^ J := by simp
  refine le_min hN ?_
  rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
  by_cases hex : ∃ k, k ≤ J ∧ 36 * ((J - k + 2 : ℕ) : ℝ) ≤ 4 ^ k * (d : ℝ) ^ 2
  · classical
    obtain ⟨hk0J, hk0C⟩ := Nat.find_spec hex
    have hmin : ∀ k < Nat.find hex,
        ¬ (k ≤ J ∧ 36 * ((J - k + 2 : ℕ) : ℝ) ≤ 4 ^ k * (d : ℝ) ^ 2) :=
      fun k hk => Nat.find_min hex hk
    generalize Nat.find hex = k0 at hk0J hk0C hmin
    have hL2 : (2 : ℝ) ≤ ((J - k0 + 2 : ℕ) : ℝ) := by
      push_cast
      linarith [Nat.cast_nonneg (α := ℝ) (J - k0)]
    have h72 : 72 ≤ 4 ^ k0 * (d : ℝ) ^ 2 := by linarith
    let g : ℕ → ℝ := fun k =>
      if k ≤ k0 then (4 : ℝ) ^ k else 2 * 4 ^ k0 - 4 ^ k0 * (1 / 2) ^ (k - k0)
    have hterm : ∀ k ∈ Finset.range J,
        3 * (4 : ℝ) ^ k * P.real {ω | k < tailStop J ω} ≤ g (k + 1) - g k := by
      intro k hk
      have hkJ : k < J := Finset.mem_range.mp hk
      by_cases hlt : k < k0
      · have h1 : g (k + 1) = 4 ^ (k + 1) := ite_eq_left (by omega)
        have h2 : g k = 4 ^ k := ite_eq_left (by omega)
        have hp : P.real {ω | k < tailStop J ω} ≤ 1 := measureReal_le_one
        rw [h1, h2, pow_succ]
        have h4 : (0 : ℝ) < 4 ^ k := by positivity
        nlinarith
      · have hge : k0 ≤ k := not_lt.mp hlt
        obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hge
        have h1 : g (k0 + j + 1) = 2 * 4 ^ k0 - 4 ^ k0 * (1 / 2) ^ (j + 1) := by
          have hne : ¬ k0 + j + 1 ≤ k0 := by omega
          simp only [g, ite_eq_right hne]
          rw [show k0 + j + 1 - k0 = j + 1 by omega]
        have h2 : g (k0 + j) = 2 * 4 ^ k0 - 4 ^ k0 * (1 / 2) ^ j := by
          by_cases hj0 : k0 + j ≤ k0
          · have hj : j = 0 := by omega
            subst hj
            simp only [g, add_zero, le_refl, ite_true, pow_zero]
            ring
          · simp only [g, ite_eq_right hj0]
            rw [show k0 + j - k0 = j by omega]
        have hCk : 36 * ((J - (k0 + j) + 2 : ℕ) : ℝ) ≤ 4 ^ (k0 + j) * (d : ℝ) ^ 2 := by
          have ha : ((J - (k0 + j) + 2 : ℕ) : ℝ) ≤ ((J - k0 + 2 : ℕ) : ℝ) := by
            exact_mod_cast (by omega : J - (k0 + j) + 2 ≤ J - k0 + 2)
          have hb : (4 : ℝ) ^ k0 ≤ 4 ^ (k0 + j) :=
            pow_le_pow_right₀ (by norm_num) (by omega)
          have hc : (4 : ℝ) ^ k0 * (d : ℝ) ^ 2 ≤ 4 ^ (k0 + j) * (d : ℝ) ^ 2 := by gcongr
          linarith
        have hr := tailThreshold_le_of_scale J (k0 + j) hd0.le hCk
        have hsub : {ω | k0 + j < tailStop J ω} ⊆ {ω | ¬ tailResolvedAt J (k0 + j) ω} :=
          fun ω hω => not_resolved_of_lt_stop hω
        have hp : P.real {ω | k0 + j < tailStop J ω} ≤
            exp (-(4 ^ (k0 + j) * (d : ℝ) ^ 2 / 2)) :=
          (measureReal_mono hsub).trans (tail_not_resolved_le_exp J (k0 + j) d hr)
        have hw := tail_work_term k0 j h72
        rw [h1, h2, pow_succ]
        have h4 : (0 : ℝ) < 3 * 4 ^ (k0 + j) := by positivity
        nlinarith
    have hsum : ∑ k ∈ Finset.range J, 3 * (4 : ℝ) ^ k * P.real {ω | k < tailStop J ω} ≤
        g J - g 0 := by
      rw [← Finset.sum_range_sub g J]
      exact Finset.sum_le_sum hterm
    have hg0 : g 0 = 1 := by simp [g]
    have hgJ : g J ≤ 2 * 4 ^ k0 := by
      by_cases hJ : J ≤ k0
      · have hb : (4 : ℝ) ^ J ≤ 4 ^ k0 := pow_le_pow_right₀ (by norm_num) hJ
        simp only [g, ite_eq_left hJ]
        have : (0 : ℝ) < 4 ^ k0 := by positivity
        linarith
      · simp only [g, ite_eq_right hJ]
        have : (0 : ℝ) ≤ 4 ^ k0 * (1 / 2) ^ (J - k0) := by positivity
        linarith
    have hE : ∫ ω, (tailWork J ω : ℝ) ∂P ≤ 2 * 4 ^ k0 := by
      rw [tail_expected_work_eq J P]
      linarith
    -- The decisive check is not the first one, and its predecessor is not decisive.
    have hk0pos : 0 < k0 := by
      rcases Nat.eq_zero_or_pos k0 with h0 | hpos
      · subst h0
        simp only [pow_zero, one_mul] at h72
        nlinarith
      · exact hpos
    obtain ⟨k1, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk0pos.ne'
    have hprev : 4 ^ k1 * (d : ℝ) ^ 2 < 36 * ((J - k1 + 2 : ℕ) : ℝ) := by
      have h := hmin k1 (Nat.lt_succ_self k1)
      push Not at h
      exact h (by omega)
    have hcast : ((J - k1 + 2 : ℕ) : ℝ) = ((J - (k1 + 1) : ℕ) : ℝ) + 3 := by
      have : J - k1 + 2 = J - (k1 + 1) + 3 := by omega
      rw [this]
      push_cast
      ring
    have hlog : ((J - (k1 + 1) : ℕ) : ℝ) ≤ tailLog J d := by
      refine le_trans ?_ (le_max_right _ _)
      have hpos : (0 : ℝ) < (d : ℝ) * 2 ^ J := by positivity
      rw [Real.le_logb_iff_rpow_le (by norm_num) hpos, Real.rpow_natCast]
      have hone : (1 : ℝ) ≤ 2 ^ (k1 + 1) * (d : ℝ) := by
        by_contra hlt
        push Not at hlt
        have hnn : (0 : ℝ) ≤ 2 ^ (k1 + 1) * (d : ℝ) := by positivity
        have hsq : (2 ^ (k1 + 1) * (d : ℝ)) ^ 2 < 1 := by nlinarith
        have h4 : (4 : ℝ) ^ (k1 + 1) = ((2 : ℝ) ^ (k1 + 1)) ^ 2 := by
          rw [← pow_mul, mul_comm, pow_mul]
          norm_num
        rw [h4] at h72
        nlinarith
      have hsplit : (2 : ℝ) ^ J = 2 ^ (J - (k1 + 1)) * 2 ^ (k1 + 1) := by
        rw [← pow_add]
        congr 1
        omega
      rw [hsplit]
      have hpp : (0 : ℝ) < 2 ^ (J - (k1 + 1)) := by positivity
      nlinarith
    rw [hcast] at hprev
    have h4s : (4 : ℝ) ^ (k1 + 1) = 4 * 4 ^ k1 := by
      rw [pow_succ]
      ring
    rw [h4s] at hE
    have hd2pos : (0 : ℝ) < (d : ℝ) ^ 2 := by positivity
    nlinarith
  · push Not at hex
    have hJ := hex J le_rfl
    simp only [Nat.sub_self, zero_add, Nat.cast_ofNat] at hJ
    have hd2pos : (0 : ℝ) < (d : ℝ) ^ 2 := by positivity
    nlinarith

end ThresholdHC.ArbitraryLawAdaptation
