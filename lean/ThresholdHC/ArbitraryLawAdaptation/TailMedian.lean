import ThresholdHC.ArbitraryLawAdaptation.TailProbe
import Mathlib.Data.Fin.Tuple.Sort

/-! The median over tail probes: definitions and counting.

`m` probes run on separate streams of fresh coins. The certificate of the
procedure is the median of their certificates, the entry of rank `⌊m/2⌋` in
increasing order. This module defines the median and proves the two counting
facts that transfer a property of more than half of the probes to the median.
It also bounds the total charge on every path. No probability enters here. -/

noncomputable section
open Classical
namespace ThresholdHC.ArbitraryLawAdaptation

/-- Number of indices `j < m` with `p j`. -/
def blockCount (m : ℕ) (p : ℕ → Prop) : ℕ := ((Finset.range m).filter p).card

/-- The median of the first `m` values: the entry of rank `⌊m/2⌋` in increasing
order. It is `1` when `m = 0`. -/
def blockMedian (m : ℕ) (v : ℕ → ℝ) : ℝ :=
  if h : 0 < m then
    v (Tuple.sort (fun j : Fin m => v j) ⟨m / 2, Nat.div_lt_self h (by norm_num)⟩)
  else 1

/-- The median certificate of `m` probes at depth `J`. Probe `j` runs on stream
`ω j` with flip budget `b j` and coin cap `M j`. -/
def medianUpper (J m : ℕ) (b M : ℕ → ℕ) (ω : ℕ → ℕ → ℕ → Bool) : ℝ :=
  blockMedian m (fun j => probeUpper (probeCompleted J (b j) (M j) (ω j)))

/-- Flips charged to the `m` probes together. -/
def medianFlips (J m : ℕ) (b M : ℕ → ℕ) (ω : ℕ → ℕ → ℕ → Bool) : ℕ :=
  ∑ j ∈ Finset.range m, probeFlips J (b j) (M j) (ω j)

theorem blockCount_le (m : ℕ) (p : ℕ → Prop) : blockCount m p ≤ m := by
  unfold blockCount
  calc ((Finset.range m).filter p).card ≤ (Finset.range m).card := Finset.card_filter_le _ _
    _ = m := Finset.card_range m

theorem blockCount_mono {m : ℕ} {p q : ℕ → Prop} (h : ∀ j < m, p j → q j) :
    blockCount m p ≤ blockCount m q := by
  unfold blockCount
  apply Finset.card_le_card
  intro j hj
  rw [Finset.mem_filter] at hj ⊢
  exact ⟨hj.1, h j (Finset.mem_range.mp hj.1) hj.2⟩

/-- A finite set of indices below `m` that satisfy `p` is counted. -/
theorem card_le_blockCount {m : ℕ} {p : ℕ → Prop} (T : Finset ℕ) (hT : ∀ j ∈ T, j < m ∧ p j) :
    T.card ≤ blockCount m p := by
  unfold blockCount
  apply Finset.card_le_card
  intro j hj
  rw [Finset.mem_filter, Finset.mem_range]
  exact hT j hj

/-- The indices that satisfy `p` and those that do not partition the first `m`. -/
theorem blockCount_add_not (m : ℕ) (p : ℕ → Prop) :
    blockCount m p + blockCount m (fun j => ¬ p j) = m := by
  unfold blockCount
  rw [Finset.card_filter_add_card_filter_not, Finset.card_range]

theorem blockMedian_zero (v : ℕ → ℝ) : blockMedian 0 v = 1 := by
  simp [blockMedian]

/-- The median is one of the `m` values. -/
theorem blockMedian_eq_value {m : ℕ} (hm : 0 < m) (v : ℕ → ℝ) :
    ∃ j < m, blockMedian m v = v j := by
  unfold blockMedian
  rw [dite_eq_left hm]
  exact ⟨_, (Tuple.sort (fun j : Fin m => v j) ⟨m / 2, Nat.div_lt_self hm (by norm_num)⟩).isLt,
    rfl⟩

/-- If more than half of the values are at most `c`, so is the median. -/
theorem blockMedian_le {m : ℕ} {v : ℕ → ℝ} {c : ℝ}
    (h : m < 2 * blockCount m (fun j => v j ≤ c)) : blockMedian m v ≤ c := by
  have hm : 0 < m := by
    by_contra h0
    have hz : m = 0 := by omega
    subst hz
    simp [blockCount] at h
  unfold blockMedian
  rw [dite_eq_left hm]
  by_contra hc
  have hmono : Monotone ((fun j : Fin m => v j) ∘ Tuple.sort (fun j : Fin m => v j)) :=
    Tuple.monotone_sort _
  have hle := card_le_blockCount (m := m) (p := fun j => ¬ v j ≤ c)
    ((Finset.Ici (⟨m / 2, Nat.div_lt_self hm (by norm_num)⟩ : Fin m)).image
      (fun i => ((Tuple.sort (fun j : Fin m => v j) i : Fin m) : ℕ))) (by
    intro j hj
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hj
    refine ⟨(Tuple.sort (fun j : Fin m => v j) i).isLt, fun hle => hc ?_⟩
    exact le_trans (hmono (Finset.mem_Ici.mp hi)) hle)
  have hcard : ((Finset.Ici (⟨m / 2, Nat.div_lt_self hm (by norm_num)⟩ : Fin m)).image
      (fun i => ((Tuple.sort (fun j : Fin m => v j) i : Fin m) : ℕ))).card = m - m / 2 := by
    rw [Finset.card_image_of_injective _ (fun a b hab =>
      (Tuple.sort (fun j : Fin m => v j)).injective (Fin.val_injective hab)), Fin.card_Ici]
  have hadd := blockCount_add_not m (fun j => v j ≤ c)
  rw [hcard] at hle
  omega

/-- If more than half of the values are at least `a`, so is the median. -/
theorem le_blockMedian {m : ℕ} {v : ℕ → ℝ} {a : ℝ}
    (h : m < 2 * blockCount m (fun j => a ≤ v j)) : a ≤ blockMedian m v := by
  have hm : 0 < m := by
    by_contra h0
    have hz : m = 0 := by omega
    subst hz
    simp [blockCount] at h
  unfold blockMedian
  rw [dite_eq_left hm]
  by_contra hc
  have hmono : Monotone ((fun j : Fin m => v j) ∘ Tuple.sort (fun j : Fin m => v j)) :=
    Tuple.monotone_sort _
  have hle := card_le_blockCount (m := m) (p := fun j => ¬ a ≤ v j)
    ((Finset.Iic (⟨m / 2, Nat.div_lt_self hm (by norm_num)⟩ : Fin m)).image
      (fun i => ((Tuple.sort (fun j : Fin m => v j) i : Fin m) : ℕ))) (by
    intro j hj
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hj
    refine ⟨(Tuple.sort (fun j : Fin m => v j) i).isLt, fun hle => hc ?_⟩
    exact le_trans hle (hmono (Finset.mem_Iic.mp hi)))
  have hcard : ((Finset.Iic (⟨m / 2, Nat.div_lt_self hm (by norm_num)⟩ : Fin m)).image
      (fun i => ((Tuple.sort (fun j : Fin m => v j) i : Fin m) : ℕ))).card = m / 2 + 1 := by
    rw [Finset.card_image_of_injective _ (fun a b hab =>
      (Tuple.sort (fun j : Fin m => v j)).injective (Fin.val_injective hab)), Fin.card_Iic]
  have hadd := blockCount_add_not m (fun j => a ≤ v j)
  rw [hcard] at hle
  omega

theorem medianUpper_pos (J m : ℕ) (b M : ℕ → ℕ) (ω : ℕ → ℕ → ℕ → Bool) :
    0 < medianUpper J m b M ω := by
  unfold medianUpper
  rcases Nat.eq_zero_or_pos m with h0 | hm
  · rw [h0, blockMedian_zero]
    exact one_pos
  · obtain ⟨j, -, hj⟩ := blockMedian_eq_value hm
      (fun j => probeUpper (probeCompleted J (b j) (M j) (ω j)))
    rw [hj]
    exact probeUpper_pos _

/-- The median certificate lies in `[0,1]`. -/
theorem medianUpper_le_one (J m : ℕ) (b M : ℕ → ℕ) (ω : ℕ → ℕ → ℕ → Bool) :
    medianUpper J m b M ω ≤ 1 := by
  unfold medianUpper
  rcases Nat.eq_zero_or_pos m with h0 | hm
  · rw [h0, blockMedian_zero]
  · obtain ⟨j, -, hj⟩ := blockMedian_eq_value hm
      (fun j => probeUpper (probeCompleted J (b j) (M j) (ω j)))
    rw [hj]
    exact probeUpper_le_one _

/-- The flip budgets are a pathwise cap on the total charge. -/
theorem medianFlips_le (J m : ℕ) (b M : ℕ → ℕ) (ω : ℕ → ℕ → ℕ → Bool) :
    medianFlips J m b M ω ≤ ∑ j ∈ Finset.range m, b j := by
  unfold medianFlips
  exact Finset.sum_le_sum fun j _ => probeFlips_le J (b j) (M j) (ω j)

/-- With a common budget `b` for every probe, the total charge is at most
`m b` on every path. -/
theorem medianFlips_le_common (J m b : ℕ) (M : ℕ → ℕ) (ω : ℕ → ℕ → ℕ → Bool) :
    medianFlips J m (fun _ => b) M ω ≤ m * b := by
  have h := medianFlips_le J m (fun _ => b) M ω
  simpa using h

end ThresholdHC.ArbitraryLawAdaptation
