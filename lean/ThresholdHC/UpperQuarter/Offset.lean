import ThresholdHC.UpperSign.Offset

/-! The offset sums of the four bands of the first grid point.

For the band `k` of the first grid point `s` at or above the split `19/20`, the
levels below the split add at most `B_k*sqrt s` (`Grid`), and the levels from `s`
on add the cap terms `capTerm (2^i*s)`. Each band is split into pieces, chosen
and checked in exact rational arithmetic by a script; on each piece the first
six cap terms are bounded by monotonicity and an eight-term Taylor sum, and the
rest by `1/1000`. -/
noncomputable section
namespace ThresholdHC.UpperQuarter
open MeasureTheory ProbabilityTheory Finset ThresholdHC.UpperSign

section QuarterOffset
open Real Uniform713

theorem quarter_piece_0_0 {s : ℝ} (ha : (19 / 20 : ℝ) ≤ s) (hb : s ≤ (391 / 400 : ℝ)) :
    (24 / 25 : ℝ) * Real.sqrt s +
      (UpperDisagreement.capTerm s + UpperDisagreement.capTerm (2 * s) + UpperDisagreement.capTerm (4 * s) +
        UpperDisagreement.capTerm (8 * s) + UpperDisagreement.capTerm (16 * s) + UpperDisagreement.capTerm (32 * s)) + 1 / 1000 ≤ (89 / 50 : ℝ) := by
  have e := scaled_sqrt_le (A := (24 / 25 : ℝ)) (s := s) (b := (391 / 400 : ℝ)) (h := (989 / 1000 : ℝ)) (by norm_num) hb (by norm_num) (by norm_num)
  have b0 := UpperDisagreement.capTerm_le_band (t := s) (lo := (19 / 20 : ℝ)) (hi := (391 / 400 : ℝ)) (h := (989 / 1000 : ℝ)) (e₁ := (14969 / 100000 : ℝ)) (e₂ := (1547 / 4000 : ℝ)) (c := (531 / 1000 : ℝ))
    ha hb (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num)
  have b1 := UpperDisagreement.capTerm_le_band (t := 2 * s) (lo := (19 / 10 : ℝ)) (hi := (391 / 200 : ℝ)) (h := (1399 / 1000 : ℝ)) (e₁ := (2331 / 100000 : ℝ)) (e₂ := (14969 / 100000 : ℝ)) (c := (243 / 1000 : ℝ))
    (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num)
  have b2 := UpperDisagreement.capTerm_le_band (t := 4 * s) (lo := (19 / 5 : ℝ)) (hi := (391 / 100 : ℝ)) (h := (989 / 500 : ℝ)) (e₁ := (99 / 100000 : ℝ)) (e₂ := (2331 / 100000 : ℝ)) (c := (49 / 1000 : ℝ))
    (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num)
  have b3 := UpperDisagreement.capTerm_le_band (t := 8 * s) (lo := (38 / 5 : ℝ)) (hi := (391 / 50 : ℝ)) (h := (2797 / 1000 : ℝ)) (e₁ := (1 / 50000 : ℝ)) (e₂ := (99 / 100000 : ℝ)) (c := (3 / 1000 : ℝ))
    (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num)
  have b4 := UpperDisagreement.capTerm_le_band (t := 16 * s) (lo := (76 / 5 : ℝ)) (hi := (391 / 25 : ℝ)) (h := (791 / 200 : ℝ)) (e₁ := (1 / 100000 : ℝ)) (e₂ := (1 / 50000 : ℝ)) (c := (1 / 1000 : ℝ))
    (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num)
  have b5 := UpperDisagreement.capTerm_le_band (t := 32 * s) (lo := (152 / 5 : ℝ)) (hi := (782 / 25 : ℝ)) (h := (5593 / 1000 : ℝ)) (e₁ := (1 / 100000 : ℝ)) (e₂ := (1 / 100000 : ℝ)) (c := (1 / 1000 : ℝ))
    (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num)
  linarith

theorem quarter_piece_0_1 {s : ℝ} (ha : (391 / 400 : ℝ) ≤ s) (hb : s ≤ (817 / 800 : ℝ)) :
    (24 / 25 : ℝ) * Real.sqrt s +
      (UpperDisagreement.capTerm s + UpperDisagreement.capTerm (2 * s) + UpperDisagreement.capTerm (4 * s) +
        UpperDisagreement.capTerm (8 * s) + UpperDisagreement.capTerm (16 * s) + UpperDisagreement.capTerm (32 * s)) + 1 / 1000 ≤ (89 / 50 : ℝ) := by
  have e := scaled_sqrt_le (A := (24 / 25 : ℝ)) (s := s) (b := (817 / 800 : ℝ)) (h := (1011 / 1000 : ℝ)) (by norm_num) hb (by norm_num) (by norm_num)
  have b0 := UpperDisagreement.capTerm_le_band (t := s) (lo := (391 / 400 : ℝ)) (hi := (817 / 800 : ℝ)) (h := (1011 / 1000 : ℝ)) (e₁ := (1417 / 10000 : ℝ)) (e₂ := (18813 / 50000 : ℝ)) (c := (131 / 250 : ℝ))
    ha hb (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num)
  have b1 := UpperDisagreement.capTerm_le_band (t := 2 * s) (lo := (391 / 200 : ℝ)) (hi := (817 / 400 : ℝ)) (h := (143 / 100 : ℝ)) (e₁ := (2101 / 100000 : ℝ)) (e₂ := (1417 / 10000 : ℝ)) (c := (233 / 1000 : ℝ))
    (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num)
  have b2 := UpperDisagreement.capTerm_le_band (t := 4 * s) (lo := (391 / 100 : ℝ)) (hi := (817 / 200 : ℝ)) (h := (1011 / 500 : ℝ)) (e₁ := (21 / 25000 : ℝ)) (e₂ := (2101 / 100000 : ℝ)) (c := (9 / 200 : ℝ))
    (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num)
  have b3 := UpperDisagreement.capTerm_le_band (t := 8 * s) (lo := (391 / 50 : ℝ)) (hi := (817 / 100 : ℝ)) (h := (2859 / 1000 : ℝ)) (e₁ := (1 / 50000 : ℝ)) (e₂ := (21 / 25000 : ℝ)) (c := (3 / 1000 : ℝ))
    (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num)
  have b4 := UpperDisagreement.capTerm_le_band (t := 16 * s) (lo := (391 / 25 : ℝ)) (hi := (817 / 50 : ℝ)) (h := (4043 / 1000 : ℝ)) (e₁ := (1 / 100000 : ℝ)) (e₂ := (1 / 50000 : ℝ)) (c := (1 / 1000 : ℝ))
    (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num)
  have b5 := UpperDisagreement.capTerm_le_band (t := 32 * s) (lo := (782 / 25 : ℝ)) (hi := (817 / 25 : ℝ)) (h := (5717 / 1000 : ℝ)) (e₁ := (1 / 100000 : ℝ)) (e₂ := (1 / 100000 : ℝ)) (c := (1 / 1000 : ℝ))
    (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num)
  linarith

theorem quarter_piece_0_2 {s : ℝ} (ha : (817 / 800 : ℝ) ≤ s) (hb : s ≤ (873 / 800 : ℝ)) :
    (24 / 25 : ℝ) * Real.sqrt s +
      (UpperDisagreement.capTerm s + UpperDisagreement.capTerm (2 * s) + UpperDisagreement.capTerm (4 * s) +
        UpperDisagreement.capTerm (8 * s) + UpperDisagreement.capTerm (16 * s) + UpperDisagreement.capTerm (32 * s)) + 1 / 1000 ≤ (89 / 50 : ℝ) := by
  have e := scaled_sqrt_le (A := (24 / 25 : ℝ)) (s := s) (b := (873 / 800 : ℝ)) (h := (209 / 200 : ℝ)) (by norm_num) hb (by norm_num) (by norm_num)
  have b0 := UpperDisagreement.capTerm_le_band (t := s) (lo := (817 / 800 : ℝ)) (hi := (873 / 800 : ℝ)) (h := (209 / 200 : ℝ)) (e₁ := (12987 / 100000 : ℝ)) (e₂ := (7203 / 20000 : ℝ)) (c := (513 / 1000 : ℝ))
    ha hb (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num)
  have b1 := UpperDisagreement.capTerm_le_band (t := 2 * s) (lo := (817 / 400 : ℝ)) (hi := (873 / 400 : ℝ)) (h := (739 / 500 : ℝ)) (e₁ := (1783 / 100000 : ℝ)) (e₂ := (12987 / 100000 : ℝ)) (c := (219 / 1000 : ℝ))
    (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num)
  have b2 := UpperDisagreement.capTerm_le_band (t := 4 * s) (lo := (817 / 200 : ℝ)) (hi := (873 / 200 : ℝ)) (h := (209 / 100 : ℝ)) (e₁ := (33 / 50000 : ℝ)) (e₂ := (1783 / 100000 : ℝ)) (c := (39 / 1000 : ℝ))
    (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num)
  have b3 := UpperDisagreement.capTerm_le_band (t := 8 * s) (lo := (817 / 100 : ℝ)) (hi := (873 / 100 : ℝ)) (h := (591 / 200 : ℝ)) (e₁ := (1 / 100000 : ℝ)) (e₂ := (33 / 50000 : ℝ)) (c := (1 / 500 : ℝ))
    (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num)
  have b4 := UpperDisagreement.capTerm_le_band (t := 16 * s) (lo := (817 / 50 : ℝ)) (hi := (873 / 50 : ℝ)) (h := (4179 / 1000 : ℝ)) (e₁ := (1 / 100000 : ℝ)) (e₂ := (1 / 100000 : ℝ)) (c := (1 / 1000 : ℝ))
    (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num)
  have b5 := UpperDisagreement.capTerm_le_band (t := 32 * s) (lo := (817 / 25 : ℝ)) (hi := (873 / 25 : ℝ)) (h := (591 / 100 : ℝ)) (e₁ := (1 / 100000 : ℝ)) (e₂ := (1 / 100000 : ℝ)) (c := (1 / 1000 : ℝ))
    (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num)
  linarith

theorem quarter_piece_0_3 {s : ℝ} (ha : (873 / 800 : ℝ) ≤ s) (hb : s ≤ (19 / 16 : ℝ)) :
    (24 / 25 : ℝ) * Real.sqrt s +
      (UpperDisagreement.capTerm s + UpperDisagreement.capTerm (2 * s) + UpperDisagreement.capTerm (4 * s) +
        UpperDisagreement.capTerm (8 * s) + UpperDisagreement.capTerm (16 * s) + UpperDisagreement.capTerm (32 * s)) + 1 / 1000 ≤ (89 / 50 : ℝ) := by
  have e := scaled_sqrt_le (A := (24 / 25 : ℝ)) (s := s) (b := (19 / 16 : ℝ)) (h := (109 / 100 : ℝ)) (by norm_num) hb (by norm_num) (by norm_num)
  have b0 := UpperDisagreement.capTerm_le_band (t := s) (lo := (873 / 800 : ℝ)) (hi := (19 / 16 : ℝ)) (h := (109 / 100 : ℝ)) (e₁ := (5649 / 50000 : ℝ)) (e₂ := (33581 / 100000 : ℝ)) (c := (49 / 100 : ℝ))
    ha hb (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num)
  have b1 := UpperDisagreement.capTerm_le_band (t := 2 * s) (lo := (873 / 400 : ℝ)) (hi := (19 / 8 : ℝ)) (h := (771 / 500 : ℝ)) (e₁ := (43 / 3125 : ℝ)) (e₂ := (5649 / 50000 : ℝ)) (c := (49 / 250 : ℝ))
    (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num)
  have b2 := UpperDisagreement.capTerm_le_band (t := 4 * s) (lo := (873 / 200 : ℝ)) (hi := (19 / 4 : ℝ)) (h := (109 / 50 : ℝ)) (e₁ := (23 / 50000 : ℝ)) (e₂ := (43 / 3125 : ℝ)) (c := (31 / 1000 : ℝ))
    (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num)
  have b3 := UpperDisagreement.capTerm_le_band (t := 8 * s) (lo := (873 / 100 : ℝ)) (hi := (19 / 2 : ℝ)) (h := (3083 / 1000 : ℝ)) (e₁ := (1 / 100000 : ℝ)) (e₂ := (23 / 50000 : ℝ)) (c := (1 / 500 : ℝ))
    (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num)
  have b4 := UpperDisagreement.capTerm_le_band (t := 16 * s) (lo := (873 / 50 : ℝ)) (hi := (19 : ℝ)) (h := (4359 / 1000 : ℝ)) (e₁ := (1 / 100000 : ℝ)) (e₂ := (1 / 100000 : ℝ)) (c := (1 / 1000 : ℝ))
    (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num)
  have b5 := UpperDisagreement.capTerm_le_band (t := 32 * s) (lo := (873 / 25 : ℝ)) (hi := (38 : ℝ)) (h := (1233 / 200 : ℝ)) (e₁ := (1 / 100000 : ℝ)) (e₂ := (1 / 100000 : ℝ)) (c := (1 / 1000 : ℝ))
    (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num)
  linarith

/-- The offset sum of band 0. -/
theorem quarter_offset_0 (s : ℝ) (h1 : (19 / 20 : ℝ) ≤ s) (h2 : s ≤ (19 / 16 : ℝ)) (I : ℕ) :
    (24 / 25 : ℝ) * Real.sqrt s + ∑ i ∈ range I, UpperDisagreement.capTerm (2 ^ i * s) ≤ (89 / 50 : ℝ) := by
  have hr := UpperDisagreement.cap_offset_reduce s (by linarith) I
  have hred : (24 / 25 : ℝ) * Real.sqrt s + ∑ i ∈ range I, UpperDisagreement.capTerm (2 ^ i * s) ≤
      (24 / 25 : ℝ) * Real.sqrt s +
      (UpperDisagreement.capTerm s + UpperDisagreement.capTerm (2 * s) + UpperDisagreement.capTerm (4 * s) +
        UpperDisagreement.capTerm (8 * s) + UpperDisagreement.capTerm (16 * s) + UpperDisagreement.capTerm (32 * s)) + 1 / 1000 := by linarith
  refine hred.trans ?_
  rcases le_or_gt s (391 / 400 : ℝ) with hk | hp
  · exact quarter_piece_0_0 h1 hk
  rcases le_or_gt s (817 / 800 : ℝ) with hk | hp
  · exact quarter_piece_0_1 hp.le hk
  rcases le_or_gt s (873 / 800 : ℝ) with hk | hp
  · exact quarter_piece_0_2 hp.le hk
  exact quarter_piece_0_3 hp.le h2

theorem quarter_piece_1_0 {s : ℝ} (ha : (19 / 16 : ℝ) ≤ s) (hb : s ≤ (517 / 400 : ℝ)) :
    (997 / 1000 : ℝ) * Real.sqrt s +
      (UpperDisagreement.capTerm s + UpperDisagreement.capTerm (2 * s) + UpperDisagreement.capTerm (4 * s) +
        UpperDisagreement.capTerm (8 * s) + UpperDisagreement.capTerm (16 * s) + UpperDisagreement.capTerm (32 * s)) + 1 / 1000 ≤ (89 / 50 : ℝ) := by
  have e := scaled_sqrt_le (A := (997 / 1000 : ℝ)) (s := s) (b := (517 / 400 : ℝ)) (h := (1137 / 1000 : ℝ)) (by norm_num) hb (by norm_num) (by norm_num)
  have b0 := UpperDisagreement.capTerm_le_band (t := s) (lo := (19 / 16 : ℝ)) (hi := (517 / 400 : ℝ)) (h := (1137 / 1000 : ℝ)) (e₁ := (9331 / 100000 : ℝ)) (e₂ := (61 / 200 : ℝ)) (c := (453 / 1000 : ℝ))
    ha hb (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num)
  have b1 := UpperDisagreement.capTerm_le_band (t := 2 * s) (lo := (19 / 8 : ℝ)) (hi := (517 / 200 : ℝ)) (h := (201 / 125 : ℝ)) (e₁ := (971 / 100000 : ℝ)) (e₂ := (9331 / 100000 : ℝ)) (c := (83 / 500 : ℝ))
    (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num)
  have b2 := UpperDisagreement.capTerm_le_band (t := 4 * s) (lo := (19 / 4 : ℝ)) (hi := (517 / 100 : ℝ)) (h := (1137 / 500 : ℝ)) (e₁ := (7 / 25000 : ℝ)) (e₂ := (971 / 100000 : ℝ)) (c := (23 / 1000 : ℝ))
    (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num)
  have b3 := UpperDisagreement.capTerm_le_band (t := 8 * s) (lo := (19 / 2 : ℝ)) (hi := (517 / 50 : ℝ)) (h := (402 / 125 : ℝ)) (e₁ := (1 / 100000 : ℝ)) (e₂ := (7 / 25000 : ℝ)) (c := (1 / 1000 : ℝ))
    (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num)
  have b4 := UpperDisagreement.capTerm_le_band (t := 16 * s) (lo := (19 : ℝ)) (hi := (517 / 25 : ℝ)) (h := (1137 / 250 : ℝ)) (e₁ := (1 / 100000 : ℝ)) (e₂ := (1 / 100000 : ℝ)) (c := (1 / 1000 : ℝ))
    (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num)
  have b5 := UpperDisagreement.capTerm_le_band (t := 32 * s) (lo := (38 : ℝ)) (hi := (1034 / 25 : ℝ)) (h := (804 / 125 : ℝ)) (e₁ := (1 / 100000 : ℝ)) (e₂ := (1 / 100000 : ℝ)) (c := (1 / 1000 : ℝ))
    (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num)
  linarith

theorem quarter_piece_1_1 {s : ℝ} (ha : (517 / 400 : ℝ) ≤ s) (hb : s ≤ (57 / 40 : ℝ)) :
    (997 / 1000 : ℝ) * Real.sqrt s +
      (UpperDisagreement.capTerm s + UpperDisagreement.capTerm (2 * s) + UpperDisagreement.capTerm (4 * s) +
        UpperDisagreement.capTerm (8 * s) + UpperDisagreement.capTerm (16 * s) + UpperDisagreement.capTerm (32 * s)) + 1 / 1000 ≤ (89 / 50 : ℝ) := by
  have e := scaled_sqrt_le (A := (997 / 1000 : ℝ)) (s := s) (b := (57 / 40 : ℝ)) (h := (597 / 500 : ℝ)) (by norm_num) hb (by norm_num) (by norm_num)
  have b0 := UpperDisagreement.capTerm_le_band (t := s) (lo := (517 / 400 : ℝ)) (hi := (57 / 40 : ℝ)) (h := (597 / 500 : ℝ)) (e₁ := (7579 / 100000 : ℝ)) (e₂ := (27461 / 100000 : ℝ)) (c := (419 / 1000 : ℝ))
    ha hb (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num)
  have b1 := UpperDisagreement.capTerm_le_band (t := 2 * s) (lo := (517 / 200 : ℝ)) (hi := (57 / 20 : ℝ)) (h := (1689 / 1000 : ℝ)) (e₁ := (671 / 100000 : ℝ)) (e₂ := (7579 / 100000 : ℝ)) (c := (7 / 50 : ℝ))
    (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num)
  have b2 := UpperDisagreement.capTerm_le_band (t := 4 * s) (lo := (517 / 100 : ℝ)) (hi := (57 / 10 : ℝ)) (h := (597 / 250 : ℝ)) (e₁ := (17 / 100000 : ℝ)) (e₂ := (671 / 100000 : ℝ)) (c := (17 / 1000 : ℝ))
    (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num)
  have b3 := UpperDisagreement.capTerm_le_band (t := 8 * s) (lo := (517 / 50 : ℝ)) (hi := (57 / 5 : ℝ)) (h := (3377 / 1000 : ℝ)) (e₁ := (1 / 100000 : ℝ)) (e₂ := (17 / 100000 : ℝ)) (c := (1 / 1000 : ℝ))
    (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num)
  have b4 := UpperDisagreement.capTerm_le_band (t := 16 * s) (lo := (517 / 25 : ℝ)) (hi := (114 / 5 : ℝ)) (h := (191 / 40 : ℝ)) (e₁ := (1 / 100000 : ℝ)) (e₂ := (1 / 100000 : ℝ)) (c := (1 / 1000 : ℝ))
    (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num)
  have b5 := UpperDisagreement.capTerm_le_band (t := 32 * s) (lo := (1034 / 25 : ℝ)) (hi := (228 / 5 : ℝ)) (h := (6753 / 1000 : ℝ)) (e₁ := (1 / 100000 : ℝ)) (e₂ := (1 / 100000 : ℝ)) (c := (1 / 1000 : ℝ))
    (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num)
  linarith

/-- The offset sum of band 1. -/
theorem quarter_offset_1 (s : ℝ) (h1 : (19 / 16 : ℝ) ≤ s) (h2 : s ≤ (57 / 40 : ℝ)) (I : ℕ) :
    (997 / 1000 : ℝ) * Real.sqrt s + ∑ i ∈ range I, UpperDisagreement.capTerm (2 ^ i * s) ≤ (89 / 50 : ℝ) := by
  have hr := UpperDisagreement.cap_offset_reduce s (by linarith) I
  have hred : (997 / 1000 : ℝ) * Real.sqrt s + ∑ i ∈ range I, UpperDisagreement.capTerm (2 ^ i * s) ≤
      (997 / 1000 : ℝ) * Real.sqrt s +
      (UpperDisagreement.capTerm s + UpperDisagreement.capTerm (2 * s) + UpperDisagreement.capTerm (4 * s) +
        UpperDisagreement.capTerm (8 * s) + UpperDisagreement.capTerm (16 * s) + UpperDisagreement.capTerm (32 * s)) + 1 / 1000 := by linarith
  refine hred.trans ?_
  rcases le_or_gt s (517 / 400 : ℝ) with hk | hp
  · exact quarter_piece_1_0 h1 hk
  exact quarter_piece_1_1 hp.le h2

theorem quarter_piece_2_0 {s : ℝ} (ha : (57 / 40 : ℝ) ≤ s) (hb : s ≤ (123 / 80 : ℝ)) :
    (207 / 200 : ℝ) * Real.sqrt s +
      (UpperDisagreement.capTerm s + UpperDisagreement.capTerm (2 * s) + UpperDisagreement.capTerm (4 * s) +
        UpperDisagreement.capTerm (8 * s) + UpperDisagreement.capTerm (16 * s) + UpperDisagreement.capTerm (32 * s)) + 1 / 1000 ≤ (89 / 50 : ℝ) := by
  have e := scaled_sqrt_le (A := (207 / 200 : ℝ)) (s := s) (b := (123 / 80 : ℝ)) (h := (31 / 25 : ℝ)) (by norm_num) hb (by norm_num) (by norm_num)
  have b0 := UpperDisagreement.capTerm_le_band (t := s) (lo := (57 / 40 : ℝ)) (hi := (123 / 80 : ℝ)) (h := (31 / 25 : ℝ)) (e₁ := (5837 / 100000 : ℝ)) (e₂ := (12027 / 50000 : ℝ)) (c := (371 / 1000 : ℝ))
    ha hb (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num)
  have b1 := UpperDisagreement.capTerm_le_band (t := 2 * s) (lo := (57 / 20 : ℝ)) (hi := (123 / 40 : ℝ)) (h := (877 / 500 : ℝ)) (e₁ := (427 / 100000 : ℝ)) (e₂ := (5837 / 100000 : ℝ)) (c := (11 / 100 : ℝ))
    (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num)
  have b2 := UpperDisagreement.capTerm_le_band (t := 4 * s) (lo := (57 / 10 : ℝ)) (hi := (123 / 20 : ℝ)) (h := (62 / 25 : ℝ)) (e₁ := (1 / 10000 : ℝ)) (e₂ := (427 / 100000 : ℝ)) (c := (11 / 1000 : ℝ))
    (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num)
  have b3 := UpperDisagreement.capTerm_le_band (t := 8 * s) (lo := (57 / 5 : ℝ)) (hi := (123 / 10 : ℝ)) (h := (877 / 250 : ℝ)) (e₁ := (1 / 100000 : ℝ)) (e₂ := (1 / 10000 : ℝ)) (c := (1 / 1000 : ℝ))
    (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num)
  have b4 := UpperDisagreement.capTerm_le_band (t := 16 * s) (lo := (114 / 5 : ℝ)) (hi := (123 / 5 : ℝ)) (h := (124 / 25 : ℝ)) (e₁ := (1 / 100000 : ℝ)) (e₂ := (1 / 100000 : ℝ)) (c := (1 / 1000 : ℝ))
    (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num)
  have b5 := UpperDisagreement.capTerm_le_band (t := 32 * s) (lo := (228 / 5 : ℝ)) (hi := (246 / 5 : ℝ)) (h := (1403 / 200 : ℝ)) (e₁ := (1 / 100000 : ℝ)) (e₂ := (1 / 100000 : ℝ)) (c := (1 / 1000 : ℝ))
    (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num)
  linarith

theorem quarter_piece_2_1 {s : ℝ} (ha : (123 / 80 : ℝ) ≤ s) (hb : s ≤ (133 / 80 : ℝ)) :
    (207 / 200 : ℝ) * Real.sqrt s +
      (UpperDisagreement.capTerm s + UpperDisagreement.capTerm (2 * s) + UpperDisagreement.capTerm (4 * s) +
        UpperDisagreement.capTerm (8 * s) + UpperDisagreement.capTerm (16 * s) + UpperDisagreement.capTerm (32 * s)) + 1 / 1000 ≤ (89 / 50 : ℝ) := by
  have e := scaled_sqrt_le (A := (207 / 200 : ℝ)) (s := s) (b := (133 / 80 : ℝ)) (h := (129 / 100 : ℝ)) (by norm_num) hb (by norm_num) (by norm_num)
  have b0 := UpperDisagreement.capTerm_le_band (t := s) (lo := (123 / 80 : ℝ)) (hi := (133 / 80 : ℝ)) (h := (129 / 100 : ℝ)) (e₁ := (4683 / 100000 : ℝ)) (e₂ := (21497 / 100000 : ℝ)) (c := (169 / 500 : ℝ))
    ha hb (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num)
  have b1 := UpperDisagreement.capTerm_le_band (t := 2 * s) (lo := (123 / 40 : ℝ)) (hi := (133 / 40 : ℝ)) (h := (228 / 125 : ℝ)) (e₁ := (37 / 12500 : ℝ)) (e₂ := (4683 / 100000 : ℝ)) (c := (91 / 1000 : ℝ))
    (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num)
  have b2 := UpperDisagreement.capTerm_le_band (t := 4 * s) (lo := (123 / 20 : ℝ)) (hi := (133 / 20 : ℝ)) (h := (2579 / 1000 : ℝ)) (e₁ := (3 / 50000 : ℝ)) (e₂ := (37 / 12500 : ℝ)) (c := (1 / 125 : ℝ))
    (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num)
  have b3 := UpperDisagreement.capTerm_le_band (t := 8 * s) (lo := (123 / 10 : ℝ)) (hi := (133 / 10 : ℝ)) (h := (3647 / 1000 : ℝ)) (e₁ := (1 / 100000 : ℝ)) (e₂ := (3 / 50000 : ℝ)) (c := (1 / 1000 : ℝ))
    (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num)
  have b4 := UpperDisagreement.capTerm_le_band (t := 16 * s) (lo := (123 / 5 : ℝ)) (hi := (133 / 5 : ℝ)) (h := (2579 / 500 : ℝ)) (e₁ := (1 / 100000 : ℝ)) (e₂ := (1 / 100000 : ℝ)) (c := (1 / 1000 : ℝ))
    (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num)
  have b5 := UpperDisagreement.capTerm_le_band (t := 32 * s) (lo := (246 / 5 : ℝ)) (hi := (266 / 5 : ℝ)) (h := (3647 / 500 : ℝ)) (e₁ := (1 / 100000 : ℝ)) (e₂ := (1 / 100000 : ℝ)) (c := (1 / 1000 : ℝ))
    (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num)
  linarith

/-- The offset sum of band 2. -/
theorem quarter_offset_2 (s : ℝ) (h1 : (57 / 40 : ℝ) ≤ s) (h2 : s ≤ (133 / 80 : ℝ)) (I : ℕ) :
    (207 / 200 : ℝ) * Real.sqrt s + ∑ i ∈ range I, UpperDisagreement.capTerm (2 ^ i * s) ≤ (89 / 50 : ℝ) := by
  have hr := UpperDisagreement.cap_offset_reduce s (by linarith) I
  have hred : (207 / 200 : ℝ) * Real.sqrt s + ∑ i ∈ range I, UpperDisagreement.capTerm (2 ^ i * s) ≤
      (207 / 200 : ℝ) * Real.sqrt s +
      (UpperDisagreement.capTerm s + UpperDisagreement.capTerm (2 * s) + UpperDisagreement.capTerm (4 * s) +
        UpperDisagreement.capTerm (8 * s) + UpperDisagreement.capTerm (16 * s) + UpperDisagreement.capTerm (32 * s)) + 1 / 1000 := by linarith
  refine hred.trans ?_
  rcases le_or_gt s (123 / 80 : ℝ) with hk | hp
  · exact quarter_piece_2_0 h1 hk
  exact quarter_piece_2_1 hp.le h2

theorem quarter_piece_3_0 {s : ℝ} (ha : (133 / 80 : ℝ) ≤ s) (hb : s ≤ (341 / 200 : ℝ)) :
    (1073 / 1000 : ℝ) * Real.sqrt s +
      (UpperDisagreement.capTerm s + UpperDisagreement.capTerm (2 * s) + UpperDisagreement.capTerm (4 * s) +
        UpperDisagreement.capTerm (8 * s) + UpperDisagreement.capTerm (16 * s) + UpperDisagreement.capTerm (32 * s)) + 1 / 1000 ≤ (89 / 50 : ℝ) := by
  have e := scaled_sqrt_le (A := (1073 / 1000 : ℝ)) (s := s) (b := (341 / 200 : ℝ)) (h := (653 / 500 : ℝ)) (by norm_num) hb (by norm_num) (by norm_num)
  have b0 := UpperDisagreement.capTerm_le_band (t := s) (lo := (133 / 80 : ℝ)) (hi := (341 / 200 : ℝ)) (h := (653 / 500 : ℝ)) (e₁ := (3673 / 100000 : ℝ)) (e₂ := (18973 / 100000 : ℝ)) (c := (37 / 125 : ℝ))
    ha hb (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num)
  have b1 := UpperDisagreement.capTerm_le_band (t := 2 * s) (lo := (133 / 40 : ℝ)) (hi := (341 / 100 : ℝ)) (h := (1847 / 1000 : ℝ)) (e₁ := (199 / 100000 : ℝ)) (e₂ := (3673 / 100000 : ℝ)) (c := (9 / 125 : ℝ))
    (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num)
  have b2 := UpperDisagreement.capTerm_le_band (t := 4 * s) (lo := (133 / 20 : ℝ)) (hi := (341 / 50 : ℝ)) (h := (653 / 250 : ℝ)) (e₁ := (1 / 25000 : ℝ)) (e₂ := (199 / 100000 : ℝ)) (c := (3 / 500 : ℝ))
    (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num)
  have b3 := UpperDisagreement.capTerm_le_band (t := 8 * s) (lo := (133 / 10 : ℝ)) (hi := (341 / 25 : ℝ)) (h := (1847 / 500 : ℝ)) (e₁ := (1 / 100000 : ℝ)) (e₂ := (1 / 25000 : ℝ)) (c := (1 / 1000 : ℝ))
    (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num)
  have b4 := UpperDisagreement.capTerm_le_band (t := 16 * s) (lo := (133 / 5 : ℝ)) (hi := (682 / 25 : ℝ)) (h := (653 / 125 : ℝ)) (e₁ := (1 / 100000 : ℝ)) (e₂ := (1 / 100000 : ℝ)) (c := (1 / 1000 : ℝ))
    (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num)
  have b5 := UpperDisagreement.capTerm_le_band (t := 32 * s) (lo := (266 / 5 : ℝ)) (hi := (1364 / 25 : ℝ)) (h := (7387 / 1000 : ℝ)) (e₁ := (1 / 100000 : ℝ)) (e₂ := (1 / 100000 : ℝ)) (c := (1 / 1000 : ℝ))
    (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num)
  linarith

theorem quarter_piece_3_1 {s : ℝ} (ha : (341 / 200 : ℝ) ≤ s) (hb : s ≤ (349 / 200 : ℝ)) :
    (1073 / 1000 : ℝ) * Real.sqrt s +
      (UpperDisagreement.capTerm s + UpperDisagreement.capTerm (2 * s) + UpperDisagreement.capTerm (4 * s) +
        UpperDisagreement.capTerm (8 * s) + UpperDisagreement.capTerm (16 * s) + UpperDisagreement.capTerm (32 * s)) + 1 / 1000 ≤ (89 / 50 : ℝ) := by
  have e := scaled_sqrt_le (A := (1073 / 1000 : ℝ)) (s := s) (b := (349 / 200 : ℝ)) (h := (1321 / 1000 : ℝ)) (by norm_num) hb (by norm_num) (by norm_num)
  have b0 := UpperDisagreement.capTerm_le_band (t := s) (lo := (341 / 200 : ℝ)) (hi := (349 / 200 : ℝ)) (h := (1321 / 1000 : ℝ)) (e₁ := (423 / 12500 : ℝ)) (e₂ := (3637 / 20000 : ℝ)) (c := (57 / 200 : ℝ))
    ha hb (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num)
  have b1 := UpperDisagreement.capTerm_le_band (t := 2 * s) (lo := (341 / 100 : ℝ)) (hi := (349 / 100 : ℝ)) (h := (1869 / 1000 : ℝ)) (e₁ := (7 / 4000 : ℝ)) (e₂ := (423 / 12500 : ℝ)) (c := (67 / 1000 : ℝ))
    (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num)
  have b2 := UpperDisagreement.capTerm_le_band (t := 4 * s) (lo := (341 / 50 : ℝ)) (hi := (349 / 50 : ℝ)) (h := (1321 / 500 : ℝ)) (e₁ := (1 / 25000 : ℝ)) (e₂ := (7 / 4000 : ℝ)) (c := (1 / 200 : ℝ))
    (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num)
  have b3 := UpperDisagreement.capTerm_le_band (t := 8 * s) (lo := (341 / 25 : ℝ)) (hi := (349 / 25 : ℝ)) (h := (3737 / 1000 : ℝ)) (e₁ := (1 / 100000 : ℝ)) (e₂ := (1 / 25000 : ℝ)) (c := (1 / 1000 : ℝ))
    (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num)
  have b4 := UpperDisagreement.capTerm_le_band (t := 16 * s) (lo := (682 / 25 : ℝ)) (hi := (698 / 25 : ℝ)) (h := (1321 / 250 : ℝ)) (e₁ := (1 / 100000 : ℝ)) (e₂ := (1 / 100000 : ℝ)) (c := (1 / 1000 : ℝ))
    (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num)
  have b5 := UpperDisagreement.capTerm_le_band (t := 32 * s) (lo := (1364 / 25 : ℝ)) (hi := (1396 / 25 : ℝ)) (h := (7473 / 1000 : ℝ)) (e₁ := (1 / 100000 : ℝ)) (e₂ := (1 / 100000 : ℝ)) (c := (1 / 1000 : ℝ))
    (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num)
  linarith

theorem quarter_piece_3_2 {s : ℝ} (ha : (349 / 200 : ℝ) ≤ s) (hb : s ≤ (1423 / 800 : ℝ)) :
    (1073 / 1000 : ℝ) * Real.sqrt s +
      (UpperDisagreement.capTerm s + UpperDisagreement.capTerm (2 * s) + UpperDisagreement.capTerm (4 * s) +
        UpperDisagreement.capTerm (8 * s) + UpperDisagreement.capTerm (16 * s) + UpperDisagreement.capTerm (32 * s)) + 1 / 1000 ≤ (89 / 50 : ℝ) := by
  have e := scaled_sqrt_le (A := (1073 / 1000 : ℝ)) (s := s) (b := (1423 / 800 : ℝ)) (h := (667 / 500 : ℝ)) (by norm_num) hb (by norm_num) (by norm_num)
  have b0 := UpperDisagreement.capTerm_le_band (t := s) (lo := (349 / 200 : ℝ)) (hi := (1423 / 800 : ℝ)) (h := (667 / 500 : ℝ)) (e₁ := (3133 / 100000 : ℝ)) (e₂ := (17473 / 100000 : ℝ)) (c := (11 / 40 : ℝ))
    ha hb (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num)
  have b1 := UpperDisagreement.capTerm_le_band (t := 2 * s) (lo := (349 / 100 : ℝ)) (hi := (1423 / 400 : ℝ)) (h := (1887 / 1000 : ℝ)) (e₁ := (31 / 20000 : ℝ)) (e₂ := (3133 / 100000 : ℝ)) (c := (63 / 1000 : ℝ))
    (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num)
  have b2 := UpperDisagreement.capTerm_le_band (t := 4 * s) (lo := (349 / 50 : ℝ)) (hi := (1423 / 200 : ℝ)) (h := (667 / 250 : ℝ)) (e₁ := (3 / 100000 : ℝ)) (e₂ := (31 / 20000 : ℝ)) (c := (1 / 200 : ℝ))
    (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num)
  have b3 := UpperDisagreement.capTerm_le_band (t := 8 * s) (lo := (349 / 25 : ℝ)) (hi := (1423 / 100 : ℝ)) (h := (3773 / 1000 : ℝ)) (e₁ := (1 / 100000 : ℝ)) (e₂ := (3 / 100000 : ℝ)) (c := (1 / 1000 : ℝ))
    (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num)
  have b4 := UpperDisagreement.capTerm_le_band (t := 16 * s) (lo := (698 / 25 : ℝ)) (hi := (1423 / 50 : ℝ)) (h := (1067 / 200 : ℝ)) (e₁ := (1 / 100000 : ℝ)) (e₂ := (1 / 100000 : ℝ)) (c := (1 / 1000 : ℝ))
    (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num)
  have b5 := UpperDisagreement.capTerm_le_band (t := 32 * s) (lo := (1396 / 25 : ℝ)) (hi := (1423 / 25 : ℝ)) (h := (1509 / 200 : ℝ)) (e₁ := (1 / 100000 : ℝ)) (e₂ := (1 / 100000 : ℝ)) (c := (1 / 1000 : ℝ))
    (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num)
  linarith

theorem quarter_piece_3_3 {s : ℝ} (ha : (1423 / 800 : ℝ) ≤ s) (hb : s ≤ (1449 / 800 : ℝ)) :
    (1073 / 1000 : ℝ) * Real.sqrt s +
      (UpperDisagreement.capTerm s + UpperDisagreement.capTerm (2 * s) + UpperDisagreement.capTerm (4 * s) +
        UpperDisagreement.capTerm (8 * s) + UpperDisagreement.capTerm (16 * s) + UpperDisagreement.capTerm (32 * s)) + 1 / 1000 ≤ (89 / 50 : ℝ) := by
  have e := scaled_sqrt_le (A := (1073 / 1000 : ℝ)) (s := s) (b := (1449 / 800 : ℝ)) (h := (673 / 500 : ℝ)) (by norm_num) hb (by norm_num) (by norm_num)
  have b0 := UpperDisagreement.capTerm_le_band (t := s) (lo := (1423 / 800 : ℝ)) (hi := (1449 / 800 : ℝ)) (h := (673 / 500 : ℝ)) (e₁ := (2937 / 100000 : ℝ)) (e₂ := (8447 / 50000 : ℝ)) (c := (267 / 1000 : ℝ))
    ha hb (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num)
  have b1 := UpperDisagreement.capTerm_le_band (t := 2 * s) (lo := (1423 / 400 : ℝ)) (hi := (1449 / 400 : ℝ)) (h := (238 / 125 : ℝ)) (e₁ := (7 / 5000 : ℝ)) (e₂ := (2937 / 100000 : ℝ)) (c := (59 / 1000 : ℝ))
    (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num)
  have b2 := UpperDisagreement.capTerm_le_band (t := 4 * s) (lo := (1423 / 200 : ℝ)) (hi := (1449 / 200 : ℝ)) (h := (673 / 250 : ℝ)) (e₁ := (3 / 100000 : ℝ)) (e₂ := (7 / 5000 : ℝ)) (c := (1 / 250 : ℝ))
    (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num)
  have b3 := UpperDisagreement.capTerm_le_band (t := 8 * s) (lo := (1423 / 100 : ℝ)) (hi := (1449 / 100 : ℝ)) (h := (3807 / 1000 : ℝ)) (e₁ := (1 / 100000 : ℝ)) (e₂ := (3 / 100000 : ℝ)) (c := (1 / 1000 : ℝ))
    (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num)
  have b4 := UpperDisagreement.capTerm_le_band (t := 16 * s) (lo := (1423 / 50 : ℝ)) (hi := (1449 / 50 : ℝ)) (h := (673 / 125 : ℝ)) (e₁ := (1 / 100000 : ℝ)) (e₂ := (1 / 100000 : ℝ)) (c := (1 / 1000 : ℝ))
    (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num)
  have b5 := UpperDisagreement.capTerm_le_band (t := 32 * s) (lo := (1423 / 25 : ℝ)) (hi := (1449 / 25 : ℝ)) (h := (3807 / 500 : ℝ)) (e₁ := (1 / 100000 : ℝ)) (e₂ := (1 / 100000 : ℝ)) (c := (1 / 1000 : ℝ))
    (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num)
  linarith

theorem quarter_piece_3_4 {s : ℝ} (ha : (1449 / 800 : ℝ) ≤ s) (hb : s ≤ (147 / 80 : ℝ)) :
    (1073 / 1000 : ℝ) * Real.sqrt s +
      (UpperDisagreement.capTerm s + UpperDisagreement.capTerm (2 * s) + UpperDisagreement.capTerm (4 * s) +
        UpperDisagreement.capTerm (8 * s) + UpperDisagreement.capTerm (16 * s) + UpperDisagreement.capTerm (32 * s)) + 1 / 1000 ≤ (89 / 50 : ℝ) := by
  have e := scaled_sqrt_le (A := (1073 / 1000 : ℝ)) (s := s) (b := (147 / 80 : ℝ)) (h := (339 / 250 : ℝ)) (by norm_num) hb (by norm_num) (by norm_num)
  have b0 := UpperDisagreement.capTerm_le_band (t := s) (lo := (1449 / 800 : ℝ)) (hi := (147 / 80 : ℝ)) (h := (339 / 250 : ℝ)) (e₁ := (69 / 2500 : ℝ)) (e₂ := (3271 / 20000 : ℝ)) (c := (13 / 50 : ℝ))
    ha hb (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num)
  have b1 := UpperDisagreement.capTerm_le_band (t := 2 * s) (lo := (1449 / 400 : ℝ)) (hi := (147 / 40 : ℝ)) (h := (959 / 500 : ℝ)) (e₁ := (127 / 100000 : ℝ)) (e₂ := (69 / 2500 : ℝ)) (c := (7 / 125 : ℝ))
    (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num)
  have b2 := UpperDisagreement.capTerm_le_band (t := 4 * s) (lo := (1449 / 200 : ℝ)) (hi := (147 / 20 : ℝ)) (h := (339 / 125 : ℝ)) (e₁ := (3 / 100000 : ℝ)) (e₂ := (127 / 100000 : ℝ)) (c := (1 / 250 : ℝ))
    (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num)
  have b3 := UpperDisagreement.capTerm_le_band (t := 8 * s) (lo := (1449 / 100 : ℝ)) (hi := (147 / 10 : ℝ)) (h := (767 / 200 : ℝ)) (e₁ := (1 / 100000 : ℝ)) (e₂ := (3 / 100000 : ℝ)) (c := (1 / 1000 : ℝ))
    (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num)
  have b4 := UpperDisagreement.capTerm_le_band (t := 16 * s) (lo := (1449 / 50 : ℝ)) (hi := (147 / 5 : ℝ)) (h := (5423 / 1000 : ℝ)) (e₁ := (1 / 100000 : ℝ)) (e₂ := (1 / 100000 : ℝ)) (c := (1 / 1000 : ℝ))
    (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num)
  have b5 := UpperDisagreement.capTerm_le_band (t := 32 * s) (lo := (1449 / 25 : ℝ)) (hi := (294 / 5 : ℝ)) (h := (7669 / 1000 : ℝ)) (e₁ := (1 / 100000 : ℝ)) (e₂ := (1 / 100000 : ℝ)) (c := (1 / 1000 : ℝ))
    (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num)
  linarith

theorem quarter_piece_3_5 {s : ℝ} (ha : (147 / 80 : ℝ) ≤ s) (hb : s ≤ (149 / 80 : ℝ)) :
    (1073 / 1000 : ℝ) * Real.sqrt s +
      (UpperDisagreement.capTerm s + UpperDisagreement.capTerm (2 * s) + UpperDisagreement.capTerm (4 * s) +
        UpperDisagreement.capTerm (8 * s) + UpperDisagreement.capTerm (16 * s) + UpperDisagreement.capTerm (32 * s)) + 1 / 1000 ≤ (89 / 50 : ℝ) := by
  have e := scaled_sqrt_le (A := (1073 / 1000 : ℝ)) (s := s) (b := (149 / 80 : ℝ)) (h := (273 / 200 : ℝ)) (by norm_num) hb (by norm_num) (by norm_num)
  have b0 := UpperDisagreement.capTerm_le_band (t := s) (lo := (147 / 80 : ℝ)) (hi := (149 / 80 : ℝ)) (h := (273 / 200 : ℝ)) (e₁ := (21 / 800 : ℝ)) (e₂ := (3983 / 25000 : ℝ)) (c := (127 / 500 : ℝ))
    ha hb (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num)
  have b1 := UpperDisagreement.capTerm_le_band (t := 2 * s) (lo := (147 / 40 : ℝ)) (hi := (149 / 40 : ℝ)) (h := (1931 / 1000 : ℝ)) (e₁ := (59 / 50000 : ℝ)) (e₂ := (21 / 800 : ℝ)) (c := (53 / 1000 : ℝ))
    (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num)
  have b2 := UpperDisagreement.capTerm_le_band (t := 4 * s) (lo := (147 / 20 : ℝ)) (hi := (149 / 20 : ℝ)) (h := (273 / 100 : ℝ)) (e₁ := (1 / 50000 : ℝ)) (e₂ := (59 / 50000 : ℝ)) (c := (1 / 250 : ℝ))
    (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num)
  have b3 := UpperDisagreement.capTerm_le_band (t := 8 * s) (lo := (147 / 10 : ℝ)) (hi := (149 / 10 : ℝ)) (h := (3861 / 1000 : ℝ)) (e₁ := (1 / 100000 : ℝ)) (e₂ := (1 / 50000 : ℝ)) (c := (1 / 1000 : ℝ))
    (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num)
  have b4 := UpperDisagreement.capTerm_le_band (t := 16 * s) (lo := (147 / 5 : ℝ)) (hi := (149 / 5 : ℝ)) (h := (5459 / 1000 : ℝ)) (e₁ := (1 / 100000 : ℝ)) (e₂ := (1 / 100000 : ℝ)) (c := (1 / 1000 : ℝ))
    (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num)
  have b5 := UpperDisagreement.capTerm_le_band (t := 32 * s) (lo := (294 / 5 : ℝ)) (hi := (298 / 5 : ℝ)) (h := (7721 / 1000 : ℝ)) (e₁ := (1 / 100000 : ℝ)) (e₂ := (1 / 100000 : ℝ)) (c := (1 / 1000 : ℝ))
    (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num)
  linarith

theorem quarter_piece_3_6 {s : ℝ} (ha : (149 / 80 : ℝ) ≤ s) (hb : s ≤ (301 / 160 : ℝ)) :
    (1073 / 1000 : ℝ) * Real.sqrt s +
      (UpperDisagreement.capTerm s + UpperDisagreement.capTerm (2 * s) + UpperDisagreement.capTerm (4 * s) +
        UpperDisagreement.capTerm (8 * s) + UpperDisagreement.capTerm (16 * s) + UpperDisagreement.capTerm (32 * s)) + 1 / 1000 ≤ (89 / 50 : ℝ) := by
  have e := scaled_sqrt_le (A := (1073 / 1000 : ℝ)) (s := s) (b := (301 / 160 : ℝ)) (h := (343 / 250 : ℝ)) (by norm_num) hb (by norm_num) (by norm_num)
  have b0 := UpperDisagreement.capTerm_le_band (t := s) (lo := (149 / 80 : ℝ)) (hi := (301 / 160 : ℝ)) (h := (343 / 250 : ℝ)) (e₁ := (2503 / 100000 : ℝ)) (e₂ := (777 / 5000 : ℝ)) (c := (31 / 125 : ℝ))
    ha hb (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num)
  have b1 := UpperDisagreement.capTerm_le_band (t := 2 * s) (lo := (149 / 40 : ℝ)) (hi := (301 / 80 : ℝ)) (h := (97 / 50 : ℝ)) (e₁ := (11 / 10000 : ℝ)) (e₂ := (2503 / 100000 : ℝ)) (c := (51 / 1000 : ℝ))
    (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num)
  have b2 := UpperDisagreement.capTerm_le_band (t := 4 * s) (lo := (149 / 20 : ℝ)) (hi := (301 / 40 : ℝ)) (h := (343 / 125 : ℝ)) (e₁ := (1 / 50000 : ℝ)) (e₂ := (11 / 10000 : ℝ)) (c := (1 / 250 : ℝ))
    (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num)
  have b3 := UpperDisagreement.capTerm_le_band (t := 8 * s) (lo := (149 / 10 : ℝ)) (hi := (301 / 20 : ℝ)) (h := (97 / 25 : ℝ)) (e₁ := (1 / 100000 : ℝ)) (e₂ := (1 / 50000 : ℝ)) (c := (1 / 1000 : ℝ))
    (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num)
  have b4 := UpperDisagreement.capTerm_le_band (t := 16 * s) (lo := (149 / 5 : ℝ)) (hi := (301 / 10 : ℝ)) (h := (5487 / 1000 : ℝ)) (e₁ := (1 / 100000 : ℝ)) (e₂ := (1 / 100000 : ℝ)) (c := (1 / 1000 : ℝ))
    (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num)
  have b5 := UpperDisagreement.capTerm_le_band (t := 32 * s) (lo := (298 / 5 : ℝ)) (hi := (301 / 5 : ℝ)) (h := (7759 / 1000 : ℝ)) (e₁ := (1 / 100000 : ℝ)) (e₂ := (1 / 100000 : ℝ)) (c := (1 / 1000 : ℝ))
    (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num)
  linarith

theorem quarter_piece_3_7 {s : ℝ} (ha : (301 / 160 : ℝ) ≤ s) (hb : s ≤ (1519 / 800 : ℝ)) :
    (1073 / 1000 : ℝ) * Real.sqrt s +
      (UpperDisagreement.capTerm s + UpperDisagreement.capTerm (2 * s) + UpperDisagreement.capTerm (4 * s) +
        UpperDisagreement.capTerm (8 * s) + UpperDisagreement.capTerm (16 * s) + UpperDisagreement.capTerm (32 * s)) + 1 / 1000 ≤ (89 / 50 : ℝ) := by
  have e := scaled_sqrt_le (A := (1073 / 1000 : ℝ)) (s := s) (b := (1519 / 800 : ℝ)) (h := (689 / 500 : ℝ)) (by norm_num) hb (by norm_num) (by norm_num)
  have b0 := UpperDisagreement.capTerm_le_band (t := s) (lo := (301 / 160 : ℝ)) (hi := (1519 / 800 : ℝ)) (h := (689 / 500 : ℝ)) (e₁ := (483 / 20000 : ℝ)) (e₂ := (3813 / 25000 : ℝ)) (c := (61 / 250 : ℝ))
    ha hb (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num)
  have b1 := UpperDisagreement.capTerm_le_band (t := 2 * s) (lo := (301 / 80 : ℝ)) (hi := (1519 / 400 : ℝ)) (h := (1949 / 1000 : ℝ)) (e₁ := (13 / 12500 : ℝ)) (e₂ := (483 / 20000 : ℝ)) (c := (1 / 20 : ℝ))
    (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num)
  have b2 := UpperDisagreement.capTerm_le_band (t := 4 * s) (lo := (301 / 40 : ℝ)) (hi := (1519 / 200 : ℝ)) (h := (689 / 250 : ℝ)) (e₁ := (1 / 50000 : ℝ)) (e₂ := (13 / 12500 : ℝ)) (c := (3 / 1000 : ℝ))
    (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num)
  have b3 := UpperDisagreement.capTerm_le_band (t := 8 * s) (lo := (301 / 20 : ℝ)) (hi := (1519 / 100 : ℝ)) (h := (1949 / 500 : ℝ)) (e₁ := (1 / 100000 : ℝ)) (e₂ := (1 / 50000 : ℝ)) (c := (1 / 1000 : ℝ))
    (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num)
  have b4 := UpperDisagreement.capTerm_le_band (t := 16 * s) (lo := (301 / 10 : ℝ)) (hi := (1519 / 50 : ℝ)) (h := (689 / 125 : ℝ)) (e₁ := (1 / 100000 : ℝ)) (e₂ := (1 / 100000 : ℝ)) (c := (1 / 1000 : ℝ))
    (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num)
  have b5 := UpperDisagreement.capTerm_le_band (t := 32 * s) (lo := (301 / 5 : ℝ)) (hi := (1519 / 25 : ℝ)) (h := (1559 / 200 : ℝ)) (e₁ := (1 / 100000 : ℝ)) (e₂ := (1 / 100000 : ℝ)) (c := (1 / 1000 : ℝ))
    (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num)
  linarith

theorem quarter_piece_3_8 {s : ℝ} (ha : (1519 / 800 : ℝ) ≤ s) (hb : s ≤ (19 / 10 : ℝ)) :
    (1073 / 1000 : ℝ) * Real.sqrt s +
      (UpperDisagreement.capTerm s + UpperDisagreement.capTerm (2 * s) + UpperDisagreement.capTerm (4 * s) +
        UpperDisagreement.capTerm (8 * s) + UpperDisagreement.capTerm (16 * s) + UpperDisagreement.capTerm (32 * s)) + 1 / 1000 ≤ (89 / 50 : ℝ) := by
  have e := scaled_sqrt_le (A := (1073 / 1000 : ℝ)) (s := s) (b := (19 / 10 : ℝ)) (h := (1379 / 1000 : ℝ)) (by norm_num) hb (by norm_num) (by norm_num)
  have b0 := UpperDisagreement.capTerm_le_band (t := s) (lo := (1519 / 800 : ℝ)) (hi := (19 / 10 : ℝ)) (h := (1379 / 1000 : ℝ)) (e₁ := (2337 / 100000 : ℝ)) (e₂ := (3747 / 25000 : ℝ)) (c := (239 / 1000 : ℝ))
    ha hb (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num)
  have b1 := UpperDisagreement.capTerm_le_band (t := 2 * s) (lo := (1519 / 400 : ℝ)) (hi := (19 / 5 : ℝ)) (h := (39 / 20 : ℝ)) (e₁ := (99 / 100000 : ℝ)) (e₂ := (2337 / 100000 : ℝ)) (c := (6 / 125 : ℝ))
    (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num)
  have b2 := UpperDisagreement.capTerm_le_band (t := 4 * s) (lo := (1519 / 200 : ℝ)) (hi := (38 / 5 : ℝ)) (h := (2757 / 1000 : ℝ)) (e₁ := (1 / 50000 : ℝ)) (e₂ := (99 / 100000 : ℝ)) (c := (3 / 1000 : ℝ))
    (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num)
  have b3 := UpperDisagreement.capTerm_le_band (t := 8 * s) (lo := (1519 / 100 : ℝ)) (hi := (76 / 5 : ℝ)) (h := (3899 / 1000 : ℝ)) (e₁ := (1 / 100000 : ℝ)) (e₂ := (1 / 50000 : ℝ)) (c := (1 / 1000 : ℝ))
    (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num)
  have b4 := UpperDisagreement.capTerm_le_band (t := 16 * s) (lo := (1519 / 50 : ℝ)) (hi := (152 / 5 : ℝ)) (h := (2757 / 500 : ℝ)) (e₁ := (1 / 100000 : ℝ)) (e₂ := (1 / 100000 : ℝ)) (c := (1 / 1000 : ℝ))
    (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num)
  have b5 := UpperDisagreement.capTerm_le_band (t := 32 * s) (lo := (1519 / 25 : ℝ)) (hi := (304 / 5 : ℝ)) (h := (3899 / 500 : ℝ)) (e₁ := (1 / 100000 : ℝ)) (e₂ := (1 / 100000 : ℝ)) (c := (1 / 1000 : ℝ))
    (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num)
  linarith

/-- The offset sum of band 3. -/
theorem quarter_offset_3 (s : ℝ) (h1 : (133 / 80 : ℝ) ≤ s) (h2 : s ≤ (19 / 10 : ℝ)) (I : ℕ) :
    (1073 / 1000 : ℝ) * Real.sqrt s + ∑ i ∈ range I, UpperDisagreement.capTerm (2 ^ i * s) ≤ (89 / 50 : ℝ) := by
  have hr := UpperDisagreement.cap_offset_reduce s (by linarith) I
  have hred : (1073 / 1000 : ℝ) * Real.sqrt s + ∑ i ∈ range I, UpperDisagreement.capTerm (2 ^ i * s) ≤
      (1073 / 1000 : ℝ) * Real.sqrt s +
      (UpperDisagreement.capTerm s + UpperDisagreement.capTerm (2 * s) + UpperDisagreement.capTerm (4 * s) +
        UpperDisagreement.capTerm (8 * s) + UpperDisagreement.capTerm (16 * s) + UpperDisagreement.capTerm (32 * s)) + 1 / 1000 := by linarith
  refine hred.trans ?_
  rcases le_or_gt s (341 / 200 : ℝ) with hk | hp
  · exact quarter_piece_3_0 h1 hk
  rcases le_or_gt s (349 / 200 : ℝ) with hk | hp
  · exact quarter_piece_3_1 hp.le hk
  rcases le_or_gt s (1423 / 800 : ℝ) with hk | hp
  · exact quarter_piece_3_2 hp.le hk
  rcases le_or_gt s (1449 / 800 : ℝ) with hk | hp
  · exact quarter_piece_3_3 hp.le hk
  rcases le_or_gt s (147 / 80 : ℝ) with hk | hp
  · exact quarter_piece_3_4 hp.le hk
  rcases le_or_gt s (149 / 80 : ℝ) with hk | hp
  · exact quarter_piece_3_5 hp.le hk
  rcases le_or_gt s (301 / 160 : ℝ) with hk | hp
  · exact quarter_piece_3_6 hp.le hk
  rcases le_or_gt s (1519 / 800 : ℝ) with hk | hp
  · exact quarter_piece_3_7 hp.le hk
  exact quarter_piece_3_8 hp.le h2

end QuarterOffset

end ThresholdHC.UpperQuarter
