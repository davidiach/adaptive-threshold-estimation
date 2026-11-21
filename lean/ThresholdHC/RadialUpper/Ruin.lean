import ThresholdHC.RadialUpper.Walk

/-! Gambler's-ruin bounds for the capped walk started at state `1`.

For a coin of mean `1/2+d` (upward drift) the walk hits the upper boundary with
probability at least `1-r` minus `E[steps]/N`, which bounds the probability of
being cut off by the cap, and reads at most `2K` bits in expectation. For a coin of
mean `1/2-d` it hits the upper boundary with probability at most `r^(K-1)` and
reads at most `1/(2d)` bits in expectation. Here `r = (1/2-d)/(1/2+d)`. These are
finite-cap analogues of `pop:ruin-bounds` and of the source's stopped-walk work
bounds; the down-drift hit bound is `r^(K-1)`. -/

noncomputable section
namespace ThresholdHC.RadialUpper

/-- The ratio `r = (1/2-d)/(1/2+d)` of the two step probabilities. -/
def walkRatio (d : ℝ) : ℝ := (1/2-d)/(1/2+d)

theorem walkRatio_nonneg {d : ℝ} (hd0 : 0 ≤ d) (hd1 : d ≤ 1/2) : 0 ≤ walkRatio d :=
  div_nonneg (by linarith) (by linarith)

theorem walkRatio_le_one {d : ℝ} (hd0 : 0 ≤ d) : walkRatio d ≤ 1 :=
  (div_le_one (by linarith)).mpr (by linarith)

theorem one_sub_walkRatio {d : ℝ} (hd0 : 0 ≤ d) : 1 - walkRatio d = 2*d/(1/2+d) := by
  unfold walkRatio
  field_simp
  ring

theorem walkRatio_identity {d : ℝ} (hd0 : 0 ≤ d) :
    (1/2+d) * walkRatio d ^ 2 + (1/2-d) = walkRatio d := by
  unfold walkRatio
  field_simp
  ring

theorem one_sub_walkRatio_le {d : ℝ} (hd0 : 0 ≤ d) : 1 - walkRatio d ≤ 4*d := by
  rw [one_sub_walkRatio hd0, div_le_iff₀ (by linarith)]
  nlinarith

/-- Upward drift: the hit probability is at least `1-r` minus `E[steps]/N`, which
bounds the cut-off probability. -/
theorem up_hit_lower {d : ℝ} (hd0 : 0 ≤ d) (hd1 : d ≤ 1/2) (K N : ℕ) (hN : 0 < N) :
    1 - walkRatio d ≤ walkSum (1/2+d) K N 1 (fun r => walkHit K r.2) +
      walkSum (1/2+d) K N 1 (fun r => (r.1 : ℝ)) / N := by
  have hp0 : 0 ≤ 1/2+d := by linarith
  have hp1 : 1/2+d ≤ 1 := by linarith
  have hr0 := walkRatio_nonneg hd0 hd1
  have hr1 := walkRatio_le_one hd0
  have hh := walkSum_harmonic (1/2+d) K (fun k => 1 - walkRatio d ^ k) (by
    intro k hk _
    obtain ⟨j, rfl⟩ : ∃ j, k = j+1 := ⟨k-1, by omega⟩
    simp only [Nat.add_sub_cancel]
    linear_combination (-(walkRatio d ^ j)) * walkRatio_identity hd0) N 1
  simp only [pow_one] at hh
  rw [← hh, div_eq_inv_mul (walkSum _ _ _ _ _), ← walkSum_const_mul, ← walkSum_add]
  apply walkSum_mono hp0 hp1
  intro w
  set r := walkRun K N 1 w
  have hNr : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  by_cases h0 : r.2 = 0
  · simp only [h0, pow_zero, sub_self]
    exact add_nonneg (walkHit_nonneg _ _) (mul_nonneg (inv_nonneg.mpr hNr.le) (Nat.cast_nonneg _))
  by_cases hK : K ≤ r.2
  · have : walkHit K r.2 = 1 := by simp [walkHit, hK]
    rw [this]
    have := pow_nonneg hr0 r.2
    have := mul_nonneg (inv_nonneg.mpr hNr.le) (Nat.cast_nonneg (α := ℝ) r.1)
    linarith
  · have hs : r.1 = N := walkRun_alive K N 1 w ⟨Nat.pos_of_ne_zero h0, lt_of_not_ge hK⟩
    rw [hs, inv_mul_cancel₀ hNr.ne']
    have := pow_nonneg hr0 r.2
    have := walkHit_nonneg K r.2
    linarith

/-- The partial geometric sum `1 + r + ... + r^(k-1)`. -/
def walkGeom (r : ℝ) (k : ℕ) : ℝ := ∑ i ∈ Finset.range k, r^i

theorem walkGeom_succ (r : ℝ) (k : ℕ) : walkGeom r (k+1) = walkGeom r k + r^k :=
  Finset.sum_range_succ _ _

theorem walkGeom_mul (r : ℝ) (k : ℕ) : (1-r) * walkGeom r k = 1 - r^k := by
  induction k with
  | zero => simp [walkGeom]
  | succ k ih => rw [walkGeom_succ, mul_add, ih]; ring

theorem walkGeom_one_le {r : ℝ} (hr0 : 0 ≤ r) {k : ℕ} (hk : 1 ≤ k) : 1 ≤ walkGeom r k := by
  have h := Finset.single_le_sum (f := fun i => r^i) (fun i _ => pow_nonneg hr0 i)
    (Finset.mem_range.mpr (show 0 < k by omega))
  simpa [walkGeom] using h

theorem walkGeom_lower {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (k : ℕ) :
    (k : ℝ) * r^k ≤ walkGeom r k := by
  have h : ∀ i ∈ Finset.range k, r^k ≤ r^i := fun i hi =>
    pow_le_pow_of_le_one hr0 hr1 (Finset.mem_range.mp hi).le
  have := Finset.card_nsmul_le_sum (Finset.range k) (fun i => r^i) (r^k) h
  simpa [walkGeom, nsmul_eq_mul] using this

/-- Averages of a decreasing sequence decrease: `k G(K) <= K G(k)` for `k <= K`. -/
theorem walkGeom_average {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1) {k K : ℕ} (hkK : k ≤ K) :
    (k : ℝ) * walkGeom r K ≤ K * walkGeom r k := by
  induction K, hkK using Nat.le_induction with
  | base => exact le_rfl
  | succ K hk ih =>
    rw [walkGeom_succ]
    have h1 := walkGeom_lower hr0 hr1 k
    have h2 : r^K ≤ r^k := pow_le_pow_of_le_one hr0 hr1 hk
    have h3 : (k : ℝ) * r^K ≤ (k : ℝ) * r^k := mul_le_mul_of_nonneg_left h2 (Nat.cast_nonneg k)
    push_cast
    nlinarith

/-- Upward drift: the expected number of bits read is at most `2K`. -/
theorem up_cost_le {d : ℝ} (hd0 : 0 < d) (hd1 : d ≤ 1/2) (K N : ℕ) (hK : 1 ≤ K) :
    walkSum (1/2+d) K N 1 (fun r => (r.1 : ℝ)) ≤ 2*K := by
  have hp0 : 0 ≤ 1/2+d := by linarith
  have hp1 : 1/2+d ≤ 1 := by linarith
  set r := walkRatio d with hr
  have hr0 : 0 ≤ r := walkRatio_nonneg hd0.le hd1
  have hr1 : r ≤ 1 := walkRatio_le_one hd0.le
  have hG := walkGeom_one_le hr0 hK
  have hGpos : 0 < walkGeom r K := by linarith
  set c := (K : ℝ) / walkGeom r K with hc
  have hharm (j : ℕ) : (1/2+d) * walkGeom r (j+2) + (1-(1/2+d)) * walkGeom r j =
      walkGeom r (j+1) := by
    rw [walkGeom_succ r (j+1), walkGeom_succ r j]
    have hpr : (1/2+d) * r = 1/2-d := by
      rw [hr, walkRatio]
      field_simp
    have : (1/2+d) * r^(j+1) = (1/2-d) * r^j := by rw [pow_succ, ← mul_assoc, mul_comm _ (r^j),
      mul_assoc, hpr, mul_comm]
    linarith
  let W : ℕ → ℝ := fun k => (c * walkGeom r k - k) / (2*d)
  have hW0 (k : ℕ) (hk : k ≤ K) : 0 ≤ W k := by
    apply div_nonneg _ (by linarith)
    have ha := walkGeom_average hr0 hr1 hk
    rw [hc, div_mul_eq_mul_div, sub_nonneg, le_div_iff₀ hGpos]
    linarith
  have hW (k : ℕ) (hk : 0 < k) (_ : k < K) : 1 + (1/2+d) * W (k+1) + (1-(1/2+d)) * W (k-1) ≤ W k := by
    obtain ⟨j, rfl⟩ : ∃ j, k = j+1 := ⟨k-1, by omega⟩
    simp only [W, Nat.add_sub_cancel]
    have hh := hharm j
    rw [show j+1+1 = j+2 by ring]
    apply le_of_eq
    simp only [div_eq_mul_inv]
    push_cast
    have hinv : 2*d*(2*d)⁻¹ = 1 := mul_inv_cancel₀ (by positivity)
    linear_combination ((2*d)⁻¹*c) * hh - hinv
  have hb := walkSum_steps_le hp0 hp1 K W hW0 hW N 1 hK
  refine hb.trans ?_
  simp only [W]
  have h1 : walkGeom r 1 = 1 := by simp [walkGeom]
  rw [h1, mul_one, Nat.cast_one, div_le_iff₀ (by linarith), hc, div_sub_one hGpos.ne',
    div_le_iff₀ hGpos]
  have hm := walkGeom_mul r K
  have hm' : (K:ℝ) * ((1-r) * walkGeom r K) = K * (1 - r^K) := by rw [hm]
  have hl := walkGeom_lower hr0 hr1 K
  have hs := one_sub_walkRatio_le hd0.le
  rw [← hr] at hs
  have hK0 : (0 : ℝ) ≤ K := Nat.cast_nonneg K
  nlinarith [mul_le_mul_of_nonneg_left hs (mul_nonneg hK0 hGpos.le)]

/-- Downward drift: the hit probability is at most `r^(K-1)`. -/
theorem down_hit_upper {d : ℝ} (hd0 : 0 ≤ d) (hd1 : d ≤ 1/2) (K N : ℕ) :
    walkSum (1/2-d) K N 1 (fun r => walkHit K r.2) ≤ walkRatio d ^ (K-1) := by
  have hp0 : 0 ≤ 1/2-d := by linarith
  have hp1 : 1/2-d ≤ 1 := by linarith
  have hr0 := walkRatio_nonneg hd0 hd1
  have hh := walkSum_harmonic (1/2-d) K (fun k => walkRatio d ^ (K-k)) (by
    intro k hk hkK
    obtain ⟨m, hm⟩ : ∃ m, K - k = m+1 := ⟨K-k-1, by omega⟩
    have e1 : K - (k+1) = m := by omega
    have e2 : K - (k-1) = m+2 := by omega
    simp only [e1, e2, hm]
    linear_combination (walkRatio d ^ m) * walkRatio_identity hd0) N 1
  rw [← hh]
  apply walkSum_mono hp0 hp1
  intro w
  unfold walkHit
  split
  · rename_i h
    simp [Nat.sub_eq_zero_of_le h]
  · exact pow_nonneg hr0 _

/-- Downward drift: the expected number of bits read is at most `1/(2d)`. -/
theorem down_cost_le {d : ℝ} (hd0 : 0 < d) (hd1 : d ≤ 1/2) (K N : ℕ) :
    walkSum (1/2-d) K N 1 (fun r => (r.1 : ℝ)) ≤ 1/(2*d) := by
  have hp0 : 0 ≤ 1/2-d := by linarith
  have hp1 : 1/2-d ≤ 1 := by linarith
  by_cases hK : 1 ≤ K
  · have hb := walkSum_steps_le hp0 hp1 K (fun k => k/(2*d))
      (fun k _ => div_nonneg (Nat.cast_nonneg k) (by linarith)) (by
        intro k hk _
        apply le_of_eq
        rw [Nat.cast_add_one, Nat.cast_sub hk]
        field_simp
        ring) N 1 hK
    simpa using hb
  · have hK0 : K = 0 := by omega
    subst hK0
    cases N with
    | zero => rw [walkSum_zero]; simp only [CharP.cast_eq_zero]; positivity
    | succ n => rw [walkSum_stop _ _ _ _ _ (by omega)]; simp only [CharP.cast_eq_zero]; positivity

end ThresholdHC.RadialUpper
