import SharpInterpolation

/-! Enclosing all integer exits on a real parameter bin with finitely many
barriers and a single upper bound for the tail. -/
noncomputable section
namespace ThresholdHC.SharpRMS

def exitFactor (s t x : ℝ) := (1-t*x)*(1+t*s)

private theorem factor_order (s t b x y : ℝ) (hs : 0 ≤ s) (ht : 0 ≤ t)
    (tb : t ≤ b) (sx : s ≤ x) (xy : x ≤ y) :
    exitFactor s b y ≤ exitFactor s t x := by
  have hb : 0 ≤ b := ht.trans tb
  have hx : 0 ≤ x := hs.trans sx
  unfold exitFactor
  have A : (1-b*y)*(1+b*s) ≤ (1-b*x)*(1+b*s) := by
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    linarith only [mul_le_mul_of_nonneg_left xy hb]
  apply A.trans
  nlinarith only [mul_nonneg (sub_nonneg.mpr tb) (sub_nonneg.mpr sx),
    mul_nonneg (mul_nonneg (mul_nonneg (sub_nonneg.mpr tb) (add_nonneg ht hb)) hs) hx]

private theorem length_order (s t b : ℝ) (hs : 0 < s) (hs' : s < 1)
    (tb : t ≤ b) (k : ℕ) (hk : 0 < k) : exitLength s b k ≤ exitLength s t k := by
  have post := barrier_posterior_bounds s hs hs' k
  have hx := hs.trans_le (post.2.2.2 hk)
  have h : 1/s ≤ (k:ℝ)/barrierPosterior s k :=
    (div_le_div_iff₀ hs hx).mpr (by linarith only [post.2.2.1])
  unfold exitLength
  linarith only [mul_le_mul_of_nonneg_right tb (sub_nonneg.mpr h)]

/-- The left endpoint bounds the taper. At the right endpoint retain the
first m-1 barriers and use x=1 and the mth exit length for the entire tail. -/
theorem rectangle_exit_price (s l t b H : ℝ) (m : ℕ) (hm : 0 < m)
    (hs : 0 < s) (hs' : s < 1) (hl : 0 ≤ l) (lt' : l ≤ t) (tb : t ≤ b)
    (hb : b ≤ 1) (ht : t < 1) (hH : 0 < H)
    (bounds : ∀ k : ℕ, 0 < k → k ≤ m →
      let y := if k=m then 1 else barrierPosterior s k
      (1-l^2)^2*(1+y/s) ≤ H*(exitFactor s b y*exitLength s b k)) :
    ∃ P, 0 < P ∧ P ≤ 1 ∧ admissibleExitPrice s t P ∧ (1-t^2)^2 ≤ H*P := by
  let P := (1-t^2)^2/H
  have ht0 := hl.trans lt'
  have hb0 := ht0.trans tb
  have v : 0 < 1-t^2 := by nlinarith [mul_pos (sub_pos.mpr ht) (show 0 < 1+t by linarith)]
  have w : (1-t^2)^2 ≤ (1-l^2)^2 := by
    have a : 1-t^2 ≤ 1-l^2 := by nlinarith [mul_nonneg (sub_nonneg.mpr lt') (add_nonneg hl ht0)]
    nlinarith only [mul_nonneg (sub_nonneg.mpr a) (show 0 ≤ 1-l^2+(1-t^2) by linarith)]
  have adm : admissibleExitPrice s t P := by
    intro k hk
    let j := min k m
    have hj : 0 < j := lt_min hk hm
    let x := barrierPosterior s k
    let y : ℝ := if j=m then 1 else barrierPosterior s j
    have xprop := barrier_posterior_bounds s hs hs' k
    have xy : x ≤ y := by
      unfold y
      split_ifs with he
      · exact xprop.2.1.le
      · have hjk : j=k := (min_cases k m).elim (fun h => h.1) (fun h => (he h.1).elim)
        rw [hjk]
    have y1 : y ≤ 1 := by
      unfold y
      split_ifs
      · rfl
      · exact (barrier_posterior_bounds s hs hs' j).2.1.le
    have den := factor_order s t b x y hs.le ht0 tb (xprop.2.2.2 hk) xy
    have fpos : 0 ≤ exitFactor s b y := by
      apply mul_nonneg _ (by positivity)
      linarith only [(mul_le_mul_of_nonneg_left y1 hb0).trans (by simpa using hb)]
    have lmono := (length_order s t b hs hs' tb j hj).trans
      (exit_length_mono s t hs hs' ht0 ht.le j k hj (min_le_left ..))
    have lenpos : 0 ≤ exitLength s t k := by
      have lo := exit_length_mono s t hs hs' ht0 ht.le 1 k (by decide) hk
      have one : exitLength s t 1=2 := by simp [exitLength,barrierPosterior]; ring
      linarith
    have prod := mul_le_mul_of_nonneg den lmono fpos lenpos
    have numer : (1-t^2)^2*(1+x/s) ≤ (1-l^2)^2*(1+y/s) := by
      apply mul_le_mul_of_nonneg w _ (sq_nonneg _) (by have := xprop.1.trans xy; positivity)
      linarith only [div_le_div_of_nonneg_right xy hs.le]
    have cert := (numer.trans (bounds j hj (min_le_right ..))).trans (mul_le_mul_of_nonneg_left prod hH.le)
    change ((1-t^2)^2/H)*(1+x/s) ≤ exitFactor s t x*exitLength s t k
    rw [div_mul_eq_mul_div,div_le_iff₀ hH]
    linarith only [cert]
  have a := adm 1 (by decide)
  simp [barrierPosterior,hs.ne'] at a
  have up : P ≤ 1 := by nlinarith only [a,mul_nonneg (sq_nonneg t) (sq_nonneg s)]
  refine ⟨P, div_pos (sq_pos_of_pos v) hH,up,adm,?_⟩
  dsimp [P]
  rw [mul_div_cancel₀ _ hH.ne']

/-- Independent sign-revelation bound for each full bin, including the last
bin where the formal right endpoint is one. -/
theorem rectangle_sign_price (s l t H : ℝ) (hs : 0 < s) (hs' : s < 1)
    (hl : 0 ≤ l) (hlt : l ≤ t) (ht : t < 1) (hH : (1-l^2)/s^2 ≤ H) :
    ∃ P, 0 < P ∧ P ≤ 1 ∧ admissibleExitPrice s t P ∧ (1-t^2)^2 ≤ H*P := by
  have ht0 := hl.trans hlt
  have v : 0 < 1-t^2 := by nlinarith [mul_pos (sub_pos.mpr ht) (show 0 < 1+t by linarith)]
  have s2 : s^2 ≤ 1 := by nlinarith [mul_nonneg (sub_nonneg.mpr hs'.le) (show 0 ≤ 1+s by linarith)]
  have st : s*t ≤ 1 := (mul_le_mul_of_nonneg_right hs'.le ht0).trans (by simpa using ht.le)
  let P := s^2*(1-t^2)
  have pos : 0<P := mul_pos (sq_pos_of_pos hs) v
  refine ⟨P,pos,?_,?_,?_⟩
  · change s^2*(1-t^2) ≤ 1
    nlinarith [mul_nonneg (sq_nonneg s) (sq_nonneg t)]
  · apply price_of_two_caps s t P hs hs' ht0 ht pos.le
    · dsimp [P]
      linarith
    · dsimp [P]
      nlinarith only [mul_nonneg pos.le (sub_nonneg.mpr st)]
  · have raw := (div_le_iff₀ (sq_pos_of_pos hs)).mp hH
    have a : 1-t^2 ≤ H*s^2 := by nlinarith only [raw,mul_nonneg (sub_nonneg.mpr hlt) (add_nonneg hl ht0)]
    dsimp [P]
    nlinarith only [mul_le_mul_of_nonneg_right a v.le]

end ThresholdHC.SharpRMS
