import ThresholdHC.QuantileFactorUpper.Checker
import ThresholdHC.OptimalQuantile.Root

/-! Soundness of the natural-number exponential enclosure.

For a rational `x = num/den ≥ 0`, the Taylor sum of `exp` at `x/2^s` with
terms rounded down bounds `exp (x/2^s)` from below (`Real.sum_le_exp_of_nonneg`),
so its rounded-up reciprocal bounds `exp (-x/2^s)` from above, and `s`
upward-rounded squarings bound `exp (-x)`. At the grid point `u = a/gridDen` the
value `crit a / scale` bounds `finitePartition 5 k u + 2^-62` for
`k = 1462554551280/10^12`. -/
noncomputable section
open Real
namespace ThresholdHC.QuantileFactorUpper
open ThresholdHC.OptimalQuantile

theorem scale_pos : 0 < scale := by
  unfold scale
  positivity

theorem le_ceilDiv_mul (a b : ℕ) (hb : 0 < b) : a ≤ ceilDiv a b*b := by
  unfold ceilDiv
  have h1 := Nat.div_add_mod (a+b-1) b
  have h2 := Nat.mod_lt (a+b-1) hb
  rw [mul_comm]
  generalize (a+b-1)/b = q at *
  generalize b*q = x at *
  omega

theorem div_le_ceilDiv (a b : ℕ) (hb : 0 < b) : (a : ℝ)/b ≤ ceilDiv a b := by
  rw [div_le_iff₀ (by exact_mod_cast hb)]
  exact_mod_cast le_ceilDiv_mul a b hb

theorem taylorLow_le (num den : ℕ) (hd : 0 < den) (n : ℕ) :
    (taylorLow num den n : ℝ) ≤
      scale*∑ i ∈ Finset.range n, ((num : ℝ)/den)^i/(i.factorial : ℝ) := by
  induction n with
  | zero => simp [taylorLow]
  | succ n ih =>
    rw [Finset.sum_range_succ, mul_add]
    rw [show taylorLow num den (n+1) =
      taylorLow num den n+scale*num^n/(den^n*n.factorial) from rfl, Nat.cast_add]
    have h := Nat.cast_div_le (α := ℝ) (m := scale*num^n) (n := den^n*n.factorial)
    have hd' : (0 : ℝ) < den := by exact_mod_cast hd
    have hf : (0 : ℝ) < n.factorial := by exact_mod_cast n.factorial_pos
    have he : ((scale*num^n : ℕ) : ℝ)/((den^n*n.factorial : ℕ) : ℝ) =
        scale*(((num : ℝ)/den)^n/(n.factorial : ℝ)) := by
      push_cast
      rw [div_pow]
      field_simp
    linarith

theorem scale_le_taylorLow (num den n : ℕ) : scale ≤ taylorLow num den (n+1) := by
  induction n with
  | zero => simp [taylorLow]
  | succ n ih =>
    show scale ≤ taylorLow num den (n+1)+scale*num^(n+1)/(den^(n+1)*(n+1).factorial)
    exact ih.trans (Nat.le_add_right _ _)

theorem expBase_sound (num den : ℕ) (hd : 0 < den) :
    exp (-((num : ℝ)/den)) ≤ (expBase num den : ℝ)/scale := by
  have hy : 0 ≤ (num : ℝ)/den := by positivity
  have hT : scale ≤ taylorLow num den terms := scale_le_taylorLow num den 21
  have hs : (0 : ℝ) < scale := by exact_mod_cast scale_pos
  have hTn : 0 < taylorLow num den terms := lt_of_lt_of_le scale_pos hT
  have hTpos : (0 : ℝ) < taylorLow num den terms := by exact_mod_cast hTn
  have h1 : (taylorLow num den terms : ℝ) ≤ scale*exp ((num : ℝ)/den) :=
    (taylorLow_le num den hd terms).trans
      (mul_le_mul_of_nonneg_left (Real.sum_le_exp_of_nonneg hy terms) hs.le)
  have h2 : exp (-((num : ℝ)/den)) ≤ scale/taylorLow num den terms := by
    rw [exp_neg, inv_eq_one_div, div_le_div_iff₀ (exp_pos _) hTpos]
    linarith
  have h3 := div_le_ceilDiv (scale*scale) (taylorLow num den terms) hTn
  calc
    _ ≤ (scale : ℝ)/taylorLow num den terms := h2
    _ = ((scale*scale : ℕ) : ℝ)/taylorLow num den terms/scale := by
      push_cast
      field_simp
    _ ≤ _ := div_le_div_of_nonneg_right h3 hs.le

theorem squareIter_sound {e : ℝ} {v : ℕ} (he : 0 ≤ e) (hv : e ≤ v/scale) (t : ℕ) :
    e^(2^t) ≤ (squareIter t v : ℝ)/scale := by
  have hs : (0 : ℝ) < scale := by exact_mod_cast scale_pos
  induction t with
  | zero => simpa [squareIter] using hv
  | succ t ih =>
    have hpos : 0 ≤ e^(2^t) := pow_nonneg he _
    have hsq : e^(2^(t+1)) = (e^(2^t))^2 := by rw [pow_succ, pow_mul]
    rw [hsq]
    have h1 : (e^(2^t))^2 ≤ ((squareIter t v : ℝ)/scale)^2 := pow_le_pow_left₀ hpos ih 2
    have h2 := div_le_ceilDiv (squareIter t v*squareIter t v) scale scale_pos
    calc
      _ ≤ ((squareIter t v : ℝ)/scale)^2 := h1
      _ = ((squareIter t v*squareIter t v : ℕ) : ℝ)/scale/scale := by
        push_cast
        field_simp
      _ ≤ _ := div_le_div_of_nonneg_right h2 hs.le

theorem expNegUp_sound (num den s : ℕ) (hd : 0 < den) :
    exp (-((num : ℝ)/den)) ≤ (expNegUp num den s : ℝ)/scale := by
  have hd' : 0 < den*2^s := by positivity
  have hb := expBase_sound num (den*2^s) hd'
  have h := squareIter_sound (exp_pos _).le hb s
  have hdr : (0 : ℝ) < den := by exact_mod_cast hd
  have heq : exp (-((num : ℝ)/den)) = (exp (-((num : ℝ)/((den*2^s : ℕ) : ℝ))))^(2^s) := by
    rw [← exp_nat_mul]
    congr 1
    push_cast
    field_simp
  rw [heq]
  exact h

/-- The factor `1462554551280/10^12` as a ratio of the checker's naturals. -/
theorem factor_eq : (1462554551280/1000000000000 : ℝ) = (factorNum : ℝ)/factorDen := by
  unfold factorNum factorDen
  norm_num

theorem gridDen_pos : 0 < gridDen := by
  unfold gridDen
  positivity

theorem factor_facts :
    (factorDen : ℝ) ≤ factorNum ∧ 2*(factorDen : ℝ)^2 ≤ factorNum^2 ∧
      (factorDen : ℝ)^2+4*factorNum*factorDen ≤ 4*factorNum^2 := by
  unfold factorNum factorDen
  norm_num

theorem price_sub (a : ℕ) :
    4*factorNum*factorDen*a*gridDen ≤ 2*factorNum^2*(a^2+gridDen^2) := by
  obtain ⟨h1,_,_⟩ := factor_facts
  have hM : (0 : ℝ) ≤ factorDen := Nat.cast_nonneg _
  have hK : (0 : ℝ) ≤ factorNum := Nat.cast_nonneg _
  have h : (4*factorNum*factorDen*a*gridDen : ℝ) ≤ 2*factorNum^2*(a^2+gridDen^2) := by
    nlinarith only [mul_nonneg (mul_nonneg hK (sub_nonneg.mpr h1))
        (add_nonneg (sq_nonneg (a : ℝ)) (sq_nonneg (gridDen : ℝ))),
      mul_nonneg (mul_nonneg hK hM) (sq_nonneg ((a : ℝ)-gridDen))]
  exact_mod_cast h

theorem first_sub (a : ℕ) :
    2*factorNum*factorDen*a*gridDen+factorDen^2*a^2 ≤ factorNum^2*(a^2+gridDen^2) := by
  obtain ⟨_,h2,_⟩ := factor_facts
  have h : (2*factorNum*factorDen*a*gridDen+factorDen^2*a^2 : ℝ) ≤
      factorNum^2*(a^2+gridDen^2) := by
    nlinarith only [mul_nonneg (sub_nonneg.mpr h2) (sq_nonneg (a : ℝ)),
      sq_nonneg ((factorNum : ℝ)*gridDen-factorDen*a)]
  exact_mod_cast h

theorem priceDen_le (a : ℕ) : priceDen a ≤ priceNum a := by
  obtain ⟨_,_,h3⟩ := factor_facts
  unfold priceDen priceNum
  have hs := price_sub a
  apply Nat.le_sub_of_add_le
  have hA : (0 : ℝ) ≤ a := Nat.cast_nonneg _
  have hN : (0 : ℝ) ≤ gridDen := Nat.cast_nonneg _
  have h : (factorDen^2*a*gridDen+4*factorNum*factorDen*a*gridDen : ℝ) ≤
      2*factorNum^2*(a^2+gridDen^2) := by
    nlinarith only [mul_nonneg (sq_nonneg (factorNum : ℝ)) (sq_nonneg ((a : ℝ)-gridDen)),
      mul_nonneg (sub_nonneg.mpr h3) (mul_nonneg hA hN)]
  exact_mod_cast h

theorem crit_sound {a : ℕ} (ha : 0 < a) :
    finitePartition 5 (1462554551280/1000000000000) ((a : ℝ)/gridDen)+1/2^62 ≤
      (crit a : ℝ)/scale := by
  have hA : (0 : ℝ) < a := by exact_mod_cast ha
  have hN : (0 : ℝ) < gridDen := by exact_mod_cast gridDen_pos
  have hM : (0 : ℝ) < factorDen := by unfold factorDen; norm_num
  have hs : (0 : ℝ) < scale := by exact_mod_cast scale_pos
  have hPD : 0 < priceDen a := by
    unfold priceDen
    have : 0 < factorDen := by unfold factorDen; norm_num
    have := gridDen_pos
    positivity
  have hFD : 0 < firstDen a := by
    unfold firstDen
    have : 0 < factorDen := by unfold factorDen; norm_num
    positivity
  have hprice : dualPrice ((factorNum : ℝ)/factorDen) ((a : ℝ)/gridDen) =
      (priceNum a : ℝ)/priceDen a := by
    unfold dualPrice priceNum priceDen
    rw [Nat.cast_sub (price_sub a)]
    push_cast
    field_simp
  have hfirst : 1-dualPrice ((factorNum : ℝ)/factorDen) ((a : ℝ)/gridDen)/(2*((a : ℝ)/gridDen)) =
      -((firstNum a : ℝ)/firstDen a) := by
    have hb := first_sub a
    unfold dualPrice firstNum firstDen
    rw [Nat.cast_sub (Nat.le_sub_of_add_le (by rw [add_comm]; exact hb)),
      Nat.cast_sub (le_trans (Nat.le_add_right _ _) hb)]
    push_cast
    field_simp
    ring
  have htail (j : ℕ) : 1-dualPrice ((factorNum : ℝ)/factorDen) ((a : ℝ)/gridDen)*2^j =
      -(((2^j*priceNum a-priceDen a : ℕ) : ℝ)/priceDen a) := by
    have hle : priceDen a ≤ 2^j*priceNum a :=
      (priceDen_le a).trans (Nat.le_mul_of_pos_left _ (by positivity))
    rw [hprice, Nat.cast_sub hle]
    push_cast
    have : (0 : ℝ) < priceDen a := by exact_mod_cast hPD
    field_simp
    ring
  have hT (j : ℕ) : exp (1-dualPrice ((factorNum : ℝ)/factorDen) ((a : ℝ)/gridDen)*2^j) ≤
      (tailTerm a j : ℝ)/scale := by
    rw [htail j]
    exact expNegUp_sound _ _ _ hPD
  have h0 : exp (1-dualPrice ((factorNum : ℝ)/factorDen) ((a : ℝ)/gridDen)/(2*((a : ℝ)/gridDen))) ≤
      (expNegUp (firstNum a) (firstDen a) 0 : ℝ)/scale := by
    rw [hfirst]
    exact expNegUp_sound _ _ _ hFD
  have hc : ((scale/2^62 : ℕ) : ℝ)/scale = 1/2^62 := by
    unfold scale
    norm_num
  rw [factor_eq]
  unfold finitePartition
  rw [Fin.sum_univ_five]
  simp only [Fin.val_zero, Fin.val_one, Fin.val_two]
  have h3 : ((3 : Fin 5) : ℕ) = 3 := rfl
  have h4 : ((4 : Fin 5) : ℕ) = 4 := rfl
  rw [h3, h4]
  have hcrit : (crit a : ℝ)/scale = (expNegUp (firstNum a) (firstDen a) 0 : ℝ)/scale+
      ((tailTerm a 0 : ℝ)/scale+(tailTerm a 1 : ℝ)/scale+(tailTerm a 2 : ℝ)/scale+
        (tailTerm a 3 : ℝ)/scale+(tailTerm a 4 : ℝ)/scale)+((scale/2^62 : ℕ) : ℝ)/scale := by
    unfold crit
    push_cast
    ring
  rw [hcrit, hc]
  have t0 := hT 0
  have t1 := hT 1
  have t2 := hT 2
  have t3 := hT 3
  have t4 := hT 4
  norm_num at t0 t1 t2 t3 t4 ⊢
  linarith

end ThresholdHC.QuantileFactorUpper
