import ThresholdHC.EntropyTailLower.GateLikelihood

/-! Signwise likelihood differences on bounded gate prefixes. This controls
the density difference; integrating an early-output mean is a separate step. -/

noncomputable section
open MeasureTheory Real
namespace ThresholdHC.EntropyTailLower
open ThresholdHC.CriticalEntropy

theorem exp_sub_le_scaled_sub (x y C : ℝ) (hxy : x ≤ y) (hy : y ≤ C) :
    exp y-exp x ≤ exp C*(y-x) := by
  have ht := add_one_le_exp (x-y)
  have he : exp y*exp (x-y) = exp x := by rw [← exp_add]; congr 1; ring
  have h := mul_le_mul_of_nonneg_left ht (exp_pos y).le
  rw [he] at h
  calc
    _ ≤ exp y*(y-x) := by nlinarith only [h]
    _ ≤ _ := mul_le_mul_of_nonneg_right (exp_le_exp.mpr hy) (sub_nonneg.mpr hxy)

theorem exp_abs_sub_le (x y C : ℝ) (hx : x ≤ C) (hy : y ≤ C) :
    |exp x-exp y| ≤ exp C*|x-y| := by
  rcases le_total x y with h | h
  · rw [abs_of_nonpos (sub_nonpos.mpr (exp_le_exp.mpr h)),abs_of_nonpos (sub_nonpos.mpr h)]
    simpa only [neg_sub] using exp_sub_le_scaled_sub x y C h hy
  · rw [abs_of_nonneg (sub_nonneg.mpr (exp_le_exp.mpr h)),abs_of_nonneg (sub_nonneg.mpr h)]
    exact exp_sub_le_scaled_sub y x C h hx

theorem log_one_add_abs_le (x : ℝ) (hx : |x| ≤ 1/2) :
    |log (1+x)| ≤ 2*|x| := by
  have hb := log_one_add_quadratic x hx
  have hs : 2*x^2 ≤ |x| := by nlinarith [sq_abs x, abs_nonneg x]
  apply abs_le.mpr
  constructor <;> linarith [(le_abs_self x),(neg_abs_le x)]

theorem gatePrefixLikelihood_log_difference (d : ℝ) (hd : |d| ≤ 1/4)
    (n k : ℕ) (hk : k ≤ n) :
    log (gatePrefixLikelihood d n k)-log (gatePrefixLikelihood (-d) n k) =
      (2*(k:ℝ)-(n:ℝ))*(log (1+2*d)-log (1-2*d)) := by
  have hp : 0 < 1+2*d := by linarith [(abs_le.mp hd).1]
  have hm : 0 < 1-2*d := by linarith [(abs_le.mp hd).2]
  have h₀ : 1+2*(-d) = 1-2*d := by ring
  have h₁ : 1-2*(-d) = 1+2*d := by ring
  rw [gatePrefixLikelihood,gatePrefixLikelihood,h₀,h₁,
    log_mul (pow_pos hp _).ne' (pow_pos hm _).ne',
    log_mul (pow_pos hm _).ne' (pow_pos hp _).ne']
  simp only [log_pow,Nat.cast_sub hk]
  ring

theorem gatePrefixLikelihood_difference (a d : ℝ) (ha : 0 < a) (ha4 : a ≤ 1/4)
    (hd : |d| ≤ a) (n k : ℕ) (hk : k ≤ n)
    (hn : n ≤ ⌈(a^2)⁻¹⌉₊) (hb : |2*(k:ℝ)-(n:ℝ)| ≤ (⌈a⁻¹⌉₊:ℝ)) :
    |gatePrefixLikelihood d n k-gatePrefixLikelihood (-d) n k| ≤
      8*exp 12*|d| * |2*(k:ℝ)-(n:ℝ)| := by
  have hd4 := hd.trans ha4
  have hneg : |-d| ≤ a := by simpa using hd
  have hp := gatePrefixLikelihood_positive d hd4 n k
  have hm := gatePrefixLikelihood_positive (-d) (hneg.trans ha4) n k
  have hpu := (gatePrefixLikelihood_uniform a d ha ha4 hd n k hk hn hb).2
  have hmu := (gatePrefixLikelihood_uniform a (-d) ha ha4 hneg n k hk hn hb).2
  have hlp : log (gatePrefixLikelihood d n k) ≤ 12 := by
    simpa only [log_exp] using log_le_log hp hpu
  have hlm : log (gatePrefixLikelihood (-d) n k) ≤ 12 := by
    simpa only [log_exp] using log_le_log hm hmu
  have hlogp := log_one_add_abs_le (2*d) (by rw [abs_mul]; norm_num; linarith)
  have hlogm := log_one_add_abs_le (-2*d) (by rw [abs_mul]; norm_num; linarith)
  have harg : 1+(-2*d) = 1-2*d := by ring
  rw [harg] at hlogm
  have hlogs : |log (1+2*d)-log (1-2*d)| ≤ 8*|d| := by
    have htri := abs_sub_le (log (1+2*d)) 0 (log (1-2*d))
    simp only [sub_zero,zero_sub,abs_neg,abs_mul] at htri hlogp hlogm
    norm_num at hlogp hlogm
    linarith
  have he := exp_abs_sub_le (log (gatePrefixLikelihood d n k))
    (log (gatePrefixLikelihood (-d) n k)) 12 hlp hlm
  rw [exp_log hp,exp_log hm,gatePrefixLikelihood_log_difference d hd4 n k hk,abs_mul] at he
  calc
    _ ≤ exp 12*(|2*(k:ℝ)-(n:ℝ)| * |log (1+2*d)-log (1-2*d)|) := he
    _ ≤ exp 12*(|2*(k:ℝ)-(n:ℝ)| * (8*|d|)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hlogs (abs_nonneg _)) (exp_pos _).le
    _ = _ := by ring

theorem activationGate_prefix_likelihood_difference {R E : Type}
    [MeasurableSpace R] [MeasurableSpace E] (A : StoppedProcedure R E)
    (a d : ℝ) (ha : 0 < a) (ha4 : a ≤ 1/4) (hd : |d| ≤ a)
    (z : R × (ℕ → Bool)) :
    let n := activationGateCost A ⌈(a^2)⁻¹⌉₊ ⌈a⁻¹⌉₊ z
    let k := wordHeads (Tier2.tapePrefix n z.2)
    |gatePrefixLikelihood d n k-gatePrefixLikelihood (-d) n k| ≤
      8*exp 12*|d| * |(tapeBalance n z.2:ℝ)| := by
  dsimp only
  have hg := activationGate_bounds A ⌈(a^2)⁻¹⌉₊ ⌈a⁻¹⌉₊ z
  have hk : wordHeads (Tier2.tapePrefix (activationGateCost A ⌈(a^2)⁻¹⌉₊ ⌈a⁻¹⌉₊ z) z.2) ≤
      activationGateCost A ⌈(a^2)⁻¹⌉₊ ⌈a⁻¹⌉₊ z := by
    unfold wordHeads
    simpa using Finset.card_filter_le (s := Finset.univ)
      (fun i => Tier2.tapePrefix (activationGateCost A ⌈(a^2)⁻¹⌉₊ ⌈a⁻¹⌉₊ z) z.2 i = true)
  have he (n : ℕ) : (tapeBalance n z.2:ℝ) =
      2*(wordHeads (Tier2.tapePrefix n z.2):ℝ)-(n:ℝ) := by
    exact_mod_cast tapeBalance_heads n z.2
  rw [he]
  apply gatePrefixLikelihood_difference a d ha ha4 hd _ _ hk hg.1
  rw [tapeBalance_heads] at hg
  exact_mod_cast hg.2

end ThresholdHC.EntropyTailLower
