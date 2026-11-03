import ThresholdHC.EntropyTailLower.ActivationGate
import ThresholdHC.CriticalEntropy.ObservationModel

/-! Uniform likelihood bounds on the actual gate's stopped prefixes.
The constants are deliberately conservative: the density relative to a fair
prefix lies between exp(-12) and exp(12), uniformly over both signs and all
gaps below the gate's scale. No probability bound on gate activation is yet
asserted here. -/
noncomputable section
open MeasureTheory Real
namespace ThresholdHC.EntropyTailLower
open ThresholdHC.CriticalEntropy

theorem log_one_add_quadratic (x : ℝ) (hx : |x| ≤ 1/2) :
    x-2*x^2 ≤ log (1+x) ∧ log (1+x) ≤ x := by
  have hp : 0 < 1+x := by linarith [(abs_le.mp hx).1]
  have hl : x-2*x^2 ≤ x/(1+x) := by
    apply (le_div_iff₀ hp).mpr
    nlinarith [mul_nonneg (sq_nonneg x) (show 0 ≤ 1+2*x by linarith [(abs_le.mp hx).1])]
  have he : x/(1+x) = 1-(1+x)⁻¹ := by field_simp; ring
  refine ⟨hl.trans ?_,?_⟩
  · rw [he]
    exact one_sub_inv_le_log_of_pos hp
  · linarith [log_le_sub_one_of_pos hp]

def gatePrefixLikelihood (d : ℝ) (n k : ℕ) : ℝ :=
  (1+2*d)^k*(1-2*d)^(n-k)

/-- Exact factorization relative to the fair-word probability. -/
theorem gatePrefixLikelihood_factor (d : ℝ) (n k : ℕ) (hk : k ≤ n) :
    (1/2+d)^k*(1/2-d)^(n-k) = (1/2:ℝ)^n*gatePrefixLikelihood d n k := by
  have hp : 1/2+d = (1/2:ℝ)*(1+2*d) := by ring
  have hm : 1/2-d = (1/2:ℝ)*(1-2*d) := by ring
  rw [hp,hm,mul_pow,mul_pow]
  have hn : k+(n-k) = n := Nat.add_sub_of_le hk
  calc
    _ = ((1/2:ℝ)^k*(1/2:ℝ)^(n-k))*gatePrefixLikelihood d n k := by
      unfold gatePrefixLikelihood
      ring
    _ = _ := by rw [← pow_add,hn]

theorem gatePrefixLikelihood_ratio (d : ℝ) (n k : ℕ) (hk : k ≤ n) :
    ((1/2+d)^k*(1/2-d)^(n-k))/(1/2:ℝ)^n = gatePrefixLikelihood d n k := by
  rw [gatePrefixLikelihood_factor d n k hk]
  exact mul_div_cancel_left₀ _ (pow_ne_zero _ (by norm_num : (1/2:ℝ) ≠ 0))

theorem gatePrefixLikelihood_positive (d : ℝ) (hd : |d| ≤ 1/4) (n k : ℕ) :
    0 < gatePrefixLikelihood d n k := by
  have hp : 0 < 1+2*d := by linarith [(abs_le.mp hd).1]
  have hm : 0 < 1-2*d := by linarith [(abs_le.mp hd).2]
  exact mul_pos (pow_pos hp _) (pow_pos hm _)

theorem gatePrefixLikelihood_log (d : ℝ) (hd : |d| ≤ 1/4) (n k : ℕ) (hk : k ≤ n) :
    2*d*(2*(k:ℝ)-(n:ℝ))-8*(n:ℝ)*d^2 ≤ log (gatePrefixLikelihood d n k) ∧
      log (gatePrefixLikelihood d n k) ≤ 2*d*(2*(k:ℝ)-(n:ℝ)) := by
  have hp : 0 < 1+2*d := by linarith [(abs_le.mp hd).1]
  have hm : 0 < 1-2*d := by linarith [(abs_le.mp hd).2]
  have hp' := log_one_add_quadratic (2*d) (by rw [abs_mul]; norm_num; linarith)
  have hm' := log_one_add_quadratic (-2*d) (by rw [abs_mul]; norm_num; linarith)
  have hlo₁ := mul_le_mul_of_nonneg_left hp'.1 (Nat.cast_nonneg k : (0:ℝ) ≤ k)
  have hhi₁ := mul_le_mul_of_nonneg_left hp'.2 (Nat.cast_nonneg k : (0:ℝ) ≤ k)
  have hlo₀ := mul_le_mul_of_nonneg_left hm'.1 (Nat.cast_nonneg (n-k) : (0:ℝ) ≤ (n-k:ℕ))
  have hhi₀ := mul_le_mul_of_nonneg_left hm'.2 (Nat.cast_nonneg (n-k) : (0:ℝ) ≤ (n-k:ℕ))
  rw [Nat.cast_sub hk] at hlo₀ hhi₀
  have he : 1+(-2*d) = 1-2*d := by ring
  rw [he] at hlo₀ hhi₀
  rw [gatePrefixLikelihood,log_mul (pow_pos hp _).ne' (pow_pos hm _).ne',log_pow,log_pow,
    Nat.cast_sub hk]
  constructor <;> nlinarith only [hlo₁,hlo₀,hhi₁,hhi₀]

theorem gate_scale_ceiling_bounds (a : ℝ) (ha : 0 < a) :
    a*(⌈a⁻¹⌉₊:ℝ) ≤ 1+a ∧ a^2*(⌈(a^2)⁻¹⌉₊:ℝ) ≤ 1+a^2 := by
  have hh := mul_le_mul_of_nonneg_left
    (Nat.ceil_lt_add_one (inv_nonneg.mpr ha.le)).le ha.le
  have hn := mul_le_mul_of_nonneg_left
    (Nat.ceil_lt_add_one (inv_nonneg.mpr (sq_nonneg a))).le (sq_nonneg a)
  rw [mul_add,mul_inv_cancel₀ ha.ne',mul_one] at hh
  rw [mul_add,mul_inv_cancel₀ (pow_ne_zero 2 ha.ne'),mul_one] at hn
  exact ⟨hh,hn⟩

theorem gatePrefixLikelihood_uniform (a d : ℝ) (ha : 0 < a) (ha4 : a ≤ 1/4)
    (hd : |d| ≤ a) (n k : ℕ) (hk : k ≤ n)
    (hn : n ≤ ⌈(a^2)⁻¹⌉₊) (hb : |2*(k:ℝ)-(n:ℝ)| ≤ (⌈a⁻¹⌉₊:ℝ)) :
    exp (-12) ≤ gatePrefixLikelihood d n k ∧ gatePrefixLikelihood d n k ≤ exp 12 := by
  have hlog := gatePrefixLikelihood_log d (hd.trans ha4) n k hk
  obtain ⟨hH,hN⟩ := gate_scale_ceiling_bounds a ha
  have hnr : (n:ℝ) ≤ ⌈(a^2)⁻¹⌉₊ := by exact_mod_cast hn
  have hdsq : d^2 ≤ a^2 := by nlinarith [(sq_le_sq₀ (abs_nonneg d) ha.le).mpr hd,sq_abs d]
  have hnsmall : (n:ℝ)*d^2 ≤ 1+a^2 := by
    calc
      _ ≤ (n:ℝ)*a^2 := mul_le_mul_of_nonneg_left hdsq (Nat.cast_nonneg _)
      _ ≤ a^2*(⌈(a^2)⁻¹⌉₊:ℝ) := by nlinarith [mul_le_mul_of_nonneg_left hnr (sq_nonneg a)]
      _ ≤ _ := hN
  have hbalance : |d*(2*(k:ℝ)-(n:ℝ))| ≤ 1+a := by
    rw [abs_mul]
    exact (mul_le_mul hd hb (abs_nonneg _) ha.le).trans hH
  have hasq : a^2 ≤ 1/16 := by nlinarith
  have hlo : -12 ≤ log (gatePrefixLikelihood d n k) := by
    nlinarith [hlog.1,(abs_le.mp hbalance).1]
  have hhi : log (gatePrefixLikelihood d n k) ≤ 12 := by
    nlinarith [hlog.2,(abs_le.mp hbalance).2]
  have he := exp_log (gatePrefixLikelihood_positive d (hd.trans ha4) n k)
  constructor
  · simpa only [he] using exp_le_exp.mpr hlo
  · simpa only [he] using exp_le_exp.mpr hhi

theorem tapeBalance_heads (n : ℕ) (ω : ℕ → Bool) :
    tapeBalance n ω = 2*(wordHeads (Tier2.tapePrefix n ω):ℤ)-(n:ℤ) := by
  unfold tapeBalance
  rw [← Fin.sum_univ_eq_sum_range]
  have he (i : Fin n) : (if ω i then (1:ℤ) else -1) = 2*(if ω i then (1:ℤ) else 0)-1 := by
    cases ω i <;> norm_num
  simp_rw [he]
  rw [Finset.sum_sub_distrib,← Finset.mul_sum]
  simp [wordHeads,Tier2.tapePrefix]
  rfl

/-- The likelihood factor of the gate's actual stopped word is uniformly
bounded. The original procedure may stop at infinity. -/
theorem activationGate_prefix_likelihood {R E : Type} [MeasurableSpace R] [MeasurableSpace E]
    (A : StoppedProcedure R E) (a d : ℝ) (ha : 0 < a) (ha4 : a ≤ 1/4)
    (hd : |d| ≤ a) (z : R × (ℕ → Bool)) :
    let n := activationGateCost A ⌈(a^2)⁻¹⌉₊ ⌈a⁻¹⌉₊ z
    let k := wordHeads (Tier2.tapePrefix n z.2)
    exp (-12) ≤ gatePrefixLikelihood d n k ∧ gatePrefixLikelihood d n k ≤ exp 12 := by
  dsimp only
  have hg := activationGate_bounds A ⌈(a^2)⁻¹⌉₊ ⌈a⁻¹⌉₊ z
  have hk : wordHeads (Tier2.tapePrefix (activationGateCost A ⌈(a^2)⁻¹⌉₊ ⌈a⁻¹⌉₊ z) z.2) ≤
      activationGateCost A ⌈(a^2)⁻¹⌉₊ ⌈a⁻¹⌉₊ z := by
    unfold wordHeads
    simpa using Finset.card_filter_le (s := Finset.univ)
      (fun i => Tier2.tapePrefix (activationGateCost A ⌈(a^2)⁻¹⌉₊ ⌈a⁻¹⌉₊ z) z.2 i = true)
  apply gatePrefixLikelihood_uniform a d ha ha4 hd _ _ hk hg.1
  rw [tapeBalance_heads] at hg
  exact_mod_cast hg.2

end ThresholdHC.EntropyTailLower
