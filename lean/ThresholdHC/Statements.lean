import Mathlib

/-!
# Frozen target statements

DO NOT EDIT after the Phase 0 freeze (see `BRIEF.md`). The scorer checks this
file's SHA-256 against `FROZEN.sha256`.

Each target is a `def <name> : Prop` in namespace `ThresholdHC.Targets`.
Proofs live in `ThresholdHC/Proofs/*.lean` as
`theorem ThresholdHC.Proofs.<name> : ThresholdHC.Targets.<name>`.

References are to v4 of "A Distributional Minimax Law for Adaptive Threshold
Estimation". Every statement was checked numerically before freezing
(`tools/check_targets_numeric.py`); none is believed false.
-/

noncomputable section

namespace ThresholdHC

open Real MeasureTheory

/-- Bernoulli Kullback–Leibler divergence `kl(u, v)` (Mathlib's `log 0 = 0`). -/
def klB (u v : ℝ) : ℝ :=
  u * Real.log (u / v) + (1 - u) * Real.log ((1 - u) / (1 - v))

/-- Posterior probability of the positive sign: prior `1/2 + η`, likelihood ratio `L`. -/
def rhoPlus (η L : ℝ) : ℝ := (1/2 + η) * L / ((1/2 - η) + (1/2 + η) * L)

/-- Posterior probability of the positive sign: prior `1/2 - η`, likelihood ratio `L`. -/
def rhoMinus (η L : ℝ) : ℝ := (1/2 - η) * L / ((1/2 + η) + (1/2 - η) * L)

/-- Next-observation success probability for magnitude `d` and posterior `ρ`. -/
def pred (d ρ : ℝ) : ℝ := 1/2 - d + 2 * d * ρ

/-- Hard-pair sign perturbation `η_h(d) = min{1, h/d}/8` (paper eq. hard-pair). -/
def etaHard (h d : ℝ) : ℝ := (1/8) * min 1 (h / d)

/-- Level ratio `r = 2^{-1/2}` of the geometric level law. -/
def rLevel : ℝ := (Real.sqrt 2)⁻¹

/-- `H² = 1 - Σ √(p q)` on a finite space (affinity convention of Lemma B). -/
def hell2 {n : ℕ} (p q : Fin n → ℝ) : ℝ := 1 - ∑ i, Real.sqrt (p i * q i)

/-- Finite Kullback–Leibler divergence. -/
def klFin {n : ℕ} (p q : Fin n → ℝ) : ℝ := ∑ i, p i * Real.log (p i / q i)

/-- Mean of `Y` under weights `p`. -/
def meanFin {n : ℕ} (p Y : Fin n → ℝ) : ℝ := ∑ i, p i * Y i

/-- Variance of `Y` under weights `p`. -/
def varFin {n : ℕ} (p Y : Fin n → ℝ) : ℝ := ∑ i, p i * (Y i - meanFin p Y) ^ 2

namespace Targets

/-! ## Group A — posterior algebra (Lemma 3) -/

/-- A1 [Lemma 3, eq. (posterior)]. -/
def posterior_identity : Prop :=
  ∀ η L : ℝ, 0 ≤ η → η < 1/2 → 0 < L →
    rhoPlus η L - rhoMinus η L = 2 * η * L / (L + (1/4 - η ^ 2) * (L - 1) ^ 2)

/-- A2 [Lemma 3, eq. (posterior), inequality part]. -/
def posterior_diff_le : Prop :=
  ∀ η L : ℝ, 0 ≤ η → η < 1/2 → 0 < L → rhoPlus η L - rhoMinus η L ≤ 2 * η

/-- A3 Posteriors lie in (0,1) and are ordered. -/
def posterior_mem : Prop :=
  ∀ η L : ℝ, 0 ≤ η → η < 1/2 → 0 < L →
    0 < rhoMinus η L ∧ rhoMinus η L ≤ rhoPlus η L ∧ rhoPlus η L < 1

/-- A4 [Lemma 3 proof] `ξ(1-ξ) ≥ ρ(1-ρ)` for `ξ = 1/2 - d + 2dρ`, `d ≤ 1/2`. -/
def pred_variance_ge : Prop :=
  ∀ d ρ : ℝ, 0 ≤ d → d ≤ 1/2 → ρ * (1 - ρ) ≤ pred d ρ * (1 - pred d ρ)

/-- A5 [Lemma 3 proof] `L/(b+aL)² ≤ 1/(4ab)`. -/
def ratio_bound : Prop :=
  ∀ a b L : ℝ, 0 < a → 0 < b → 0 < L → L / (b + a * L) ^ 2 ≤ 1 / (4 * a * b)

/-! ## Group B — Bernoulli KL bounds (Lemma 3, Proposition 5) -/

/-- B1 [Lemma 3 proof] Taylor bound for Bernoulli KL, either order of arguments. -/
def kl_taylor_bound : Prop :=
  ∀ u v : ℝ, 0 < u → u < 1 → 0 < v → v < 1 →
    klB u v ≤ (u - v) ^ 2 / (2 * min (u * (1 - u)) (v * (1 - v)))

/-- B2 [Lemma 3, eq. (predictive)] forward direction. -/
def lemmaA_forward : Prop :=
  ∀ d η L : ℝ, 0 < d → d ≤ 1/2 → 0 ≤ η → η < 1/2 → 0 < L →
    klB (pred d (rhoPlus η L)) (pred d (rhoMinus η L))
      ≤ 32 * d ^ 2 * η ^ 2 / (1 - 4 * η ^ 2) ^ 2

/-- B3 [Lemma 3] reverse direction. -/
def lemmaA_reverse : Prop :=
  ∀ d η L : ℝ, 0 < d → d ≤ 1/2 → 0 ≤ η → η < 1/2 → 0 < L →
    klB (pred d (rhoMinus η L)) (pred d (rhoPlus η L))
      ≤ 32 * d ^ 2 * η ^ 2 / (1 - 4 * η ^ 2) ^ 2

/-- B4 [Lemma 3] sharpness of the constant 32 at `L = 1`. -/
def lemmaA_sharp_at_one : Prop :=
  ∀ d : ℝ, 0 < d → d ≤ 1/2 →
    Filter.Tendsto
      (fun η : ℝ => klB (pred d (rhoPlus η 1)) (pred d (rhoMinus η 1))
                      / (32 * d ^ 2 * η ^ 2 / (1 - 4 * η ^ 2) ^ 2))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 1)

/-- B5 [Proposition 5] per-observation bound for the hard pair: `≤ 128 h²/225`. -/
def hardpair_step_kl : Prop :=
  ∀ d h L : ℝ, 0 < d → d ≤ 1/2 → 0 < h → 0 < L →
    klB (pred d (rhoPlus (etaHard h d) L)) (pred d (rhoMinus (etaHard h d) L))
      ≤ (128/225) * h ^ 2

/-! ## Group C — Hellinger and the two-point converse (Lemma B, Theorem 2) -/

/-- C1 [Lemma B proof] `(x-y) log(x/y) ≥ 4(√x-√y)²`. -/
def sym_kl_hellinger_pointwise : Prop :=
  ∀ x y : ℝ, 0 < x → 0 < y →
    4 * (Real.sqrt x - Real.sqrt y) ^ 2 ≤ (x - y) * Real.log (x / y)

/-- C2 [Lemma B] `2H² ≤ KL` on a finite space with positive weights. -/
def kl_ge_two_hell_finite : Prop :=
  ∀ (n : ℕ) (p q : Fin n → ℝ), (∀ i, 0 < p i) → (∀ i, 0 < q i) →
    ∑ i, p i = 1 → ∑ i, q i = 1 → 2 * hell2 p q ≤ klFin p q

/-- C3 [Lemma B] `8H² ≤ KL(P,Q) + KL(Q,P)` on a finite space. -/
def sym_kl_ge_eight_hell_finite : Prop :=
  ∀ (n : ℕ) (p q : Fin n → ℝ), (∀ i, 0 < p i) → (∀ i, 0 < q i) →
    ∑ i, p i = 1 → ∑ i, q i = 1 → 8 * hell2 p q ≤ klFin p q + klFin q p

/-- C4 [Lemma B] two-point variance inequality on a finite space. -/
def two_point_variance_finite : Prop :=
  ∀ (n : ℕ) (p q Y : Fin n → ℝ), (∀ i, 0 ≤ p i) → (∀ i, 0 ≤ q i) →
    ∑ i, p i = 1 → ∑ i, q i = 1 →
    (meanFin p Y - meanFin q Y) ^ 2 * (1 - 2 * hell2 p q)
      ≤ 4 * hell2 p q * (varFin p Y + varFin q Y)

/-! ## Group D — fixed-gap sharpness of 1/16 (Theorem 2) -/

/-- D1 One-flip estimator `Y = (X - 1/2 + d)/(2d)` is unbiased for `q`. -/
def fixed_gap_unbiased : Prop :=
  ∀ d q : ℝ, 0 < d → d ≤ 1/2 →
    pred d q * ((1 - 1/2 + d) / (2 * d)) + (1 - pred d q) * ((0 - 1/2 + d) / (2 * d)) = q

/-- D2 Its variance is at most `1/(16 d²)`. -/
def fixed_gap_variance : Prop :=
  ∀ d q : ℝ, 0 < d → d ≤ 1/2 →
    pred d q * ((1 - 1/2 + d) / (2 * d) - q) ^ 2
      + (1 - pred d q) * ((0 - 1/2 + d) / (2 * d) - q) ^ 2 ≤ 1 / (16 * d ^ 2)

/-- D3 Equality at `q = 1/2`. -/
def fixed_gap_equality : Prop :=
  ∀ d : ℝ, 0 < d → d ≤ 1/2 →
    pred d (1/2) * ((1 - 1/2 + d) / (2 * d) - 1/2) ^ 2
      + (1 - pred d (1/2)) * ((0 - 1/2 + d) / (2 * d) - 1/2) ^ 2 = 1 / (16 * d ^ 2)

/-! ## Group E — inverse-binomial calibration (Lemma 4, Haldane) -/

/-- E1 Negative-binomial(2, p) probabilities sum to one (`K = k + 2`). -/
def negbin_total : Prop :=
  ∀ p : ℝ, 0 < p → p ≤ 1 → ∑' k : ℕ, ((k : ℝ) + 1) * p ^ 2 * (1 - p) ^ k = 1

/-- E2 `E K = 2/p`. -/
def negbin_mean : Prop :=
  ∀ p : ℝ, 0 < p → p ≤ 1 →
    ∑' k : ℕ, ((k : ℝ) + 2) * (((k : ℝ) + 1) * p ^ 2 * (1 - p) ^ k) = 2 / p

/-- E3 Haldane: `E[1/(K-1)] = p`. -/
def haldane_inverse_moment : Prop :=
  ∀ p : ℝ, 0 < p → p ≤ 1 →
    ∑' k : ℕ, ((k : ℝ) + 1)⁻¹ * (((k : ℝ) + 1) * p ^ 2 * (1 - p) ^ k) = p

/-! ## Group F — the modulus (eqs. scaling, power-modulus) -/

/-- F1 Pointwise upward scaling. -/
def scaling_up_pointwise : Prop :=
  ∀ c h x : ℝ, 1 ≤ c → 0 < h → 0 < x → min 1 (c * h / x) ≤ c * min 1 (h / x)

/-- F2 Pointwise downward scaling. -/
def scaling_down_pointwise : Prop :=
  ∀ b h x : ℝ, 0 < b → b ≤ 1 → 0 < h → 0 < x → b * min 1 (h / x) ≤ min 1 (b * h / x)

/-- F3 [eq. scaling] `ω(ch) ≤ c ω(h)` for any probability law on `(0, ∞)`. -/
def modulus_scaling_up : Prop :=
  ∀ μ : Measure ℝ, IsProbabilityMeasure μ → μ (Set.Iic 0) = 0 →
    ∀ c h : ℝ, 1 ≤ c → 0 < h →
      ∫ x, min 1 (c * h / x) ∂μ ≤ c * ∫ x, min 1 (h / x) ∂μ

/-- F4 [eq. power-modulus, α = 1] uniform law: `ω = u(1 - log u)`. -/
def power_modulus_critical : Prop :=
  ∀ u : ℝ, 0 < u → u < 1 →
    intervalIntegral (fun t : ℝ => min 1 (u / t)) 0 1 MeasureTheory.volume
      = u * (1 - Real.log u)

/-- F5 [eq. power-modulus, α ≠ 1] density `α t^(α-1)` on (0,1). -/
def power_modulus : Prop :=
  ∀ α u : ℝ, 0 < α → α ≠ 1 → 0 < u → u < 1 →
    intervalIntegral (fun t : ℝ => min 1 (u / t) * (α * t ^ (α - 1))) 0 1
        MeasureTheory.volume
      = (α * u - u ^ α) / (α - 1)

/-! ## Group G — numerical constants and confidence algebra -/

/-- G1 [Lemma 7] second-moment constant is below 85. -/
def constant_second_moment : Prop :=
  5 / (1 - rLevel) * (1 / (1 - rLevel) + 1 / (1 - rLevel ^ 3)) < 85

/-- G2 [Lemma 7] work constant is below 149. -/
def constant_work : Prop :=
  34 * (2 + Real.log 2 + rLevel * Real.log 2 / (1 - rLevel)) < 149

/-- G3 [eq. confidence-kl] `kl(1-δ, δ) = (1-2δ) log((1-δ)/δ)`. -/
def kl_delta_identity : Prop :=
  ∀ δ : ℝ, 0 < δ → δ < 1/2 → klB (1 - δ) δ = (1 - 2 * δ) * Real.log ((1 - δ) / δ)

/-- G4 [eq. confidence-kl] `(1-2δ) log((1-δ)/δ) ≥ log(1/δ)/4` on `(0, 1/4]`. -/
def kl_delta_lower : Prop :=
  ∀ δ : ℝ, 0 < δ → δ ≤ 1/4 →
    (1/4) * Real.log (1 / δ) ≤ (1 - 2 * δ) * Real.log ((1 - δ) / δ)

/-! ## Group H — classifier lemmas (Lemma 6) -/

/-- H1 [Lemma 6 proof] tail algebra `e^{-2x} + (2/3)e^{-2}x^{-2} < x^{-2}` for `x ≥ 1`. -/
def error_tail_bound : Prop :=
  ∀ x : ℝ, 1 ≤ x → Real.exp (-2 * x) + Real.exp (-2) * (2/3) * (x⁻¹) ^ 2 < (x⁻¹) ^ 2

/-- H2 [Lemma 6 proof] survival scale step. -/
def classifier_scale_step : Prop :=
  ∀ n N d : ℝ, 0 < n → n ≤ N → 0 < d → 1 ≤ N * d ^ 2 →
    d ≤ 2 * Real.sqrt ((1 + Real.log (N / n)) / n) →
      n * d ^ 2 ≤ 4 * (1 + Real.log (N * d ^ 2))

/-- H3 [eq. dyadic-integral, v = 1] `Σ_k 2^k e^{-b 2^k} ≤ 2/b`. -/
def dyadic_sum_v1 : Prop :=
  ∀ b : ℝ, 0 < b → ∑' k : ℕ, (2 : ℝ) ^ k * Real.exp (-(b * 2 ^ k)) ≤ 2 / b

/-- H4 [eq. dyadic-integral, v = 2] `Σ_k 4^k e^{-b 2^k} ≤ 8/(3b²)`. -/
def dyadic_sum_v2 : Prop :=
  ∀ b : ℝ, 0 < b → ∑' k : ℕ, ((2 : ℝ) ^ k) ^ 2 * Real.exp (-(b * 2 ^ k)) ≤ 8 / (3 * b ^ 2)

end Targets

end ThresholdHC
