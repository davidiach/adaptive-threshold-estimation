import ThresholdHC.Statements

/-!
# Tier 2 frozen target statements

Proposed 27 October 2026; frozen only after David's approval (see `TIER2.md`).
Same conventions as Tier 1: each target is a `def <name> : Prop` in
`ThresholdHC.Targets`, proved as `theorem ThresholdHC.Proofs.<name>` in
`ThresholdHC/Proofs/Tier2/*.lean`.

The 713 constant is not duplicated here: it is formalized, untruncated and for
arbitrary magnitude laws, by the separate `ThresholdHC.Uniform713` development
(`FullBound713Statement`, `tools/verify_uniform713.py`).

Everything here is finite and self-contained:
* the adaptive experiment is a deterministic policy over finitely many coins
  with revealed magnitudes, run for at most `n` steps (randomized policies are
  mixtures of these, and longer horizons follow by limits);
* classifiers act on finite Bernoulli streams `Fin M → Bool`.

Every statement was checked numerically before proposal
(`tools/check_targets2_numeric.py`).
-/

noncomputable section

namespace ThresholdHC

open Real MeasureTheory

/-! ## Finite information tools -/

/-- KL divergence of weight functions on a finite type (Mathlib's `log 0 = 0`). -/
def klFT {α : Type} [Fintype α] (P Q : α → ℝ) : ℝ := ∑ a, P a * Real.log (P a / Q a)

/-- Total variation distance on a finite type. -/
def tvFT {α : Type} [Fintype α] (P Q : α → ℝ) : ℝ := (1/2) * ∑ a, |P a - Q a|

/-! ## Adaptive experiments with revealed magnitudes -/

/-- Outcomes observed before step `t` of a padded transcript (`none` = no observation). -/
def histBefore {n : ℕ} (ω : Fin n → Option Bool) (t : Fin n) : List Bool :=
  (List.ofFn (fun j : Fin t.val => ω (Fin.castLE t.isLt.le j))).filterMap id

/-- Probability of a padded transcript under a deterministic adaptive policy, when coin `i`
has success probability `p i`. The policy sees the outcomes so far and returns the coin to
observe next, or `none` to stop; after stopping every entry must be `none`. -/
def pathProb {m n : ℕ} (pol : List Bool → Option (Fin m)) (p : Fin m → ℝ)
    (ω : Fin n → Option Bool) : ℝ :=
  ∏ t : Fin n,
    match pol (histBefore ω t), ω t with
    | none, none => 1
    | some i, some true => p i
    | some i, some false => 1 - p i
    | _, _ => 0

/-- Transcript law when coin `i` has magnitude `d i` and an independent sign with
`P(positive) = q i`. -/
def transcriptLaw {m n : ℕ} (pol : List Bool → Option (Fin m)) (d q : Fin m → ℝ)
    (ω : Fin n → Option Bool) : ℝ :=
  ∑ s : Fin m → Bool, (∏ i, if s i then q i else 1 - q i) *
    pathProb pol (fun i => 1/2 + (if s i then d i else -d i)) ω

/-- Number of observations actually taken in a padded transcript. -/
def workOf {n : ℕ} (ω : Fin n → Option Bool) : ℝ :=
  ((Finset.univ.filter (fun t : Fin n => (ω t).isSome = true)).card : ℝ)

/-! ## Capped dyadic classifiers on a shared Bernoulli stream (v4 Section 4) -/

/-- Number of successes among the first `k` entries of a stream. -/
def succCount {M : ℕ} (x : Fin M → Bool) (k : ℕ) : ℕ :=
  (Finset.univ.filter (fun i : Fin M => i.val < k ∧ x i = true)).card

/-- Early-stop threshold `t(n, N) = sqrt((k1 + k2 log(N/n))/n)`; v4 uses `k1 = k2 = 1`. -/
def thrK (k1 k2 : ℝ) (n N : ℕ) : ℝ :=
  Real.sqrt ((k1 + k2 * Real.log ((N : ℝ) / n)) / n)

/-- Decision of the cap-`2^L` classifier at prefix `2^j`: `some b` stops with output `b`,
`none` continues. At `j = L` it always decides; a tie is negative. -/
def checkpointK (k1 k2 : ℝ) (L j : ℕ) {M : ℕ} (x : Fin M → Bool) : Option Bool :=
  if j < L then
    (if (succCount x (2 ^ j) : ℝ) / (2 ^ j : ℝ) - 1/2 > thrK k1 k2 (2 ^ j) (2 ^ L) then some true
     else if 1/2 - (succCount x (2 ^ j) : ℝ) / (2 ^ j : ℝ) > thrK k1 k2 (2 ^ j) (2 ^ L) then
       some false
     else none)
  else
    (if (succCount x (2 ^ L) : ℝ) / (2 ^ L : ℝ) > 1/2 then some true else some false)

/-- Output and number of observations used by the cap-`2^L` classifier. -/
def classifyK (k1 k2 : ℝ) (L : ℕ) {M : ℕ} (x : Fin M → Bool) : Bool × ℕ :=
  match (List.range (L + 1)).findSome?
      (fun j => (checkpointK k1 k2 L j x).map (fun b => (b, 2 ^ j))) with
  | some r => r
  | none => (false, 2 ^ L)

/-- Probability of a stream for a coin with success probability `p`. -/
def streamProb {M : ℕ} (p : ℝ) (x : Fin M → Bool) : ℝ := ∏ i, if x i then p else 1 - p

/-- Success probability of a coin with magnitude `d` and sign `S`. -/
def coinP (d : ℝ) (S : Bool) : ℝ := 1/2 + (if S then d else -d)

/-- Misclassification probability of the cap-`2^L` classifier. -/
def errProbK (k1 k2 : ℝ) (L : ℕ) (d : ℝ) (S : Bool) : ℝ :=
  ∑ x : Fin (2 ^ L) → Bool,
    streamProb (coinP d S) x * (if (classifyK k1 k2 L x).1 = S then 0 else 1)

/-- Expected number of observations of the cap-`2^L` classifier. -/
def workK (k1 k2 : ℝ) (L : ℕ) (d : ℝ) (S : Bool) : ℝ :=
  ∑ x : Fin (2 ^ L) → Bool, streamProb (coinP d S) x * ((classifyK k1 k2 L x).2 : ℝ)

/-- `m_N(d) = min{N, d^{-2}[1 + log_+(N d²)]}`. -/
def mN (N d : ℝ) : ℝ := min N ((d⁻¹) ^ 2 * (1 + max 0 (Real.log (N * d ^ 2))))

/-- Classifier output as a real 0/1 value. -/
def zK (k1 k2 : ℝ) (l : ℕ) {M : ℕ} (x : Fin M → Bool) : ℝ :=
  if (classifyK k1 k2 l x).1 then 1 else 0

/-- Level increment `Δ_0 = Z_1`, `Δ_l = Z_{2^l} - Z_{2^{l-1}}` on a shared stream. -/
def deltaK (k1 k2 : ℝ) (l : ℕ) {M : ℕ} (x : Fin M → Bool) : ℝ :=
  if l = 0 then zK k1 k2 0 x else zK k1 k2 l x - zK k1 k2 (l - 1) x

/-- Work of a level increment: both classifiers run on the shared prefix. -/
def levelWork (k1 k2 : ℝ) (l : ℕ) {M : ℕ} (x : Fin M → Bool) : ℝ :=
  if l = 0 then ((classifyK k1 k2 0 x).2 : ℝ)
  else (max (classifyK k1 k2 l x).2 (classifyK k1 k2 (l - 1) x).2 : ℝ)

/-- Geometric level law `p_l = (1 - r) r^l`, `r = 2^{-1/2}`. -/
def pLevel (l : ℕ) : ℝ := (1 - rLevel) * rLevel ^ l

/-- `E[Y_L² | d, S] = Σ_{l ≤ L} E[Δ_l²]/p_l` for the single-term estimator truncated at `L`. -/
def secondMomentK (k1 k2 : ℝ) (L : ℕ) (d : ℝ) (S : Bool) : ℝ :=
  ∑ l ∈ Finset.range (L + 1),
    (∑ x : Fin (2 ^ L) → Bool, streamProb (coinP d S) x * (deltaK k1 k2 l x) ^ 2) / pLevel l

/-- `E[W_L | d, S] = Σ_{l ≤ L} p_l E[work of level l]`. -/
def workMomentK (k1 k2 : ℝ) (L : ℕ) (d : ℝ) (S : Bool) : ℝ :=
  ∑ l ∈ Finset.range (L + 1),
    pLevel l * ∑ x : Fin (2 ^ L) → Bool, streamProb (coinP d S) x * levelWork k1 k2 l x

namespace Targets

/-! ## Group I — information and testing (v4 Section 3) -/

/-- I1 Data processing for a two-cell partition (log-sum inequality). -/
def kl_data_processing_finite : Prop :=
  ∀ (α : Type) [Fintype α] (P Q : α → ℝ) (A : Finset α),
    (∀ a, 0 ≤ P a) → (∀ a, 0 ≤ Q a) → (∀ a, Q a = 0 → P a = 0) →
    ∑ a, P a = 1 → ∑ a, Q a = 1 →
    klB (∑ a ∈ A, P a) (∑ a ∈ A, Q a) ≤ klFT P Q

/-- I2 Pinsker's inequality on a finite type. -/
def pinsker_finite : Prop :=
  ∀ (α : Type) [Fintype α] (P Q : α → ℝ),
    (∀ a, 0 < P a) → (∀ a, 0 < Q a) → ∑ a, P a = 1 → ∑ a, Q a = 1 →
    tvFT P Q ≤ Real.sqrt (klFT P Q / 2)

/-- I3 [v4 §5.3] Two-point RMS lower bound via the midpoint test. -/
def two_point_rms_lower : Prop :=
  ∀ (α : Type) [Fintype α] (P Q θ : α → ℝ) (a b R : ℝ),
    (∀ x, 0 ≤ P x) → (∀ x, 0 ≤ Q x) → ∑ x, P x = 1 → ∑ x, Q x = 1 → a < b →
    ∑ x, P x * (θ x - a) ^ 2 ≤ R ^ 2 → ∑ x, Q x * (θ x - b) ^ 2 ≤ R ^ 2 →
    (b - a) ^ 2 * (1 - tvFT P Q) ≤ 8 * R ^ 2

/-- I4 Transcript laws are probability distributions. -/
def transcript_law_total : Prop :=
  ∀ (m n : ℕ) (pol : List Bool → Option (Fin m)) (d q : Fin m → ℝ),
    (∀ i, 0 ≤ d i ∧ d i ≤ 1/2) → (∀ i, 0 ≤ q i ∧ q i ≤ 1) →
    (∀ ω : Fin n → Option Bool, 0 ≤ transcriptLaw pol d q ω) ∧
    ∑ ω : Fin n → Option Bool, transcriptLaw pol d q ω = 1

/-- I5 [v4 Proposition 5, core] Stopped-transcript KL bound for the hard pair
`q_± = 1/2 ± η`, with `η ≤ 1/8` and `dη ≤ h/8` coin by coin. -/
def stopped_transcript_kl : Prop :=
  ∀ (m n : ℕ) (pol : List Bool → Option (Fin m)) (d η : Fin m → ℝ) (h : ℝ),
    0 < h → (∀ i, 0 < d i ∧ d i ≤ 1/2) → (∀ i, 0 ≤ η i ∧ η i ≤ 1/8) →
    (∀ i, d i * η i ≤ h / 8) →
    klFT (transcriptLaw (n := n) pol d (fun i => 1/2 + η i))
         (transcriptLaw (n := n) pol d (fun i => 1/2 - η i))
      ≤ (128/225) * h ^ 2 *
        ∑ ω : Fin n → Option Bool, transcriptLaw pol d (fun i => 1/2 + η i) ω * workOf ω

/-- I6 [v4 eq. finite-lower] Any test separating the hard pair with errors `≤ δ` forces
expected work at least `225 kl(1-δ, δ)/(128 h²)`. -/
def stopped_transcript_testing : Prop :=
  ∀ (m n : ℕ) (pol : List Bool → Option (Fin m)) (d η : Fin m → ℝ) (h δ : ℝ)
    (A : Finset (Fin n → Option Bool)),
    0 < h → (∀ i, 0 < d i ∧ d i ≤ 1/2) → (∀ i, 0 ≤ η i ∧ η i ≤ 1/8) →
    (∀ i, d i * η i ≤ h / 8) → 0 < δ → δ < 1/2 →
    1 - δ ≤ ∑ ω ∈ A, transcriptLaw pol d (fun i => 1/2 + η i) ω →
    ∑ ω ∈ A, transcriptLaw pol d (fun i => 1/2 - η i) ω ≤ δ →
    klB (1 - δ) δ ≤ (128/225) * h ^ 2 *
      ∑ ω : Fin n → Option Bool, transcriptLaw pol d (fun i => 1/2 + η i) ω * workOf ω

/-- I7 [next-phase Lemma "bounded-ratio decomposition", scalar core]. -/
def bounded_ratio_log : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 1 → ∃ C : ℝ, ∀ x : ℝ, 1 - κ ≤ x → x ≤ 1 + κ →
    -Real.log x + (x - 1) ≤ C * (Real.sqrt x - 1) ^ 2

/-! ## Group K — classifier and estimator as probability statements (v4 Lemmas 6–7) -/

/-- K1 [Lemma 6, eq. (error)]. -/
def lemma6_error : Prop :=
  ∀ (L : ℕ) (d : ℝ) (S : Bool), 0 < d → d ≤ 1/2 →
    errProbK 1 1 L d S ≤ min 1 ((((2 : ℝ) ^ L * d ^ 2)⁻¹) ^ 2)

/-- K2 [Lemma 6, eq. (work)]. -/
def lemma6_work : Prop :=
  ∀ (L : ℕ) (d : ℝ) (S : Bool), 0 < d → d ≤ 1/2 →
    workK 1 1 L d S ≤ 17 * mN ((2 : ℝ) ^ L) d

/-- K3 [Lemma 7, eq. (tele)] telescoping: `Σ_{l ≤ L} E[Δ_l] = P(Z_{2^L} = 1)`. -/
def lemma7_telescoping : Prop :=
  ∀ (L : ℕ) (d : ℝ) (S : Bool) (k1 k2 : ℝ),
    ∑ l ∈ Finset.range (L + 1),
        ∑ x : Fin (2 ^ L) → Bool, streamProb (coinP d S) x * deltaK k1 k2 l x
      = ∑ x : Fin (2 ^ L) → Bool, streamProb (coinP d S) x * zK k1 k2 L x

/-- K4 [Lemma 7, eq. (Y2)]. -/
def lemma7_second_moment : Prop :=
  ∀ (L : ℕ) (d : ℝ) (S : Bool), 0 < d → d ≤ 1/2 →
    secondMomentK 1 1 L d S ≤ 85 * min (Real.sqrt ((2 : ℝ) ^ L)) d⁻¹

/-- K5 [Lemma 7, eq. (Ywork)]. -/
def lemma7_work : Prop :=
  ∀ (L : ℕ) (d : ℝ) (S : Bool), 0 < d → d ≤ 1/2 →
    workMomentK 1 1 L d S ≤ 149 * min (Real.sqrt ((2 : ℝ) ^ L)) d⁻¹

/-! ## Group R — rare-event variational problem (next-phase Proposition "optimizer") -/

/-- R1 For an atomic magnitude law, the allocation `w*(d) = min{1, t²/d²}` maximizes
`Σ w_j min{v_j, h √v_j / d_j}` subject to `0 ≤ v ≤ 1`, `Σ w_j v_j ≤ ρ`. -/
def psi_optimizer_atomic : Prop :=
  ∀ (k : ℕ) (w d v : Fin k → ℝ) (ρ t h : ℝ),
    (∀ j, 0 < w j) → ∑ j, w j = 1 → (∀ j, 0 < d j ∧ d j ≤ 1/2) →
    0 < ρ → ρ < 1 → 0 < h → h < t →
    ∑ j, w j * min 1 (t ^ 2 / d j ^ 2) = ρ →
    (∀ j, 0 ≤ v j ∧ v j ≤ 1) → ∑ j, w j * v j ≤ ρ →
    ∑ j, w j * min (v j) (h * Real.sqrt (v j) / d j)
      ≤ ∑ j, w j * min (min 1 (t ^ 2 / d j ^ 2))
                       (h * Real.sqrt (min 1 (t ^ 2 / d j ^ 2)) / d j)

end Targets

end ThresholdHC
