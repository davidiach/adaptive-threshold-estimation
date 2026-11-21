import ThresholdHC.Tier5.CreationBase
import ThresholdHC.Tier5.PriorRatio

/-! The exact finite-prefix law of a policy that, up to a stopping length K
fixed in advance, creates one fresh coin per step and then stops. Each coin is
named by a function of the history that separates histories of different
lengths below K, so no coin is ever revisited. The law is a product of one
flip of success probability π k at each step k < K, followed by stop symbols.
The second-moment identity for a linear statistic of the flips follows. -/
noncomputable section
namespace ThresholdHC.OracleUpper
open ThresholdHC ThresholdHC.Tier3 ThresholdHC.Tier5 ThresholdHC.Proofs

/-- Signed value of an observation: one for heads, minus one for tails and
zero for a stop symbol. It equals `SharpRMS.bitValue` up to clause order and is
defined here so that the product-law modules do not import the `SharpRMS`
transcript. -/
def flipValue : Option Bool → ℝ
  | none => 0
  | some true => 1
  | some false => -1

/-- One factor of the product law: an informative flip with success
probability π k at a step k below K, and a stop symbol afterwards. -/
def freshAtom (K : ℕ) (π : ℕ → ℝ) (k : ℕ) (o : Option Bool) : ℝ :=
  if k < K then obsProb (π k) o else if o = none then 1 else 0

/-- The product law on padded prefixes. -/
def freshProduct (K : ℕ) (π : ℕ → ℝ) : {n : ℕ} → Prefix n → ℝ
  | 0, _ => 1
  | n+1, w => freshProduct K π (Fin.init w) * freshAtom K π n (w (Fin.last n))

private theorem hist_snoc {n : ℕ} (w : Fin n → Option Bool) (o : Option Bool) :
    fullHist (Fin.snoc w o) = fullHist w ++ o.toList := by
  unfold fullHist
  rw [List.ofFn_succ']
  simp only [Fin.snoc_castSucc, Fin.snoc_last]
  cases o <;> simp [List.concat_eq_append]

private theorem product_shape (K : ℕ) (π : ℕ → ℝ) {n : ℕ} (w : Prefix n)
    (hn : freshProduct K π w ≠ 0) : (fullHist w).length = min n K := by
  induction n with
  | zero => simp [fullHist]
  | succ n ih =>
    rw [← Fin.snoc_init_self w] at hn ⊢
    generalize Fin.init w = v at hn ⊢
    generalize w (Fin.last n) = o at hn ⊢
    simp only [freshProduct, Fin.init_snoc, Fin.snoc_last] at hn
    have h := ih v (left_ne_zero_of_mul hn)
    have ho := right_ne_zero_of_mul hn
    rw [hist_snoc, List.length_append, h]
    by_cases hd : n < K <;> cases o <;> simp_all [freshAtom, obsProb] <;> omega

private theorem next_zero {n : ℕ} (pol : List Bool → Option ℕ) (d q : ℕ → ℝ)
    (hd : ∀ i, 0 ≤ d i ∧ d i ≤ 1/2) (hq : ∀ i, 0 ≤ q i ∧ q i ≤ 1)
    (w : Prefix n) (o : Option Bool) (hz : creationLaw pol d q w = 0) :
    creationLaw pol d q (Fin.snoc w o) = 0 := by
  let P := fun a => creationLaw pol d q (Fin.snoc w a)
  have pos (a) : 0 ≤ P a := (creationLaw_total _ pol d q hd hq).1 _
  have sum := creationLaw_sum_extensions pol d q w
  rw [hz] at sum
  exact le_antisymm ((Finset.single_le_sum (f := P) (fun a _ => pos a)
    (Finset.mem_univ o)).trans_eq sum) (pos o)

private theorem query_fresh {n : ℕ} (pol : List Bool → Option ℕ) (d q : ℕ → ℝ)
    (w : Prefix n) (i : ℕ) (hi : pol (fullHist w) = some i)
    (unused : ∀ j : Fin n, pol (histBefore w j) ≠ some i) (o : Option Bool) :
    creationLaw pol d q (Fin.snoc w o) =
      creationLaw pol d q w * obsProb (1/2 + (2 * q i - 1) * d i) o := by
  let m := coinCap (n+1) pol
  have lt : i < m := selected_lt_coinCap pol (Fin.snoc w o) (Fin.last n) i
    (by simpa only [histBefore_snoc_last] using hi)
  let a : Fin m := ⟨i, lt⟩
  let π := capPolicy m pol
  have act : π (fullHist w) = some a := by simp [π, capPolicy, hi, lt, a]
  have fresh : a ∉ queriedCoins π w := by
    simp only [queriedCoins, Finset.mem_biUnion, Finset.mem_univ, true_and, not_exists]
    intro j
    cases h : pol (histBefore w j) with
    | none => simp [π, capPolicy, h]
    | some k =>
      have diff : k ≠ i := by intro e; exact unused j (h.trans (congrArg some e))
      by_cases hk : k < m <;> simp [π, capPolicy, h, hk, a, Ne.symm diff]
  have c := coinLike_eq_one_of_not_queried π w a fresh
  rw [creationLaw_eq_capped pol _ _ w m (coinCap_le_succ n pol)]
  change transcriptLaw π _ _ (Fin.snoc w o) = transcriptLaw π _ _ w * _
  rw [transcriptLaw_query π _ _ w a act, transcriptLaw_split π _ _ w a]
  simp only [coinMix, c, mul_one]
  cases o with
  | none => simp [obsProb]
  | some b => cases b <;> simp [obsProb, a] <;> ring

private theorem stop_word {n : ℕ} (pol : List Bool → Option ℕ) (d q : ℕ → ℝ)
    (w : Prefix n) (hs : pol (fullHist w) = none) (o : Option Bool) :
    creationLaw pol d q (Fin.snoc w o) = if o = none then creationLaw pol d q w else 0 := by
  rw [creationLaw_eq_capped pol _ _ w _ (coinCap_le_succ n pol)]
  exact transcriptLaw_stop _ _ _ w (by simp [capPolicy, hs]) o

/-- A policy that names a fresh coin at each step below K and then stops has
the product law, provided the names separate lengths below K and the coin
created at length k has flip probability π k. -/
theorem named_product (pol : List Bool → Option ℕ) (d q : ℕ → ℝ)
    (hd : ∀ i, 0 ≤ d i ∧ d i ≤ 1/2) (hq : ∀ i, 0 ≤ q i ∧ q i ≤ 1)
    (K : ℕ) (name : List Bool → ℕ) (π : ℕ → ℝ)
    (hpol : ∀ xs, pol xs = if xs.length < K then some (name xs) else none)
    (hname : ∀ x y, x.length < K → y.length < K → name x = name y → x.length = y.length)
    (hπ : ∀ xs, xs.length < K → 1/2 + (2 * q (name xs) - 1) * d (name xs) = π xs.length)
    {n : ℕ} (w : Prefix n) :
    creationLaw pol d q w = freshProduct K π w := by
  induction n with
  | zero => simp [creationLaw, transcriptLaw_factor, pathValidity, coinLike, freshProduct]
  | succ n ih =>
    rw [← Fin.snoc_init_self w]
    generalize Fin.init w = v
    generalize w (Fin.last n) = o
    simp only [freshProduct, Fin.init_snoc, Fin.snoc_last]
    by_cases zero : freshProduct K π v = 0
    · rw [zero, zero_mul]
      exact next_zero pol d q hd hq v o ((ih v).trans zero)
    have shape := product_shape K π v zero
    by_cases h : n < K
    · have len : (fullHist v).length = n := shape.trans (min_eq_left h.le)
      have active : (fullHist v).length < K := len.trans_lt h
      rw [query_fresh pol d q v (name (fullHist v)) (by rw [hpol]; simp [active]) _ o, ih,
        hπ _ active, len]
      · simp [freshAtom, h]
      intro j eq
      have lt : (histBefore v j).length < K :=
        ((histBefore_length_le v j).trans_lt j.isLt).trans h
      rw [hpol] at eq
      simp only [lt, ite_true, Option.some.injEq] at eq
      have same := hname _ _ lt active eq
      have lj := histBefore_length_le v j
      have jl := j.isLt
      omega
    · have len : (fullHist v).length = K := shape.trans (min_eq_right (by omega))
      rw [stop_word pol d q v (by rw [hpol]; simp [len]) o, ih]
      cases o <;> simp [freshAtom, h]

theorem freshProduct_total (K : ℕ) (π : ℕ → ℝ) (n : ℕ) :
    ∑ w : Prefix n, freshProduct K π w = 1 := by
  induction n with
  | zero => simp [freshProduct]
  | succ n ih =>
    rw [sum_snoc]
    have h (w : Prefix n) :
        ∑ o : Option Bool, freshProduct K π (Fin.snoc w o) = freshProduct K π w := by
      simp only [freshProduct, Fin.init_snoc, Fin.snoc_last, ← Finset.mul_sum]
      have : ∑ o : Option Bool, freshAtom K π n o = 1 := by
        by_cases hn : n < K <;> simp [freshAtom, hn, Fintype.sum_option, obsProb]
      rw [this, mul_one]
    simp_rw [h]
    exact ih

/-- Exact second moment of an affine statistic of the signed flips under the
product law. -/
theorem freshProduct_moment (K : ℕ) (π : ℕ → ℝ) (n : ℕ) (κ β : ℝ) :
    ∑ w : Prefix n, freshProduct K π w * (κ + β * ∑ k, flipValue (w k))^2 =
      (κ + β * ∑ k ∈ Finset.range (min n K), (2 * π k - 1))^2 +
        β^2 * ∑ k ∈ Finset.range (min n K), (1 - (2 * π k - 1)^2) := by
  induction n generalizing κ with
  | zero => simp [freshProduct]
  | succ n ih =>
    rw [sum_snoc]
    have step (w : Prefix n) :
        ∑ o : Option Bool, freshProduct K π (Fin.snoc w o) *
          (κ + β * ∑ k, flipValue ((Fin.snoc w o : Prefix (n+1)) k))^2 =
        freshProduct K π w * (if n < K then
          (κ + β * (2 * π n - 1) + β * ∑ k, flipValue (w k))^2 + β^2 * (1 - (2 * π n - 1)^2)
          else (κ + β * ∑ k, flipValue (w k))^2) := by
      simp only [freshProduct, Fin.init_snoc, Fin.snoc_last, Fin.sum_univ_castSucc,
        Fin.snoc_castSucc]
      by_cases hn : n < K
      · simp only [freshAtom, hn, ite_true, Fintype.sum_option, Fintype.sum_bool, obsProb,
          flipValue]
        ring
      · simp [freshAtom, hn, flipValue]
    simp_rw [step]
    by_cases hn : n < K
    · simp only [hn, ite_true, mul_add, Finset.sum_add_distrib, ← Finset.sum_mul,
        freshProduct_total, one_mul, ih]
      rw [min_eq_left (Nat.succ_le_of_lt hn), min_eq_left hn.le, Finset.sum_range_succ,
        Finset.sum_range_succ]
      ring
    · simp only [hn, ite_false, ih]
      rw [min_eq_right (by omega : K ≤ n + 1), min_eq_right (by omega : K ≤ n)]

end ThresholdHC.OracleUpper
