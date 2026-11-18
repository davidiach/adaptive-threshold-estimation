import ThresholdHC.UpperWork.Dyadic
import ThresholdHC.Proofs.Tier2.ClassifierModel

/-! A sharper expected-work bound for the early-stopping classifier.

The classifier at cap `2^L` survives its check `k` only if the running mean
stays within `threshold1 (cap k) (cap L)` of one half. When that threshold is
below the gap `d`, Hoeffding's inequality bounds the survival probability by
`exp(-2*cap k*(d-threshold)^2)` (`survivalBound`). With
`u = 1 + log (cap L*d^2)`, the threshold is below `d` once `cap k*d^2 > u`, and
there the term `cap k*survivalBound` is at most the dyadic term `bump` of
`Dyadic`, in units of `u/d^2`. The offset sum then gives
`E[work] ≤ (49/10)*d⁻²*(1 + log (cap L*d^2))` whenever `cap L*d^2 ≥ 1`, in
place of the factor 17 of `Tier2.Model.work_bound_of_survival`. -/
noncomputable section
namespace ThresholdHC.UpperWork
open MeasureTheory Real Finset ThresholdHC.Uniform713

/-- The sharp survival bound at check `k` of the cap-`2^L` classifier on a coin
with gap `d`. -/
def survivalBound (L k : ℕ) (d : ℝ) : ℝ :=
  if Tier2.Model.threshold1 (cap k) (cap L) ≤ d then
    Real.exp (-2 * cap k * (d - Tier2.Model.threshold1 (cap k) (cap L)) ^ 2) else 1

theorem survivalBound_le_one (L k : ℕ) (d : ℝ) : survivalBound L k d ≤ 1 := by
  unfold survivalBound
  split_ifs
  · rw [← Real.exp_zero]
    apply Real.exp_le_exp.2
    have := cap_pos k
    nlinarith [sq_nonneg (d - Tier2.Model.threshold1 (cap k) (cap L))]
  · exact le_rfl

/-- Past the stopping scale `u`, one survival term is at most the dyadic term
`bump` at the ratio `cap k*d^2/u`, in units of `u/d^2`. -/
theorem cap_mul_survivalBound_le (L k : ℕ) (hk : k < L) {d : ℝ} (hd : 0 < d)
    (hx : 1 ≤ cap L * d ^ 2) (hy : 1 + Real.log (cap L * d ^ 2) < cap k * d ^ 2) :
    cap k * survivalBound L k d ≤
      ((1 + Real.log (cap L * d ^ 2)) / d ^ 2) *
        bump (cap k * d ^ 2 / (1 + Real.log (cap L * d ^ 2))) := by
  have hn : 0 < cap k := cap_pos k
  have hnN : cap k ≤ cap L := Tier2.Model.cap_mono hk.le
  have hd2 : 0 < d ^ 2 := by positivity
  have hlogx : 0 ≤ Real.log (cap L * d ^ 2) := Real.log_nonneg hx
  set u := 1 + Real.log (cap L * d ^ 2) with hu_def
  set y := cap k * d ^ 2 with hy_def
  set t := Tier2.Model.threshold1 (cap k) (cap L) with ht_def
  have hu1 : 1 ≤ u := by linarith
  have hu0 : 0 < u := by linarith
  have hy1 : 1 < y := by linarith
  have hlogy : 0 < Real.log y := Real.log_pos hy1
  have ht2 : cap k * t ^ 2 = u - Real.log y := by
    rw [ht_def, Tier2.Model.threshold1_sq hn hnN]
    have hlog : Real.log (cap L / cap k) = Real.log (cap L * d ^ 2) - Real.log y := by
      rw [← Real.log_div (by positivity) (by positivity)]
      congr 1
      rw [hy_def]
      field_simp
    rw [hlog, hu_def]
    field_simp
    ring
  have ht0 : 0 ≤ t := Tier2.Model.threshold1_nonneg _ _
  have hnt : cap k * t ^ 2 ≤ u := by linarith
  have hsn : Real.sqrt (cap k) * t ≤ Real.sqrt u := by
    rw [show Real.sqrt (cap k) * t = Real.sqrt (cap k * t ^ 2) by
      rw [Real.sqrt_mul hn.le, Real.sqrt_sq ht0]]
    exact Real.sqrt_le_sqrt hnt
  have hsy : Real.sqrt y = Real.sqrt (cap k) * d := by
    rw [hy_def, Real.sqrt_mul hn.le, Real.sqrt_sq hd.le]
  set s := y / u with hs_def
  have hs1 : 1 < s := (one_lt_div hu0).2 (by linarith)
  have hys : y = s * u := by rw [hs_def]; field_simp
  have hsy' : Real.sqrt y = Real.sqrt s * Real.sqrt u := by
    rw [hys, Real.sqrt_mul (by linarith)]
  have hsqs : 1 ≤ Real.sqrt s := Real.le_sqrt_of_sq_le (by nlinarith)
  have htd : t ≤ d := by
    have h : Real.sqrt (cap k) * t ≤ Real.sqrt (cap k) * d := by
      calc
        Real.sqrt (cap k) * t ≤ Real.sqrt u := hsn
        _ ≤ Real.sqrt y := Real.sqrt_le_sqrt (by linarith)
        _ = _ := hsy
    exact le_of_mul_le_mul_left h (Real.sqrt_pos.2 hn)
  have hgap : (Real.sqrt s - 1) ^ 2 ≤ cap k * (d - t) ^ 2 := by
    have hA : Real.sqrt u * (Real.sqrt s - 1) ≤ Real.sqrt (cap k) * (d - t) := by
      have he : Real.sqrt (cap k) * (d - t) = Real.sqrt y - Real.sqrt (cap k) * t := by
        rw [hsy]; ring
      rw [he, hsy']
      nlinarith [hsn]
    have hB : 0 ≤ Real.sqrt u * (Real.sqrt s - 1) :=
      mul_nonneg (Real.sqrt_nonneg _) (by linarith)
    have hsq := pow_le_pow_left₀ hB hA 2
    have hu' : Real.sqrt u ^ 2 = u := Real.sq_sqrt hu0.le
    have hn' : Real.sqrt (cap k) ^ 2 = cap k := Real.sq_sqrt hn.le
    calc
      (Real.sqrt s - 1) ^ 2 ≤ u * (Real.sqrt s - 1) ^ 2 := le_mul_of_one_le_left (sq_nonneg _) hu1
      _ = (Real.sqrt u * (Real.sqrt s - 1)) ^ 2 := by rw [mul_pow, hu']
      _ ≤ (Real.sqrt (cap k) * (d - t)) ^ 2 := hsq
      _ = cap k * (d - t) ^ 2 := by rw [mul_pow, hn']
  unfold survivalBound
  rw [← ht_def, ite_eq_left htd]
  unfold bump
  have hexp : Real.exp (-2 * cap k * (d - t) ^ 2) ≤ Real.exp (-2 * (Real.sqrt s - 1) ^ 2) :=
    Real.exp_le_exp.2 (by nlinarith)
  have hcoef : (u / d ^ 2) * s = cap k := by
    rw [hs_def, hy_def]
    field_simp
  calc
    cap k * Real.exp (-2 * cap k * (d - t) ^ 2) ≤
        cap k * Real.exp (-2 * (Real.sqrt s - 1) ^ 2) := mul_le_mul_of_nonneg_left hexp hn.le
    _ = (u / d ^ 2) * (s * Real.exp (-2 * (Real.sqrt s - 1) ^ 2)) := by
      rw [← mul_assoc, hcoef]

/-- The dyadic reduction: below the stopping scale each term is at most its cap,
and past it at most the dyadic term. The sum of caps below the first dyadic
point past the scale cancels the leading one. -/
theorem dyadic_work_sum_le (L : ℕ) {d u : ℝ} (hd : 0 < d) (hu : 1 ≤ u) (hdu : d ^ 2 < u)
    (f : ℕ → ℝ) (hf : ∀ k < L, f k ≤
      if cap k * d ^ 2 ≤ u then cap k else (u / d ^ 2) * bump (cap k * d ^ 2 / u)) :
    1 + ∑ k ∈ range L, f k ≤ (49 / 10) * (u / d ^ 2) := by
  classical
  set b : ℕ → ℝ := fun k =>
    if cap k * d ^ 2 ≤ u then cap k else (u / d ^ 2) * bump (cap k * d ^ 2 / u) with hb
  have hd2 : 0 < d ^ 2 := by positivity
  have hu0 : 0 < u := by linarith
  have hb0 : ∀ k, 0 ≤ b k := by
    intro k
    simp only [hb]
    split_ifs
    · exact (cap_pos k).le
    · exact mul_nonneg (by positivity) (bump_nonneg (by have := cap_pos k; positivity))
  have hex : ∃ k, u < cap k * d ^ 2 := by
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (u / d ^ 2) (by norm_num : (1 : ℝ) < 2)
    exact ⟨n, by simpa [cap] using (div_lt_iff₀ hd2).1 hn⟩
  set K := Nat.find hex with hK
  have hKspec : u < cap K * d ^ 2 := Nat.find_spec hex
  have hKmin : ∀ k < K, cap k * d ^ 2 ≤ u := fun k hk => not_lt.1 (Nat.find_min hex hk)
  have hK0 : K ≠ 0 := by
    intro h0
    rw [h0, cap_zero, one_mul] at hKspec
    linarith
  obtain ⟨K', hK'⟩ := Nat.exists_eq_succ_of_ne_zero hK0
  have hKle : cap K * d ^ 2 ≤ 2 * u := by
    have h := hKmin K' (by omega)
    rw [hK', cap_succ]
    nlinarith
  set s := cap K * d ^ 2 / u with hs_def
  have hs1 : 1 < s := (one_lt_div hu0).2 hKspec
  have hs2 : s ≤ 2 := (div_le_iff₀ hu0).2 (by linarith)
  have hsum1 : ∑ k ∈ range L, f k ≤ ∑ k ∈ range (K + L), b k := by
    calc
      _ ≤ ∑ k ∈ range L, b k := sum_le_sum (fun k hk => hf k (mem_range.1 hk))
      _ ≤ _ := sum_le_sum_of_subset_of_nonneg (range_mono (by omega)) (fun k _ _ => hb0 k)
  rw [sum_range_add] at hsum1
  have hpre : ∑ k ∈ range K, b k = cap K - 1 := by
    have h : ∀ k ∈ range K, b k = cap k := fun k hk => by
      simp only [hb]
      rw [ite_eq_left (hKmin k (mem_range.1 hk))]
    rw [sum_congr rfl h]
    change ∑ k ∈ range K, (2 : ℝ) ^ k = (2 : ℝ) ^ K - 1
    rw [geom_sum_eq (by norm_num : (2 : ℝ) ≠ 1) K]
    norm_num
  have hpost : ∀ j, b (K + j) = (u / d ^ 2) * bump (2 ^ j * s) := by
    intro j
    have hcap : cap (K + j) * d ^ 2 = 2 ^ j * (cap K * d ^ 2) := by
      simp only [cap, pow_add]
      ring
    have hj : (1 : ℝ) ≤ 2 ^ j := one_le_pow₀ (by norm_num)
    have hgt : ¬ cap (K + j) * d ^ 2 ≤ u := by
      rw [hcap]
      nlinarith
    simp only [hb]
    rw [ite_eq_right hgt, hcap, hs_def, mul_div_assoc]
  rw [hpre, sum_congr rfl (fun j _ => hpost j), ← mul_sum] at hsum1
  have hoff := offset_sum_le s hs1 hs2 L
  have hcapK : cap K = (u / d ^ 2) * s := by
    rw [hs_def]
    field_simp
  calc
    1 + ∑ k ∈ range L, f k ≤
        1 + (cap K - 1 + (u / d ^ 2) * ∑ j ∈ range L, bump (2 ^ j * s)) := by linarith
    _ = (u / d ^ 2) * (s + ∑ j ∈ range L, bump (2 ^ j * s)) := by rw [hcapK]; ring
    _ ≤ (u / d ^ 2) * (49 / 10) := mul_le_mul_of_nonneg_left hoff (by positivity)
    _ = _ := by ring

/-- The deterministic sum behind the expected work, with the sharp survival
bound: at most `(49/10)*d⁻²*(1 + log (cap L*d^2))` once `cap L*d^2 ≥ 1`. -/
theorem survival_sum_le (L : ℕ) {d : ℝ} (hd : 0 < d) (hdmax : d ≤ 1 / 2)
    (hx : 1 ≤ cap L * d ^ 2) :
    1 + ∑ k ∈ range L, cap k * survivalBound L k d ≤
      (49 / 10) * (d⁻¹) ^ 2 * (1 + Real.log (cap L * d ^ 2)) := by
  have hlog : 0 ≤ Real.log (cap L * d ^ 2) := Real.log_nonneg hx
  have hu : 1 ≤ 1 + Real.log (cap L * d ^ 2) := by linarith
  have hdu : d ^ 2 < 1 + Real.log (cap L * d ^ 2) := by nlinarith
  have h := dyadic_work_sum_le L hd hu hdu (fun k => cap k * survivalBound L k d) (by
    intro k hk
    split_ifs with hy
    · exact mul_le_of_le_one_right (cap_pos k).le (survivalBound_le_one L k d)
    · exact cap_mul_survivalBound_le L k hk hd hx (lt_of_not_ge hy))
  refine h.trans (le_of_eq ?_)
  rw [div_eq_mul_inv, inv_pow]
  ring

section Probability
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {m : ℕ → Ω → ℝ}

theorem survival_positive (L k : ℕ) {d : ℝ} (ht : HasMeanTails μ m (1 / 2 + d)) :
    μ.real {ω | k < Tier2.Model.stopLevel (fun j => m j ω) L} ≤ survivalBound L k d := by
  unfold survivalBound
  split_ifs with h
  · have hsub : {ω | k < Tier2.Model.stopLevel (fun j => m j ω) L} ⊆
        {ω | d - Tier2.Model.threshold1 (cap k) (cap L) ≤ (1 / 2 + d) - m k ω} := by
      intro ω hω
      have hs := (firstStop_min (fun k L => Tier2.Model.threshold1 (cap k) (cap L))
        (fun j => m j ω) L k hω).2
      have hu := (abs_le.mp hs).2
      simp only [Set.mem_ofPred_eq]
      linarith
    exact (measureReal_mono hsub).trans (ht.lower k _ (sub_nonneg.2 h))
  · exact measureReal_le_one

theorem survival_negative (L k : ℕ) {d : ℝ} (ht : HasMeanTails μ m (1 / 2 - d)) :
    μ.real {ω | k < Tier2.Model.stopLevel (fun j => m j ω) L} ≤ survivalBound L k d := by
  unfold survivalBound
  split_ifs with h
  · have hsub : {ω | k < Tier2.Model.stopLevel (fun j => m j ω) L} ⊆
        {ω | d - Tier2.Model.threshold1 (cap k) (cap L) ≤ m k ω - (1 / 2 - d)} := by
      intro ω hω
      have hs := (firstStop_min (fun k L => Tier2.Model.threshold1 (cap k) (cap L))
        (fun j => m j ω) L k hω).2
      have hl := (abs_le.mp hs).1
      simp only [Set.mem_ofPred_eq]
      linarith
    exact (measureReal_mono hsub).trans (ht.upper k _ (sub_nonneg.2 h))
  · exact measureReal_le_one

theorem expected_work_le_survival (L : ℕ) {d : ℝ} (hm : ∀ k, Measurable (m k))
    (hs : ∀ k, μ.real {ω | k < Tier2.Model.stopLevel (fun j => m j ω) L} ≤
      survivalBound L k d) :
    (∫ ω, Tier2.Model.work (fun k => m k ω) L ∂μ) ≤
      1 + ∑ k ∈ range L, cap k * survivalBound L k d := by
  rw [Tier2.Model.expected_work_survival_identity m hm μ L]
  have h := sum_le_sum (fun k (_ : k ∈ range L) => mul_le_mul_of_nonneg_left (hs k) (cap_pos k).le)
  linarith

/-- The sharper expected-work bound for a coin with mean `1/2 + d`. -/
theorem expected_work_positive (L : ℕ) {d : ℝ} (hd : 0 < d) (hdmax : d ≤ 1 / 2)
    (ht : HasMeanTails μ m (1 / 2 + d)) (hx : 1 ≤ cap L * d ^ 2) :
    (∫ ω, Tier2.Model.work (fun k => m k ω) L ∂μ) ≤
      (49 / 10) * (d⁻¹) ^ 2 * (1 + Real.log (cap L * d ^ 2)) :=
  (expected_work_le_survival L ht.measurable (fun k => survival_positive L k ht)).trans
    (survival_sum_le L hd hdmax hx)

/-- The sharper expected-work bound for a coin with mean `1/2 - d`. -/
theorem expected_work_negative (L : ℕ) {d : ℝ} (hd : 0 < d) (hdmax : d ≤ 1 / 2)
    (ht : HasMeanTails μ m (1 / 2 - d)) (hx : 1 ≤ cap L * d ^ 2) :
    (∫ ω, Tier2.Model.work (fun k => m k ω) L ∂μ) ≤
      (49 / 10) * (d⁻¹) ^ 2 * (1 + Real.log (cap L * d ^ 2)) :=
  (expected_work_le_survival L ht.measurable (fun k => survival_negative L k ht)).trans
    (survival_sum_le L hd hdmax hx)

end Probability

end ThresholdHC.UpperWork
