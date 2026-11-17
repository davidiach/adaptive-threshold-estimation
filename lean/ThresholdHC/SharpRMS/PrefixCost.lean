import ThresholdHC.SharpRMS.Information
import ThresholdHC.SharpRMS.Transcript
import ThresholdHC.Tier3.StoppingBase

/-! Reverse KL at a bounded adaptive horizon, summed over opposite alternatives. -/
noncomputable section
namespace ThresholdHC.SharpRMS
open Proofs Tier3 Tier5 Real

theorem posterior_odds {m n : ℕ} (pol : List Bool → Option (Fin m))
    (w : Prefix n) (s : ℝ) (hs : 0 < s) (hs' : s < 1)
    (hw : transcriptLaw pol (fun _ => s/2) (fun _ => 1/2) w ≠ 0) (i : Fin m) :
    |posterior pol w (fun _ => s/2) i| < 1 ∧
    artanh (posterior pol w (fun _ => s/2) i) = netCount pol w i * artanh s := by
  let p := (1+s)/2
  let q := (1-s)/2
  have hp : 0 < p := by dsimp [p]; linarith
  have hq : 0 < q := by dsimp [q]; linarith
  have hpq : 1-p=q := by dsimp [p,q]; ring
  have hqp : 1-q=p := by dsimp [p,q]; ring
  let a := fun (k : Fin n) (v : ℝ) =>
    if pol (histBefore w k) = some i then obsProb v (w k) else 1
  have valid (k : Fin n) (h : pol (histBefore w k) = some i) : w k ≠ none := by
    intro he
    exact hw (transcriptLaw_zero_of_invalid _ _ _ w k (by simp [he,h]))
  have apos (k : Fin n) : 0 < a k p ∧ 0 < a k q := by
    by_cases h : pol (histBefore w k) = some i
    · obtain ⟨b,hb⟩ := Option.ne_none_iff_exists'.mp (valid k h)
      cases b <;> simp [a,h,hb,obsProb,hpq,hqp,hp,hq]
    · simp [a,h]
  let A := ∏ k, a k p
  let B := ∏ k, a k q
  have hA : 0 < A := Finset.prod_pos fun k _ => (apos k).1
  have hB : 0 < B := Finset.prod_pos fun k _ => (apos k).2
  let z := (A-B)/(A+B)
  have hpost : posterior pol w (fun _ => s/2) i = z := by
    simp only [posterior,coinLike]
    rw [show (1/2:ℝ)+s/2 = p by dsimp [p]; ring, show (1/2:ℝ)-s/2 = q by dsimp [q]; ring]
  rw [hpost]
  have hab := add_pos hA hB
  have hz : |z| < 1 := by
    rw [abs_lt]
    constructor
    · apply (lt_div_iff₀ hab).mpr
      linarith
    · apply (div_lt_iff₀ hab).mpr
      linarith
  refine ⟨hz, ?_⟩
  have ratio : (1+z)/(1-z) = A/B := by
    have hplus : 1+z = 2*A/(A+B) := by dsimp [z]; field_simp; ring
    have hminus : 1-z = 2*B/(A+B) := by dsimp [z]; field_simp; ring
    rw [hplus,hminus,div_div_div_cancel_right₀ hab.ne']
    field_simp
  have unitratio : (1+s)/(1-s) = p/q := by dsimp [p,q]; rw [div_div_div_cancel_right₀ (by norm_num : (2:ℝ) ≠ 0)]
  rw [artanh_eq_half_log ⟨(abs_lt.mp hz).1.le,(abs_lt.mp hz).2.le⟩, ratio,
    Real.log_div hA.ne' hB.ne', artanh_eq_half_log (show s ∈ Set.Icc (-1) 1 from ⟨by linarith,hs'.le⟩),
    unitratio, Real.log_div hp.ne' hq.ne']
  have step (k : Fin n) : log (a k p) - log (a k q) =
      (if pol (histBefore w k) = some i then bitValue (w k) else 0) * (log p-log q) := by
    by_cases h : pol (histBefore w k) = some i
    · obtain ⟨b,hb⟩ := Option.ne_none_iff_exists'.mp (valid k h)
      cases b <;> simp [a,h,hb,obsProb,bitValue,hpq,hqp]
    · simp [a,h]
  dsimp only [A,B]
  rw [Real.log_prod (fun k _ => (apos k).1.ne'), Real.log_prod (fun k _ => (apos k).2.ne'),
    ← Finset.sum_sub_distrib]
  simp_rw [step]
  rw [← Finset.sum_mul,netCount]
  ring

/-- Sum of the two directed discrete divergences from the fair transcript law.
A zero-mass word contributes zero with Lean's total real logarithm. -/
def pairedCost {n : ℕ} (p q r : Prefix n → ℝ) : ℝ :=
  ∑ w, p w * (log (p w/q w) + log (p w/r w))

theorem transcript_cost {m n : ℕ} (pol : List Bool → Option (Fin m))
    (s : ℝ) (hs : 0 < s) (hs' : s < 1) :
    pairedCost (n := n) (transcriptLaw pol (fun _ => s/2) (fun _ => 1/2))
      (transcriptLaw pol (fun _ => s/2) (fun _ => (1+7/10)/2))
      (transcriptLaw pol (fun _ => s/2) (fun _ => (1+ -(7/10))/2)) ≤
      (7/10:ℝ)^2 * (artanh s) * s *
        ∑ w : Prefix n, transcriptLaw pol (fun _ => s/2) (fun _ => 1/2) w * workOf w := by
  let d := fun _ : Fin m => s/2
  let P := transcriptLaw (n := n) pol d (fun _ => 1/2)
  let Q := fun t : ℝ => transcriptLaw (n := n) pol d (fun _ => (1+t)/2)
  let u := (7/10:ℝ)^2
  change (∑ w, P w * (log (P w/Q (7/10) w) + log (P w/Q (-(7/10)) w))) ≤ _
  have hden : ∀ i, 0 ≤ d i ∧ d i ≤ 1/2 := fun _ => ⟨by dsimp [d]; linarith, by dsimp [d]; linarith⟩
  have hn (w : Prefix n) : 0 ≤ P w :=
    (transcript_law_total m n pol d _ hden (fun _ => ⟨by norm_num,by norm_num⟩)).1 w
  calc
    _ ≤ ∑ w, P w * (u * artanh s * ∑ i, posterior pol w d i * netCount pol w i) := by
      apply Finset.sum_le_sum
      intro w _
      by_cases hz : P w = 0
      · simp [hz]
      apply mul_le_mul_of_nonneg_left _ (hn w)
      let Z := posterior pol w d
      have ho := posterior_odds pol w s hs hs' hz
      have pos (t : ℝ) (ht : |t| < 1) (i : Fin m) : 0 < 1+t*Z i := by
        have hh : |t*Z i| < 1 := by
          rw [abs_mul]
          exact (mul_le_mul_of_nonneg_left (ho i).1.le (abs_nonneg t)).trans_lt (by simpa using ht)
        linarith [(abs_lt.mp hh).1]
      have logQ (t : ℝ) (ht : |t| < 1) : log (P w / Q t w) = -∑ i, log (1+t*Z i) := by
        have h := transcript_tilt pol w d (fun _ => t) hden
        change Q t w = P w * ∏ i, (1+t*Z i) at h
        rw [h, Real.log_div hz (mul_ne_zero hz (Finset.prod_ne_zero_iff.mpr fun i _ => (pos t ht i).ne')),
          Real.log_mul hz (Finset.prod_ne_zero_iff.mpr fun i _ => (pos t ht i).ne'),
          Real.log_prod (fun i _ => (pos t ht i).ne')]
        ring
      rw [logQ _ (by norm_num), logQ _ (by norm_num), ← neg_add, ← Finset.sum_add_distrib,
        ← Finset.sum_neg_distrib, Finset.mul_sum]
      apply Finset.sum_le_sum
      intro i _
      rw [← Real.log_mul (pos (7/10) (by norm_num) i).ne' (pos (-(7/10)) (by norm_num) i).ne',
        show (1+7/10*Z i)*(1+ -(7/10)*Z i) = 1-u*(Z i)^2 by dsimp [u]; ring]
      have hl := paired_log_cost u (Z i) (by norm_num [u]) (by norm_num [u]) (ho i).1
      rw [(ho i).2] at hl
      convert hl using 1
      ring
    _ = _ := by
      simp_rw [mul_left_comm (P _) (u*artanh s), ← Finset.mul_sum]
      change u*artanh s*(∑ w : Prefix n, transcriptLaw pol (fun _=>s/2) (fun _=>1/2) w * _) = _
      rw [transcript_wald pol s hs.le hs'.le]
      dsimp [u]
      ring

/-- At every finite horizon and with countably many available coin labels, the
actual paired relative entropy is at most twice the three-bias cutoff when
the fair-law expected work is at most B. -/
theorem creation_paired_cost {n : ℕ} (pol : List Bool → Option ℕ) (s B : ℝ)
    (hs : 0 < s) (hs' : s ≤ 2/5) (hB : s^2*B = 4)
    (hw : (∑ w : Prefix n, creationLaw pol (fun _ => s/2) (fun _ => 1/2) w * workOf w) ≤ B) :
    pairedCost (n := n) (creationLaw pol (fun _ => s/2) (fun _ => 1/2))
      (creationLaw pol (fun _ => s/2) (fun _ => (1+7/10)/2))
      (creationLaw pol (fun _ => s/2) (fun _ => (1+ -(7/10))/2)) ≤ 2*3283/3150 := by
  have h := transcript_cost (n := n) (capPolicy (coinCap n pol) pol) s hs (by linarith)
  have hnonneg := artanh_nonneg hs.le
  refine h.trans ((mul_le_mul_of_nonneg_left hw (by positivity)).trans ?_)
  have hp := small_bias_price s hs hs'
  rw [div_le_iff₀ hs] at hp
  have hsB : s*B = 4/s := by apply (eq_div_iff hs.ne').2; nlinarith only [hB]
  rw [mul_assoc _ s B, hsB]
  field_simp
  linarith

end ThresholdHC.SharpRMS
