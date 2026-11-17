import SharpBarrier
import SharpFisher
import SharpPrefixCost

/-! The local barrier comparison summed over the original adaptive
transcript. The proof uses the centered score and the biased Wald identity. -/
noncomputable section
namespace ThresholdHC.SharpRMS
open Proofs Tier3 Tier5 Real Set

private theorem barrier_artanh (s : ℝ) (hs : 0 < s) (hs' : s < 1) (k : ℕ) :
    artanh (barrierPosterior s k) = k*artanh s := by
  induction k with
  | zero => simp [barrierPosterior]
  | succ k ih =>
    let x := barrierPosterior s k
    have hx := barrier_posterior_bounds s hs hs' k
    have hx₀ : 0 ≤ x := hx.1
    have hx₁ : x < 1 := hx.2.1
    have hnext := barrier_posterior_bounds s hs hs' (k+1)
    have hn := artanh_eq_half_log (show barrierPosterior s (k+1) ∈ Icc (-1:ℝ) 1 from
      ⟨by linarith [hnext.1],hnext.2.1.le⟩)
    rw [hn]
    change 1/2*log ((1+(x+s)/(1+s*x))/(1-(x+s)/(1+s*x))) = _
    have den : 0 < 1+s*x := by positivity
    have dm : 0 < 1-(x+s)/(1+s*x) := by change 0 < 1-barrierPosterior s (k+1); linarith [hnext.2.1]
    have eqr : (1+(x+s)/(1+s*x))/(1-(x+s)/(1+s*x)) = (1+x)/(1-x)*((1+s)/(1-s)) := by
      apply (div_eq_iff dm.ne').mpr
      field_simp [show 1-x ≠ 0 by linarith,show 1-s ≠ 0 by linarith,den.ne']
      ring
    have hu : 0 < (1+x)/(1-x) := div_pos (by linarith) (by linarith)
    have hv : 0 < (1+s)/(1-s) := div_pos (by linarith) (by linarith)
    rw [eqr,log_mul hu.ne' hv.ne',mul_add,← artanh_eq_half_log (show x ∈ Icc (-1:ℝ) 1 from ⟨by linarith,hx₁.le⟩),
      ← artanh_eq_half_log (show s ∈ Icc (-1:ℝ) 1 from ⟨by linarith,hs'.le⟩)]
    change artanh (barrierPosterior s k) + artanh s = _
    rw [ih,Nat.cast_succ]
    ring

private theorem net_integer {m n : ℕ} (pol : List Bool → Option (Fin m)) (w : Prefix n) (i : Fin m) :
    ∃ N : ℤ, netCount pol w i = N := by
  let y := fun o : Option Bool => match o with
      | none => (0:ℤ) | some true => 1 | some false => -1
  refine ⟨∑ j, if pol (histBefore w j) = some i then y (w j) else 0, ?_⟩
  rw [Int.cast_sum]
  apply Finset.sum_congr rfl
  intro j _
  by_cases h : pol (histBefore w j) = some i
  · simp only [h,↓reduceIte]
    cases w j with
    | none => norm_num [y,bitValue]
    | some b => cases b <;> norm_num [y,bitValue]
  · simp [h]

private theorem reachable {m n : ℕ} (pol : List Bool → Option (Fin m)) (w : Prefix n) (i : Fin m)
    (s : ℝ) (hs : 0 < s) (hs' : s < 1)
    (hw : transcriptLaw pol (fun _ => s/2) (fun _ => 1/2) w ≠ 0) :
    ∃ (k : ℕ) (e : ℝ), (e = -1 ∨ e = 1) ∧ netCount pol w i = e*k ∧
      posterior pol w (fun _ => s/2) i = e*barrierPosterior s k := by
  let z := posterior pol w (fun _ => s/2) i
  obtain ⟨hz,hA⟩ := posterior_odds pol w s hs hs' hw i
  have hzI : z ∈ Ioo (-1:ℝ) 1 := abs_lt.mp hz
  obtain ⟨N,hN⟩ := net_integer pol w i
  obtain ⟨k,e,he,hv⟩ : ∃ (k : ℕ) (e : ℝ), (e = -1 ∨ e = 1) ∧ (N:ℝ) = e*k := by
    cases N with
    | ofNat k => exact ⟨k,1,Or.inr rfl,by simp⟩
    | negSucc k => exact ⟨k+1,-1,Or.inl rfl,by simp⟩
  refine ⟨k,e,he,hN.trans hv,?_⟩
  have hx := barrier_posterior_bounds s hs hs' k
  have hxi : barrierPosterior s k ∈ Ioo (-1:ℝ) 1 := ⟨by linarith [hx.1],hx.2.1⟩
  change z = _
  rw [← tanh_artanh hzI]
  change artanh z = _ at hA
  rw [hA,hN,hv,mul_assoc,← barrier_artanh s hs hs']
  rcases he with rfl | rfl <;> simp [tanh_artanh hxi]

/-- For each admissible reciprocal barrier price, the Fisher information of
an arbitrary finite prefix is paid for by expected work at the same bias. -/
theorem adaptive_fisher_price {n : ℕ} (pol : List Bool → Option ℕ) (s t P : ℝ)
    (hs : 0 < s) (hs' : s < 1) (ht : |t| < 1) (hP : P ≤ 1)
    (hexit : admissibleExitPrice s |t| P) :
    let Q := fun (y : ℝ) (w : Prefix n) => creationLaw pol (fun _=>s/2) (fun _=>(1+y)/2) w
    P*(∑ w, (deriv (fun y => Q y w) t)^2/Q t w) ≤ s^2*∑ w, Q t w*workOf w := by
  let cp := capPolicy (coinCap n pol) pol
  let Q := fun (y : ℝ) (w : Prefix n) => creationLaw pol (fun _=>s/2) (fun _=>(1+y)/2) w
  let z := fun w : Prefix n => posterior cp w (fun _=>s/2)
  let M := fun w : Prefix n => ∑ i, ((z w i+t)/(1+t*z w i))*netCount cp w i
  let S := fun w : Prefix n => tiltedScore z t w
  let J := fun w : Prefix n => ∑ i, (z w i)^2/(1+t*z w i)^2
  have htI : t ∈ Ioo (-1:ℝ) 1 := abs_lt.mp ht
  let C := if 0 ≤ t then barrierOffset s t P else -barrierOffset s (-t) P
  have ids := creation_score_identities (n := n) pol (fun _=>s/2)
    (fun _=>⟨by linarith,by linarith⟩) t htI
  have wald := biased_wald (n := n) cp s t hs.le hs'.le (abs_lt.mpr htI)
  change (∑ w, Q t w*M w) = s*∑ w, Q t w*workOf w at wald
  obtain ⟨center,diagonal⟩ := ids
  change ∑ w, Q t w*S w = 0 at center
  change (∑ w, (deriv (fun y => Q y w) t)^2/Q t w) = ∑ w, Q t w*J w at diagonal
  change P*(∑ w, (deriv (fun y => Q y w) t)^2/Q t w) ≤ _
  rw [diagonal]
  have word (w : Prefix n) : P*(Q t w*J w) ≤ s*(Q t w*M w) - C*(Q t w*S w) := by
    have hq : 0 ≤ Q t w := (creationLaw_total n pol _ _ (fun _=>⟨by linarith,by linarith⟩)
      (fun _=>⟨by linarith [htI.1],by linarith [htI.2]⟩)).1 w
    by_cases he : Q t w = 0
    · simp [he]
    have hw : transcriptLaw cp (fun _=>s/2) (fun _=>1/2) w ≠ 0 := by
      intro hzero
      apply he
      have htilt := creation_tilt pol w (fun _=>s/2) (fun _=>t) (fun _=>⟨by linarith,by linarith⟩)
      change creationLaw pol (fun _=>s/2) (fun _=>1/2) w = 0 at hzero
      simpa only [hzero,zero_mul] using htilt
    have each (i) : P*((z w i)^2/(1+t*z w i)^2) ≤
        s*(((z w i+t)/(1+t*z w i))*netCount cp w i)-C*(z w i/(1+t*z w i)) := by
      obtain ⟨k,e,he,hK,hZ⟩ := reachable cp w i s hs hs' hw
      change z w i = _ at hZ
      by_cases hpos : 0 ≤ t
      · rw [abs_of_nonneg hpos] at hexit
        have h := barrier_leaf_price s t P hs hs' hpos htI.2 hP hexit k e he
        rw [← hZ,← hK] at h
        simp only [C,hpos,↓reduceIte]
        convert h using 1 <;> ring
      · rw [abs_of_neg (lt_of_not_ge hpos)] at hexit
        have he' : -e = -1 ∨ -e = 1 := by rcases he with rfl | rfl <;> norm_num
        have h := barrier_leaf_price s (-t) P hs hs' (by linarith) (by linarith [htI.1]) hP hexit k (-e) he'
        simp only [neg_mul,← hZ,← hK] at h
        simp only [C,hpos,↓reduceIte]
        convert h using 1 <;> ring
    have hp := Finset.sum_le_sum (s := Finset.univ) (fun i _ => each i)
    simp only [Finset.sum_sub_distrib,← Finset.mul_sum] at hp
    change P*J w ≤ s*M w-C*S w at hp
    linarith only [mul_le_mul_of_nonneg_left hp hq]
  have agg := Finset.sum_le_sum (s := Finset.univ) (fun w _ => word w)
  simp only [Finset.sum_sub_distrib,← Finset.mul_sum,wald,center,mul_zero,sub_zero] at agg
  change _ ≤ s^2*∑ w, Q t w*workOf w
  linarith only [agg]

end ThresholdHC.SharpRMS
