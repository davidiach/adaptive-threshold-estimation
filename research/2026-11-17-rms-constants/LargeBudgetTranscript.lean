import LargeBudgetInformation
import SharpPrefixCost
import SharpSimulation

/-! A fresh observation attains the largest summed reverse KL per expected
flip under the fair law, uniformly over adaptive prefixes. -/
noncomputable section
namespace ThresholdHC.SharpRMS.LargeBudget
open Real Proofs Tier3 Tier5 Set

def charge (s t : ℝ) := -log (1-t^2*s^2)

private theorem integer_net {m n : ℕ} (pol : List Bool → Option (Fin m)) (w : Prefix n) (i : Fin m) :
    ∃ k : ℤ, netCount pol w i = k := by
  let b : Option Bool → ℤ := fun o => match o with
    | none => 0 | some true => 1 | some false => -1
  refine ⟨∑ j, if pol (histBefore w j)=some i then b (w j) else 0,?_⟩
  rw [Int.cast_sum]
  apply Finset.sum_congr rfl
  intro j _
  by_cases e : pol (histBefore w j)=some i
  · simp only [e,↓reduceIte]
    cases w j with
    | none => norm_num [b,bitValue]
    | some y => cases y <;> norm_num [b,bitValue]
  · simp [e]

private theorem wald_leaf (s t z : ℝ) (hs : 0<s) (hs' : s<1) (ht : t^2 ≤ 2/3)
    (hz : |z|<1) (k : ℤ) (hk : artanh z=k*artanh s) :
    -log (1-t^2*z^2) ≤ charge s t/(s*artanh s)*(z*artanh z) := by
  have iz : z ∈ Ioo (-1:ℝ) 1 := abs_lt.mp hz
  have repr : z=tanh ((k:ℝ)*artanh s) := by rw [←hk,tanh_artanh iz]
  by_cases zero : k=0
  · simp [repr,zero]
  have sep := posterior_lattice_gap s hs hs' k zero
  rw [←repr] at sep
  have pz : |z|∈Ioo (0:ℝ) 1 := ⟨hs.trans_le sep,hz⟩
  have h := log_wald_ratio (t^2) (sq_nonneg _) ht ⟨hs,hs'⟩ pz sep
  have den : 0 < |z| * artanh |z| := mul_pos pz.1 (artanh_pos pz)
  have odd : |z| * artanh |z|=z*artanh z := by
    rcases le_total 0 z with h | h
    · rw [abs_of_nonneg h]
    · have neg : artanh (-z) = -artanh z := by
        conv_lhs => rw [←tanh_artanh iz,←tanh_neg,artanh_tanh]
      rw [abs_of_nonpos h,neg]; ring
  dsimp only at h
  rw [div_le_iff₀ den,sq_abs,odd] at h
  exact h

/-- Sum of the reverse divergences from bias zero to ±t. The coefficient is
exact for one fresh flip, even at a finite source bias. -/
theorem adaptive_reverse_cost {n : ℕ} (pol : List Bool → Option ℕ) (s t : ℝ)
    (hs : 0<s) (hs' : s<1) (ht : t^2≤2/3) :
    let Q := fun a : ℝ => creationLaw (n:=n) pol (fun _ => s/2) (fun _ => (1+a)/2)
    pairedCost (Q 0) (Q t) (Q (-t)) ≤ charge s t * ∑ w, Q 0 w*workOf w := by
  let m := coinCap n pol
  let pol' := capPolicy m pol
  let d := fun _ : Fin m => s/2
  let P := transcriptLaw (n:=n) pol' d (fun _ => 1/2)
  let Q := fun a : ℝ => transcriptLaw (n:=n) pol' d (fun _ => (1+a)/2)
  let c := charge s t/(s*artanh s)
  have fair : Q 0=P := by dsimp [Q,P]; norm_num
  change pairedCost (Q 0) (Q t) (Q (-t)) ≤ charge s t * ∑ w, Q 0 w*workOf w
  rw [fair]
  have td : |t|<1 := abs_lt.mpr ⟨by nlinarith [sq_nonneg (t+1)],by nlinarith [sq_nonneg (t-1)]⟩
  have hd : ∀ i, 0≤d i ∧ d i≤1/2 := fun _ => ⟨by dsimp [d]; linarith,by dsimp [d]; linarith⟩
  have hn (w : Prefix n) : 0≤P w := (transcript_law_total m n pol' d _ hd (fun _ => by norm_num)).1 w
  calc
    _ ≤ ∑ w, P w*(c*artanh s*∑ i, posterior pol' w d i*netCount pol' w i) := by
      apply Finset.sum_le_sum
      intro w _
      by_cases hz : P w=0
      · simp [hz]
      apply mul_le_mul_of_nonneg_left _ (hn w)
      let Z := posterior pol' w d
      have ho := posterior_odds pol' w s hs hs' hz
      have pos (a : ℝ) (ha : |a|<1) (i : Fin m) : 0<1+a*Z i := by
        have hab : |a*Z i|<1 := by
          rw [abs_mul]
          exact (mul_le_mul_of_nonneg_left (ho i).1.le (abs_nonneg a)).trans_lt (by simpa using ha)
        linarith [(abs_lt.mp hab).1]
      have logQ (a : ℝ) (ha : |a|<1) : log (P w/Q a w) = -∑ i, log (1+a*Z i) := by
        have h := transcript_tilt pol' w d (fun _ => a) hd
        change Q a w = P w * ∏ i, (1+a*Z i) at h
        have nz := Finset.prod_ne_zero_iff.mpr (fun i (_ : i∈(Finset.univ : Finset (Fin m))) => (pos a ha i).ne')
        rw [h,log_div hz (mul_ne_zero hz nz),log_mul hz nz,log_prod (fun i _ => (pos a ha i).ne')]
        ring
      have tm : |-t| < 1 := by simpa using td
      rw [logQ _ td,logQ _ tm,←neg_add,←Finset.sum_add_distrib,←Finset.sum_neg_distrib,Finset.mul_sum]
      apply Finset.sum_le_sum
      intro i _
      rw [←log_mul (pos t td i).ne' (pos (-t) tm i).ne',show (1+t*Z i)*(1+ -t*Z i)=1-t^2*(Z i)^2 by ring]
      obtain ⟨k,hk⟩ := integer_net pol' w i
      have odds := (ho i).2
      have h := wald_leaf s t (Z i) hs hs' ht (ho i).1 k (odds.trans (by rw [hk]))
      change _ ≤ c*(Z i*artanh (Z i)) at h
      rw [show artanh (Z i)=netCount pol' w i*artanh s from odds] at h
      convert h using 1
      ring
    _ = _ := by
      simp_rw [mul_left_comm (P _) (c*artanh s),←Finset.mul_sum]
      change c*artanh s*(∑ w : Prefix n, transcriptLaw pol' (fun _ => s/2) (fun _ => 1/2) w * _) = _
      rw [transcript_wald pol' s hs.le hs'.le]
      dsimp only [c]
      field_simp [hs.ne',(artanh_pos ⟨hs,hs'⟩).ne']
      rfl

end ThresholdHC.SharpRMS.LargeBudget
