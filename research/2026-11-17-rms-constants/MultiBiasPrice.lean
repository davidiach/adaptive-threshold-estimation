import MultiBiasData
import LargeBudgetTranscript

noncomputable section
namespace ThresholdHC.SharpRMS.MultiBias
open Real LargeBudget

def price (B : ℝ) := -B*∑ i, log (1-4*(bias i)^2/B)

def weightSum := tilt+2*∑ i, slope i

theorem price_25 : price 25= -(25*∑ i, log (cut i)) := by simp [price,cut]

theorem charge_sum (s B : ℝ) (hB : 0<B) (hcrit : s^2*B=4) :
    (∑ i, charge s (bias i))*B=price B := by
  have eq (i) : (bias i)^2*s^2=4*(bias i)^2/B := (eq_div_iff hB.ne').2 (by rw [mul_assoc,hcrit]; ring)
  simp only [charge,eq,price,Finset.sum_neg_distrib]
  ring

theorem price_decreases (N B : ℝ) (hn : 25≤N) (hb : N≤B) : price B ≤ price N := by
  have per (i : Fin 5) : N*log (1-4*(bias i)^2/N) ≤ B*log (1-4*(bias i)^2/B) := by
    have h : 4*(bias i)^2<N := by linarith [(params i).2.1]
    exact log_price_mono (4*(bias i)^2) (by have := (params i).1; positivity) h (h.trans_le hb) hb
  have h := Finset.sum_le_sum (s:=Finset.univ) (fun i _ => per i)
  simp only [←Finset.mul_sum] at h
  unfold price
  linarith only [h]

abbrev radius100 : ℝ := 17807955/100000000

/-- The extra information allowance saved at B=100, evaluated by rational arithmetic. -/
theorem gain_100 : weightSum*(4*radius100^2-target)+price 100≤price 25 := by
  let δ := weightSum*(4*radius100^2-target)/25
  let d := fun B : ℝ => ∏ i : Fin 5, (1-4*(bias i)^2/B)
  have dp (B : ℝ) (hb : 25≤B) (i : Fin 5) : 0<1-4*(bias i)^2/B := by
    apply sub_pos.mpr ((div_lt_one (by linarith : 0<B)).2 _)
    linarith [(params i).2.1]
  have dpos B hb : 0<d B := Finset.prod_pos fun i _ => dp B hb i
  have logd B hb : log (d B)=∑ i, log (1-4*(bias i)^2/B) := log_prod (fun i _ => (dp B hb i).ne')
  have hz : 0≤δ ∧ δ≤1 := by norm_num [δ,weightSum,Fin.sum_univ_succ,slope]
  have ex : exp δ ≤ (d 100)^4/d 25 := by
    apply (Real.exp_bound' hz.1 hz.2 (n:=8) (by decide)).trans
    norm_num [δ,weightSum,Fin.sum_univ_succ,slope,d,Fin.prod_univ_succ,bias,Finset.sum_range_succ,Nat.factorial]
  have h := log_le_log (exp_pos _) ex
  rw [log_exp,log_div (pow_pos (dpos 100 (by norm_num)) 4).ne' (dpos 25 (by norm_num)).ne',log_pow,
    logd 100 (by norm_num),logd 25 (by norm_num)] at h
  simp only [Nat.cast_ofNat] at h
  unfold price
  dsimp only [δ] at h
  linarith only [h]

end ThresholdHC.SharpRMS.MultiBias
