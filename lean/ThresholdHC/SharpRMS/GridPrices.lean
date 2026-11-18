import ThresholdHC.SharpRMS.GridArithmetic
import ThresholdHC.SharpRMS.Rectangles

/-! Relate the integer upward rounding to each real exit price. -/
namespace ThresholdHC.SharpRMS.Window

private theorem parts_spec (u w : ℕ) (hu : 0 < u) (hw : 0 < w) (k : ℕ) :
    0 < (posteriorParts u w k).2 ∧
    barrierPosterior ((u:ℝ)/w) k = ((posteriorParts u w k).1:ℝ)/(posteriorParts u w k).2 := by
  induction k with
  | zero => simp [posteriorParts,barrierPosterior]
  | succ k ih =>
    obtain ⟨hq,hx⟩ := ih
    generalize eq : posteriorParts u w k = z at hq hx ⊢
    obtain ⟨p,q⟩ := z
    simp only [posteriorParts,eq,barrierPosterior,Nat.cast_add,Nat.cast_mul,hx]
    refine ⟨by positivity,?_⟩
    field_simp

private theorem weight_spec (i : ℕ) (hi : i < bins) :
    (weight (i+1):ℝ) = (bins:ℝ)^2-(i:ℝ)^2 := by
  simp only [weight,Nat.add_sub_cancel]
  rw [Nat.cast_sub (Nat.pow_le_pow_left hi.le 2)]
  push_cast
  rfl

private theorem sign_bound (u w i : ℕ) (hu : 0 < u) (_hw : 0 < w) (hi : i < bins) :
    (1-((i:ℝ)/bins)^2)/((u:ℝ)/w)^2 ≤ (signHeight (i+1) u w:ℝ)/scale := by
  have npos : 0 < bins := by decide
  have spos : 0 < scale := by decide
  have h := roundUp_covers (scale*weight (i+1)*w^2) (bins^2*u^2) (by positivity)
  change _ ≤ (signHeight (i+1) u w:ℝ) at h
  push_cast at h
  rw [weight_spec i hi] at h
  field_simp at h ⊢
  linarith only [h]

private theorem last_tail (u w : ℕ) : exitHeight bins u w 20 = signHeight bins u w := by
  unfold exitHeight makeBarrier roundedExit
  generalize posteriorParts u w 20 = z
  obtain ⟨p,q⟩ := z
  simp

private theorem exit_bound (u w i k : ℕ) (hu : 0 < u) (uw : u < w)
    (hi : i+1 < bins) (hk : 0 < k) :
    let s := (u:ℝ)/w
    let l := (i:ℝ)/bins
    let b := ((i:ℝ)+1)/bins
    let y := if k=20 then 1 else barrierPosterior s k
    (1-l^2)^2*(1+y/s) ≤ ((exitHeight (i+1) u w k:ℝ)/scale)*
      (exitFactor s b y*exitLength s b k) := by
  let p := (posteriorParts u w k).1
  let q := (posteriorParts u w k).2
  let c := k*q*u-p*w
  let d := p*u
  let a := if k=20 then 1 else p
  let e := if k=20 then 1 else q
  let n := bins
  let j := i+1
  let s := (u:ℝ)/w
  let x := barrierPosterior s k
  let y := (a:ℝ)/e
  let b := (j:ℝ)/n
  let l := (i:ℝ)/n
  have hw := hu.trans uw
  have eq := parts_spec u w hu hw k
  have hq : 0<q := eq.1
  have hx : x=(p:ℝ)/q := eq.2
  have hs : 0<s := by dsimp [s]; positivity
  have h1 : s<1 := by dsimp [s]; exact_mod_cast (div_lt_one (show (0:ℝ)<w by exact_mod_cast hw)).mpr (by exact_mod_cast uw)
  have post := barrier_posterior_bounds s hs h1 k
  have hxpos : 0<x := hs.trans_le (post.2.2.2 hk)
  have hp : 0<p := by
    by_contra! hh
    have hz : p=0 := by omega
    simp [hx,hz] at hxpos
  have hd : 0<d := Nat.mul_pos hp hu
  have he : 0<e := by dsimp [e]; split_ifs <;> omega
  have yeq : y = if k=20 then 1 else x := by dsimp [y,a,e]; split_ifs <;> simp_all
  have y1 : y ≤ 1 := by rw [yeq]; split <;> linarith [post.2.1]
  have y0 : 0 ≤ y := by dsimp [y]; positivity
  have nn : 0<n := by decide
  have ss : 0<scale := by decide
  have b0 : 0≤b := by dsimp [b]; positivity
  have b1 : b<1 := (div_lt_one (by exact_mod_cast nn)).mpr (by exact_mod_cast hi)
  have kk : p*w ≤ k*q*u := by
    have zz := post.2.2.1
    change x ≤ k*s at zz
    rw [hx] at zz
    dsimp [s] at zz
    field_simp at zz
    exact_mod_cast (by linarith only [zz] : (p:ℝ)*w ≤ k*q*u)
  have cr : (c:ℝ) = k*q*u-p*w := by simp [c,Nat.cast_sub kk]
  have dr : (d:ℝ) = p*u := by simp [d]
  have sl : (k:ℝ)/x-1/s = (c:ℝ)/d := by
    rw [hx,cr,dr]
    dsimp [s]
    field_simp
  have positive : 0 < exitLength s b k := by
    have low := exit_length_mono s b hs h1 b0 b1.le 1 k (by decide) hk
    have one : exitLength s b 1 = 2 := by simp [exitLength,barrierPosterior]; ring
    linarith
  have yden : j*a < n*e := by
    have z : b*y<1 := (mul_le_mul_of_nonneg_left y1 b0).trans_lt (by simpa using b1)
    dsimp [b,y] at z
    field_simp at z
    exact_mod_cast (by linarith only [z] : (j:ℝ)*a < n*e)
  have lden : j*c < n*d*(k+1) := by
    change 0 < (k:ℝ)+1-b*((k:ℝ)/x-1/s) at positive
    rw [sl] at positive
    dsimp [b] at positive
    field_simp at positive
    exact_mod_cast (by linarith only [positive] : (j:ℝ)*c < n*d*((k:ℝ)+1))
  let top := scale*(e*u+a*w)*w*d*(weight j)^2
  let den := n*u*(n*e-j*a)*(n*w+j*u)*(n*d*(k+1)-j*c)
  have hden : 0 < den := by
    dsimp [den]
    exact Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (Nat.mul_pos nn hu) (Nat.sub_pos_of_lt yden))
      (show 0 < n*w+j*u by positivity)) (Nat.sub_pos_of_lt lden)
  have eh : exitHeight j u w k = roundUp top den := by
    have identity : exitHeight j u w k = if den=0 then signHeight j u w else roundUp top den := by
      dsimp only [den,top,n,a,e,c,d,p,q,exitHeight,roundedExit,makeBarrier]
      by_cases h : k=20 <;> simp [h]
    rw [identity,ite_eq_right hden.ne']
  have rounded := roundUp_covers top den hden
  rw [← eh] at rounded
  have raw := (div_le_iff₀ (by exact_mod_cast hden)).mp rounded
  dsimp [top,den] at raw
  simp only [Nat.cast_mul,Nat.cast_pow,Nat.cast_add,Nat.cast_one,Nat.cast_sub yden.le,
    Nat.cast_sub lden.le] at raw
  change (1-l^2)^2*(1+(if k=20 then 1 else x)/s) ≤ ((exitHeight j u w k:ℝ)/scale)*
    (exitFactor s (((i:ℝ)+1)/n) (if k=20 then 1 else x)*exitLength s (((i:ℝ)+1)/n) k)
  rw [← yeq,show ((i:ℝ)+1)/n=b by simp [b,j]]
  change _ ≤ ((exitHeight j u w k:ℝ)/scale)*((1-b*y)*(1+b*s)*((k:ℝ)+1-b*((k:ℝ)/x-1/s)))
  rw [sl]
  rw [show (weight j:ℝ) = (n:ℝ)^2-(i:ℝ)^2 from weight_spec i (by omega)] at raw
  dsimp only [l,b,s,y]
  field_simp
  nlinarith only [raw]

/-- Each rounded integer height dominates the tapered information price on
its entire real bin, including the last bin and every barrier above twenty. -/
theorem grid_price (u w : ℕ) (hu : 0 < u) (uw : u<w) (i : Fin bins)
    (t : ℝ) (mem : t ∈ Set.Icc ((i.val:ℝ)/bins) (((i.val:ℝ)+1)/bins)) (ht : t < 1) :
    ∃ P, 0 < P ∧ P ≤ 1 ∧ admissibleExitPrice ((u:ℝ)/w) t P ∧
      (1-t^2)^2 ≤ ((rectangleHeight (i.val+1) u w:ℝ)/scale)*P := by
  let j := i.val+1
  let s := (u:ℝ)/w
  let l := (i.val:ℝ)/bins
  let b := ((i.val:ℝ)+1)/bins
  let H := (largestHeight j u w:ℝ)/scale
  have hw := hu.trans uw
  have np : (0:ℝ)<bins := by norm_num [bins]
  have sc : (0:ℝ)<scale := by norm_num [scale]
  have hs : 0<s := by dsimp [s]; positivity
  have hs' : s<1 := (div_lt_one (by exact_mod_cast hw)).mpr (by exact_mod_cast uw)
  have hl : 0≤l := by dsimp [l]; positivity
  by_cases cap : signHeight j u w ≤ largestHeight j u w
  · have e : rectangleHeight j u w = signHeight j u w := min_eq_right cap
    change ∃ P, 0<P ∧ P≤1 ∧ admissibleExitPrice s t P ∧ (1-t^2)^2 ≤ ((rectangleHeight j u w:ℝ)/scale)*P
    rw [e]
    exact rectangle_sign_price s l t _ hs hs' hl mem.1 ht (sign_bound u w i.val hu hw i.isLt)
  have inside : j < bins := by
    have ub : j ≤ bins := i.isLt
    apply lt_of_le_of_ne ub
    intro equal
    have tail := exit_le_largest j u w 20 (by decide) le_rfl
    rw [equal,last_tail] at tail
    exact cap (equal ▸ tail)
  have hb1 : b<1 := (div_lt_one np).mpr (by exact_mod_cast inside)
  have hb0 : 0≤b := by dsimp [b]; positivity
  have rect (k : ℕ) (hk : 0<k) (_ : k≤20) :
      let y := if k=20 then 1 else barrierPosterior s k
      (1-l^2)^2*(1+y/s) ≤ H*(exitFactor s b y*exitLength s b k) := by
    let y := if k=20 then 1 else barrierPosterior s k
    have y1 : y≤1 := by dsimp [y]; split_ifs <;> linarith [(barrier_posterior_bounds s hs hs' k).2.1]
    have f0 : 0 ≤ exitFactor s b y := by
      apply mul_nonneg _ (by positivity)
      linarith only [(mul_le_mul_of_nonneg_left y1 hb0).trans (by simpa using hb1.le)]
    have len : 0 ≤ exitLength s b k := by
      have h := exit_length_mono s b hs hs' hb0 hb1.le 1 k (by decide) hk
      have one : exitLength s b 1=2 := by simp [exitLength,barrierPosterior]; ring
      linarith only [h,one]
    apply (exit_bound u w i.val k hu uw inside hk).trans
    apply mul_le_mul_of_nonneg_right _ (mul_nonneg f0 len)
    exact div_le_div_of_nonneg_right (by exact_mod_cast exit_le_largest j u w k hk ‹k≤20›) sc.le
  have hH : 0<H := by
    by_contra! neg
    have zz : H=0 := le_antisymm neg (by dsimp [H]; positivity)
    have test := rect 1 (by decide) (by decide)
    simp only [zz,zero_mul,show ¬(1:ℕ)=20 by decide,↓reduceIte,barrierPosterior,zero_add,
      mul_zero,add_zero,div_one,div_self hs.ne'] at test
    have ll : l<1 := mem.1.trans_lt ht
    have vv : 0 < 1-l^2 := by nlinarith only [mul_pos (sub_pos.mpr ll) (show 0<1+l by linarith only [hl])]
    nlinarith only [test,sq_pos_of_pos vv]
  have e : rectangleHeight j u w = largestHeight j u w := min_eq_left (le_of_not_ge cap)
  change ∃ P, 0<P ∧ P≤1 ∧ admissibleExitPrice s t P ∧ (1-t^2)^2 ≤ ((rectangleHeight j u w:ℝ)/scale)*P
  rw [e]
  exact rectangle_exit_price s l t b H 20 (by decide) hs hs' hl mem.1 mem.2 hb1.le ht hH rect

end ThresholdHC.SharpRMS.Window
