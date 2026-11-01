import ThresholdHC.EntropyTailLower.EntropyPacking

noncomputable section
namespace ThresholdHC.EntropyTailLower
open Real ThresholdHC.EntropyTailQuantile
open scoped BigOperators

theorem dense_tier_cross (k : ℕ) (n c A F : ℝ) (_hc : 0 ≤ c) (hA0 : 0 ≤ A)
    (hn : (2:ℝ)^k ≤ n) (hA : A ≤ 4*c*n) (hF : c*n*(1+log n) ≤ F) :
    A*(k+1:ℝ)*log 2 ≤ 4*F := by
  have hp : (1:ℝ) ≤ 2^k := one_le_pow₀ (by norm_num)
  have hn1 : 1 ≤ n := hp.trans hn
  have hl := log_le_log (show (0:ℝ) < 2^k by positivity) hn
  rw [log_pow] at hl
  have hl2 : log (2:ℝ) ≤ 1 := by
    have h := log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 2)
    norm_num at h
    exact h
  have hcoef : (k+1:ℝ)*log 2 ≤ 1+log n := by nlinarith only [hl,hl2]
  have h1 := mul_le_mul_of_nonneg_left hcoef hA0
  have h2 := mul_le_mul_of_nonneg_right hA (show 0 ≤ 1+log n by linarith [log_nonneg hn1])
  nlinarith only [h1,h2,hF]

theorem sparse_tier_mass (k : ℕ) (n M A : ℝ) (hM : 0 ≤ M)
    (hn : n ≤ (2:ℝ)^k) (hA : A ≤ M*n*(1/4:ℝ)^k) :
    A ≤ M*(1/2:ℝ)^k := by
  have hm := mul_le_mul_of_nonneg_left hn hM
  have hp := mul_le_mul_of_nonneg_right hm (show (0:ℝ) ≤ (1/4:ℝ)^k by positivity)
  have he : M*(2:ℝ)^k*(1/4:ℝ)^k = M*(1/2:ℝ)^k := by
    rw [mul_assoc,← mul_pow]
    norm_num
  rw [he] at hp
  exact hA.trans hp

theorem tier_cross_sum (K : ℕ) (A F : Fin K → ℝ) (n : Fin K → ℕ) (M : ℝ)
    (hM0 : 0 ≤ M) (hM : M ≤ ∑ i, F i) (hA0 : ∀ i, 0 ≤ A i) (hF0 : ∀ i, 0 ≤ F i)
    (hA : ∀ i, A i ≤ M*n i*(1/4:ℝ)^i.val)
    (hF : ∀ i, (M*(1/4:ℝ)^(i.val+1))*n i*(1+log (n i)) ≤ F i) :
    (∑ i, A i*(i.val+1:ℝ)*log 2) ≤ 8*∑ i, F i := by
  have hl2 : 0 ≤ log (2:ℝ) := log_nonneg (by norm_num)
  have hl21 : log (2:ℝ) ≤ 1 := by
    have h := log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 2)
    norm_num at h
    exact h
  have hi (i : Fin K) : A i*(i.val+1:ℝ)*log 2 ≤
      4*F i + M*((i.val+1:ℝ)*(1/2:ℝ)^i.val) := by
    by_cases hd : 2^i.val ≤ n i
    · have hd' : (2:ℝ)^i.val ≤ n i := by exact_mod_cast hd
      have he : M*n i*(1/4:ℝ)^i.val = 4*(M*(1/4:ℝ)^(i.val+1))*n i := by
        rw [pow_succ]
        ring
      have hh := dense_tier_cross i.val (n i) (M*(1/4:ℝ)^(i.val+1)) (A i) (F i)
        (by positivity) (hA0 i) hd' (by rw [← he]; exact hA i) (hF i)
      have hn : 0 ≤ M*((i.val+1:ℝ)*(1/2:ℝ)^i.val) := by positivity
      linarith only [hh,hn]
    · have hn' : (n i:ℝ) ≤ (2:ℝ)^i.val := by exact_mod_cast (le_of_lt (lt_of_not_ge hd))
      have hs := sparse_tier_mass i.val (n i) M (A i) hM0 hn' (hA i)
      have h1 := mul_le_mul_of_nonneg_right hs (show 0 ≤ (i.val+1:ℝ)*log 2 by positivity)
      have h2 := mul_le_mul_of_nonneg_left hl21
        (show 0 ≤ M*(1/2:ℝ)^i.val*(i.val+1:ℝ) by positivity)
      nlinarith only [h1,h2,hF0 i]
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hi i)
  simp only [Finset.sum_add_distrib,← Finset.mul_sum] at hs
  have hg := mul_le_mul_of_nonneg_left (sum_weighted_half_pow_le_four K) hM0
  nlinarith only [hs,hg,hM]

theorem entropy_partition_tier_bound {I : Type} [Fintype I]
    (K : ℕ) (a : I → ℝ) (ha : ∀ i, 0 ≤ a i) (p : I → Fin K)
    (n : Fin K → ℕ) (M : ℝ) (hM0 : 0 ≤ M)
    (hM : M ≤ ∑ j, costEntropy (fun i => if p i = j then a i else 0))
    (hA : ∀ j, costTotal (fun i => if p i = j then a i else 0) ≤
      M*n j*(1/4:ℝ)^j.val)
    (hF : ∀ j, (M*(1/4:ℝ)^(j.val+1))*n j*(1+log (n j)) ≤
      costEntropy (fun i => if p i = j then a i else 0)) :
    costEntropy a ≤ 9*∑ j, costEntropy (fun i => if p i = j then a i else 0) := by
  let A := fun j => costTotal (fun i => if p i = j then a i else 0)
  let F := fun j => costEntropy (fun i => if p i = j then a i else 0)
  have hn (j : Fin K) (i : I) : 0 ≤ if p i = j then a i else 0 := by
    split_ifs
    · exact ha i
    · exact le_rfl
  have hA0 (j) : 0 ≤ A j := costTotal_nonneg (hn j)
  have hF0 (j) : 0 ≤ F j := costEntropy_nonneg (hn j)
  have ht : costTotal A = costTotal a := by
    dsimp [A,costTotal]
    rw [Finset.sum_comm]
    simp
  have href := costEntropy_geometric_reference K A hA0
  rw [ht] at href
  have hs := tier_cross_sum K A F n M hM0 hM hA0 hF0 hA hF
  have hc : costEntropy a = (∑ j, F j)+costEntropy A-costTotal a := costEntropy_partition a p
  change costEntropy a ≤ 9*∑ j, F j
  linarith only [href,hs,hc]

theorem exists_cost_tier (M x : ℝ) (hx : 0 < x) (hxM : x ≤ M) :
    ∃ k : ℕ, M*(1/4:ℝ)^(k+1) < x ∧ x ≤ M*(1/4:ℝ)^k := by
  have hM : 0 < M := hx.trans_le hxM
  obtain ⟨k,hlo,hhi⟩ := exists_nat_pow_near_of_lt_one (div_pos hx hM)
    ((div_le_one hM).mpr hxM) (by norm_num : (0:ℝ) < 1/4) (by norm_num : (1/4:ℝ) < 1)
  refine ⟨k,?_,?_⟩
  · have h := (lt_div_iff₀ hM).mp hlo
    simpa only [mul_comm] using h
  · have h := (div_le_iff₀ hM).mp hhi
    simpa only [mul_comm] using h

theorem sum_indicator_eq_subtype {I : Type} [Fintype I] (p : I → Prop)
    [DecidablePred p] (f : I → ℝ) :
    (∑ i, if p i then f i else 0) = ∑ i : {i // p i}, f i := by
  have h := Fintype.sum_subtype_add_sum_subtype p (fun i => if p i then f i else 0)
  have hp (i : {i // p i}) : (if p i then f i else 0) = f i := ite_eq_left i.property
  have hn (i : {i // ¬p i}) : (if p i then f i else 0) = 0 := ite_eq_right i.property
  simp only [hp,hn,Finset.sum_const_zero,add_zero] at h
  exact h.symm

theorem costEntropy_indicator_eq_subtype {I : Type} [Fintype I] (p : I → Prop)
    [DecidablePred p] (a : I → ℝ) :
    costEntropy (fun i => if p i then a i else 0) = costEntropy (fun i : {i // p i} => a i) := by
  simp only [costEntropy,costTotal]
  rw [sum_indicator_eq_subtype p a]
  simp_rw [apply_ite negMulLog,negMulLog_zero]
  rw [sum_indicator_eq_subtype p (fun i => negMulLog (a i))]

theorem exists_entropy_tier_partition {I : Type} [Fintype I] [Nonempty I]
    (a : I → ℝ) (ha : ∀ i, 0 < a i) :
    ∃ (K : ℕ) (p : I → Fin K) (c : Fin K → ℝ),
      (∀ k, 0 < c k) ∧ (∀ i, c (p i) < a i ∧ a i ≤ 4*c (p i)) ∧
      costEntropy a ≤ 9*∑ k, costEntropy (fun i => if p i = k then a i else 0) := by
  classical
  obtain ⟨imax,_,hmax⟩ := Finset.exists_max_image Finset.univ a Finset.univ_nonempty
  let M := a imax
  have hM : 0 < M := ha imax
  have hamax (i) : a i ≤ M := hmax i (Finset.mem_univ i)
  choose r hlo hhi using (fun i => exists_cost_tier M (a i) (ha i) (hamax i))
  let K := (Finset.univ.sup r)+1
  have hr (i) : r i < K := by
    have h := Finset.le_sup (f := r) (Finset.mem_univ i)
    dsimp [K]
    omega
  let p : I → Fin K := fun i => ⟨r i,hr i⟩
  let c : Fin K → ℝ := fun k => M*(1/4:ℝ)^(k.val+1)
  let n : Fin K → ℕ := fun k => Fintype.card {i // p i = k}
  have hc (k) : 0 < c k := by dsimp [c]; positivity
  have hbounds (i) : c (p i) < a i ∧ a i ≤ 4*c (p i) := by
    constructor
    · exact hlo i
    · have he : 4*c (p i) = M*(1/4:ℝ)^(r i) := by dsimp [c,p]; rw [pow_succ]; ring
      rw [he]
      exact hhi i
  have hnonneg (k : Fin K) (i : I) : 0 ≤ if p i = k then a i else 0 := by
    split_ifs
    · exact (ha i).le
    · exact le_rfl
  have htotal : (∑ k, costTotal (fun i => if p i = k then a i else 0)) = costTotal a := by
    simp only [costTotal]
    rw [Finset.sum_comm]
    simp
  have hMsum : M ≤ ∑ k, costEntropy (fun i => if p i = k then a i else 0) := by
    have hs := Finset.sum_le_sum (s := Finset.univ)
      (fun k _ => costTotal_le_costEntropy (hnonneg k))
    rw [htotal] at hs
    exact (le_costTotal (fun i => (ha i).le) imax).trans hs
  have hupper (k : Fin K) : costTotal (fun i => if p i = k then a i else 0) ≤
      M*n k*(1/4:ℝ)^k.val := by
    have hs := Finset.sum_le_sum (s := Finset.univ)
      (fun (i : {i // p i = k}) _ => by
        have h := (hbounds i).2
        rw [i.property] at h
        exact h)
    have he : (∑ _i : {i // p i = k}, 4*c k) = M*n k*(1/4:ℝ)^k.val := by
      simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
      dsimp [c,n]
      rw [pow_succ]
      ring
    rw [he] at hs
    simpa only [costTotal,sum_indicator_eq_subtype] using hs
  have hlower (k : Fin K) : (M*(1/4:ℝ)^(k.val+1))*n k*(1+log (n k)) ≤
      costEntropy (fun i => if p i = k then a i else 0) := by
    have hlo' (i : {i // p i = k}) : c k ≤ a i := by
      have h := (hbounds i).1.le
      rwa [i.property] at h
    have hm := costEntropy_mono (a := fun _ : {i // p i = k} => c k)
      (fun _ => (hc k).le) hlo'
    rw [costEntropy_const] at hm
    rw [costEntropy_indicator_eq_subtype]
    exact hm
  refine ⟨K,p,c,hc,hbounds,?_⟩
  exact entropy_partition_tier_bound K a (fun i => (ha i).le) p n M hM.le hMsum hupper hlower

end ThresholdHC.EntropyTailLower
