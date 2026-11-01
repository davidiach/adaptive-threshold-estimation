import ThresholdHC.EntropyTailLower.EntropyTiers
import ThresholdHC.EntropyTailLower.SeparatedGroups
import ThresholdHC.EntropyTailLower.PackedAllocation
import ThresholdHC.EntropyTailQuantile.CostEntropySeries

noncomputable section
namespace ThresholdHC.EntropyTailLower
open Real ThresholdHC.EntropyTailQuantile
open scoped BigOperators

theorem costEntropy_fin_prefix_le {m n : ℕ} (hmn : m ≤ n)
    (a : Fin n → ℝ) (ha : ∀ i, 0 ≤ a i) :
    costEntropy (fun i : Fin m => a (Fin.castLE hmn i)) ≤ costEntropy a := by
  let f : ℕ → ℝ := fun k => if h : k < n then a ⟨k,h⟩ else 0
  have hf (k) : 0 ≤ f k := by dsimp [f]; split_ifs; exact ha _; exact le_rfl
  have he (k : ℕ) (hk : k ≤ n) : (fun i : Fin k => f i) =
      (fun i : Fin k => a (Fin.castLE hk i)) := by
    funext i
    simp only [f, dite_eq_left (lt_of_lt_of_le i.isLt hk)]
    rfl
  have h := costEntropy_prefix_monotone hf hmn
  change costEntropy (fun i : Fin m => f i) ≤ costEntropy (fun i : Fin n => f i) at h
  rw [he m hmn, he n le_rfl] at h
  exact h

theorem group_mass_le_scaled_entropy {I : Type} [Fintype I]
    (w b : I → ℝ) (a : ℝ) (ha : 0 < a) (hw : ∀ i, 0 ≤ w i)
    (hb : ∀ i, 0 < b i) (hba : ∀ i, b i ≤ a) :
    (∑ i, w i)/a^2 ≤ costEntropy (fun i => w i/(b i)^2) := by
  have hc (i) : 0 ≤ w i/(b i)^2 := div_nonneg (hw i) (sq_nonneg _)
  have hi (i) : w i ≤ (w i/(b i)^2)*a^2 := by
    have hs := (sq_le_sq₀ (hb i).le ha.le).mpr (hba i)
    have hm := mul_le_mul_of_nonneg_left hs (hc i)
    rwa [div_mul_cancel₀ _ (ne_of_gt (sq_pos_of_pos (hb i)))] at hm
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hi i)
  rw [← Finset.sum_mul] at hs
  have ht : (∑ i, w i)/a^2 ≤ costTotal (fun i => w i/(b i)^2) :=
    (div_le_iff₀ (sq_pos_of_pos ha)).mpr hs
  exact ht.trans (costTotal_le_costEntropy hc)

theorem comparable_retained_gap_floor {n : ℕ} (hn : 0 < n)
    (a b : Fin n → ℝ) (c A lam : ℝ) (hc : 0 < c) (hlam : 0 ≤ lam)
    (hlo : ∀ i, c ≤ a i) (hhi : ∀ i, a i ≤ 4*c)
    (hA : costTotal a ≤ A)
    (hgap : ∀ i, lam*(1+log (A/a i)) ≤ 2*b i) :
    ∀ i, lam*(1+log (n:ℝ))/16 ≤ b i := by
  have ha (i) : 0 < a i := hc.trans_le (hlo i)
  have hn0 : (0:ℝ) < n := by exact_mod_cast hn
  have hsum : c*(n:ℝ) ≤ A := by
    have h := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hlo i)
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at h
    exact (by simpa only [mul_comm,costTotal] using h : c*(n:ℝ) ≤ costTotal a).trans hA
  intro i
  have haiA := (le_costTotal (fun i => (ha i).le) i).trans hA
  have hx : 1 ≤ A/a i := (le_div_iff₀ (ha i)).mpr (by simpa using haiA)
  have hnx : (n:ℝ) ≤ 4*(A/a i) := by
    have hh := mul_le_mul_of_nonneg_left (hhi i) hn0.le
    have he : 4*(A/a i) = (4*A)/a i := by ring
    rw [he]
    apply (le_div_iff₀ (ha i)).mpr
    nlinarith only [hh,hsum]
  have hl := comparable_group_log_bound n (A/a i) hn0 hx hnx
  have hm := mul_le_mul_of_nonneg_left hl hlam
  have hg := hgap i
  have hb0 : 0 ≤ b i := by
    have hlx := log_nonneg hx
    have hnon : 0 ≤ lam*(1+log (A/a i)) := mul_nonneg hlam (by linarith)
    linarith only [hg,hnon]
  nlinarith only [hm,hg,hb0]

theorem comparable_retained_group_trim (n : ℕ) (hn : 0 < n)
    (w b : Fin n → ℝ) (c A lam : ℝ) (hc : 0 < c) (hlam : 0 < lam)
    (hb : ∀ i, 0 < b i)
    (hlo : ∀ i, c ≤ w i/(b i)^2) (hhi : ∀ i, w i/(b i)^2 ≤ 4*c)
    (hA : costTotal (fun i => w i/(b i)^2) ≤ A)
    (hgap : ∀ i, lam*(1+log (A/(w i/(b i)^2))) ≤ 2*b i)
    (hsep : ∀ i j, j.val = i.val+1 → 4*b j ≤ b i) :
    let m := n-Nat.clog 4 n
    let e : Fin m → Fin n := Fin.castLE (Nat.sub_le n _)
    let a := b ⟨0,hn⟩
    let s := c*((n:ℝ)*(lam*(1+log (n:ℝ))/16))^2
    let τ := ∑ i, w (e i)
    let G := costEntropy (fun i => w (e i)/(b (e i))^2)
    0 < m ∧ 0 < s ∧ (∀ i, s ≤ w (e i)) ∧ s ≤ τ ∧
      (∀ i, b (e i) ≤ a) ∧ τ/a^2 ≤ G ∧
      costEntropy (fun i => w i/(b i)^2) ≤ 64*G ∧
      G ≤ costEntropy (fun i => w i/(b i)^2) ∧
      lam^2*G^2 ≤ 4096*(τ*s/a^2) := by
  dsimp only
  let m := n-Nat.clog 4 n
  let e : Fin m → Fin n := Fin.castLE (Nat.sub_le n _)
  let a := b ⟨0,hn⟩
  let δ := lam*(1+log (n:ℝ))/16
  let bmin := (n:ℝ)*δ
  let s := c*bmin^2
  let τ := ∑ i, w (e i)
  let G := costEntropy (fun i => w (e i)/(b (e i))^2)
  let F := costEntropy (fun i => w i/(b i)^2)
  change 0 < m ∧ 0 < s ∧ (∀ i, s ≤ w (e i)) ∧ s ≤ τ ∧
    (∀ i, b (e i) ≤ a) ∧ τ/a^2 ≤ G ∧ F ≤ 64*G ∧ G ≤ F ∧
    lam^2*G^2 ≤ 4096*(τ*s/a^2)
  have hm := clog_four_trim_size n hn
  have hn1 : (1:ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0:ℝ) < n := by exact_mod_cast hn
  have hδ : 0 < δ := by dsimp [δ]; exact div_pos (mul_pos hlam (by linarith [log_nonneg hn1])) (by norm_num)
  have hmin : 0 < bmin := mul_pos hn0 hδ
  have hs : 0 < s := mul_pos hc (sq_pos_of_pos hmin)
  have hcost (i) : 0 ≤ w i/(b i)^2 := hc.le.trans (hlo i)
  have hwc (i) : c*(b i)^2 ≤ w i := (le_div_iff₀ (sq_pos_of_pos (hb i))).mp (hlo i)
  have hw (i) : 0 ≤ w i := (mul_nonneg hc.le (sq_nonneg _)).trans (hwc i)
  have hδb := comparable_retained_gap_floor hn (fun i => w i/(b i)^2) b c A lam
    hc hlam.le hlo hhi hA hgap
  have hminb (i : Fin m) : bmin ≤ b (e i) :=
    trimmed_gap_amplification n (Nat.clog 4 n) δ hδ.le b hδb
      (Nat.le_pow_clog (by norm_num) n) (separated_endpoint_power b hsep) i
  have hsw (i : Fin m) : s ≤ w (e i) := by
    have hsq := (sq_le_sq₀ hmin.le (hb (e i)).le).mpr (hminb i)
    exact (mul_le_mul_of_nonneg_left hsq hc.le).trans (hwc (e i))
  let i0 : Fin m := ⟨0,hm.1⟩
  have he0 : e i0 = ⟨0,hn⟩ := rfl
  have hwτ (i : Fin m) : w (e i) ≤ τ :=
    Finset.single_le_sum (fun k _ => hw (e k)) (Finset.mem_univ i)
  have hsτ : s ≤ τ := (hsw i0).trans (hwτ i0)
  have hba (i : Fin m) : b (e i) ≤ a := by
    have hp := separated_endpoint_power b hsep ⟨0,hn⟩ (e i).val (by simpa using (e i).isLt)
    have he : (⟨0+(e i).val,by simpa using (e i).isLt⟩ : Fin n) = e i := by ext; simp
    rw [he] at hp
    have hpow : (1:ℝ) ≤ 4^(e i).val := one_le_pow₀ (by norm_num)
    have hl := mul_le_mul_of_nonneg_right hpow (hb (e i)).le
    exact (by simpa using hl : b (e i) ≤ 4^(e i).val*b (e i)).trans hp
  have hGscale : τ/a^2 ≤ G := group_mass_le_scaled_entropy (fun i => w (e i))
    (fun i => b (e i)) a (hb ⟨0,hn⟩) (fun i => hw (e i)) (fun i => hb (e i)) hba
  have hFG : F ≤ 64*G := comparable_entropy_subfamily
    (fun i => w i/(b i)^2) (fun i => w (e i)/(b (e i))^2) c hc.le hcost hhi
    (fun i => hlo (e i)) (by simpa only [Fintype.card_fin] using hn)
    (by simpa only [Fintype.card_fin] using (hm.1 : 0 < m))
    (by simpa only [Fintype.card_fin] using hm.2)
  have hGF : G ≤ F := costEntropy_fin_prefix_le (Nat.sub_le n _) _ hcost
  have hFbound : F ≤ 4*c*(n:ℝ)*(1+log (n:ℝ)) := by
    simpa using (comparable_cost_entropy_bounds (fun i => w i/(b i)^2) c hc.le hlo hhi).2
  have hscale : lam*G ≤ 64*c*bmin := packed_gap_entropy_scale lam G c n bmin
    hlam.le hc.le (hGF.trans hFbound) (by dsimp [bmin,δ]; exact le_of_eq (by ring))
  have hca : c*a^2 ≤ τ := by
    have hh := (hwc (e i0)).trans (hwτ i0)
    rwa [he0] at hh
  have hsat := packed_saturation_numeric τ s a c bmin lam G (hb ⟨0,hn⟩)
    hc.le hmin.le hlam.le (costEntropy_nonneg (fun i => hcost (e i))) hca le_rfl hscale
  exact ⟨hm.1,hs,hsw,hsτ,hba,hGscale,hFG,hGF,hsat⟩

end ThresholdHC.EntropyTailLower
