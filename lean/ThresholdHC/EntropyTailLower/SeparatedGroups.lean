import ThresholdHC.EntropyTailLower.EntropyPacking

noncomputable section
namespace ThresholdHC.EntropyTailLower
open Real ThresholdHC.EntropyTailQuantile
open scoped BigOperators

theorem separated_endpoint_power {n : ℕ} (b : Fin n → ℝ)
    (hsep : ∀ i j, j.val = i.val+1 → 4*b j ≤ b i)
    (i : Fin n) (k : ℕ) (hik : i.val+k < n) :
    (4:ℝ)^k*b ⟨i.val+k,hik⟩ ≤ b i := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hik' : i.val+k < n := by omega
    have hs := hsep ⟨i.val+k,hik'⟩ ⟨i.val+(k+1),hik⟩ (by simp; omega)
    have hm := mul_le_mul_of_nonneg_left hs (show (0:ℝ) ≤ 4^k by positivity)
    have hh := ih hik'
    rw [pow_succ]
    nlinarith only [hm,hh]

theorem canonical_parity_separation {n : ℕ} (j : Fin n → ℕ) (hj : StrictMono j)
    (hpar : ∀ i k, j i % 2 = j k % 2) (i k : Fin n) (hik : k.val = i.val+1) :
    4*((1/2:ℝ)^(j k+1)) ≤ (1/2:ℝ)^(j i+1) := by
  have hlt : i < k := by change i.val < k.val; omega
  have hjlt := hj hlt
  have hmod := hpar i k
  have hgap : j i+3 ≤ j k+1 := by omega
  have hp := pow_le_pow_of_le_one (by norm_num : (0:ℝ) ≤ 1/2)
    (by norm_num : (1/2:ℝ) ≤ 1) hgap
  have he : (1/2:ℝ)^(j i+3) = (1/2:ℝ)^(j i+1)*(1/4:ℝ) := by
    rw [show j i+3 = (j i+1)+2 by omega,pow_add]
    norm_num
  rw [he] at hp
  nlinarith only [hp]

theorem sorted_canonical_parity_separation (S : Finset ℕ)
    (hpar : ∀ i ∈ S, ∀ j ∈ S, i % 2 = j % 2)
    (i k : Fin S.card) (hik : k.val = i.val+1) :
    4*((1/2:ℝ)^(S.orderEmbOfFin rfl k+1)) ≤ (1/2:ℝ)^(S.orderEmbOfFin rfl i+1) := by
  apply canonical_parity_separation (S.orderEmbOfFin rfl) (S.orderEmbOfFin rfl).strictMono
  · intro j l
    exact hpar _ (S.orderEmbOfFin_mem rfl j) _ (S.orderEmbOfFin_mem rfl l)
  · exact hik

theorem sorted_canonical_trim_gap (S : Finset ℕ)
    (hpar : ∀ i ∈ S, ∀ j ∈ S, i % 2 = j % 2)
    (δ : ℝ) (hδ : 0 ≤ δ) (hgap : ∀ j ∈ S, δ ≤ (1/2:ℝ)^(j+1))
    (i : Fin (S.card-Nat.clog 4 S.card)) :
    (S.card:ℝ)*δ ≤ (1/2:ℝ)^(S.orderEmbOfFin rfl ⟨i.val,by omega⟩+1) := by
  apply trimmed_gap_amplification S.card (Nat.clog 4 S.card) δ hδ
    (fun k => (1/2:ℝ)^(S.orderEmbOfFin rfl k+1))
  · intro k
    exact hgap _ (S.orderEmbOfFin_mem rfl k)
  · exact Nat.le_pow_clog (by norm_num) S.card
  · intro k t hkt
    exact separated_endpoint_power _ (sorted_canonical_parity_separation S hpar) k t hkt

theorem costEntropy_equiv {I J : Type} [Fintype I] [Fintype J]
    (e : I ≃ J) (a : J → ℝ) : costEntropy (fun i => a (e i)) = costEntropy a := by
  have ht : costTotal (fun i => a (e i)) = costTotal a :=
    Fintype.sum_equiv e _ _ (fun _ => rfl)
  have hn : (∑ i, negMulLog (a (e i))) = ∑ j, negMulLog (a j) :=
    Fintype.sum_equiv e _ _ (fun _ => rfl)
  simp only [costEntropy,ht,hn]

theorem costEntropy_bipartition {I : Type} [Fintype I]
    (a : I → ℝ) (ha : ∀ i, 0 ≤ a i) (p : I → Prop) [DecidablePred p] :
    costEntropy a ≤ 2*costEntropy (fun i => if p i then a i else 0) +
      2*costEntropy (fun i => if p i then 0 else a i) := by
  have h0 (i) : 0 ≤ if p i then a i else 0 := by split_ifs; exact ha i; exact le_rfl
  have h1 (i) : 0 ≤ if p i then 0 else a i := by split_ifs; exact le_rfl; exact ha i
  have h := costEntropy_add_le_two h0 h1
  have he : (fun i => (if p i then a i else 0)+(if p i then 0 else a i)) = a := by
    funext i
    split_ifs <;> simp
  rwa [he] at h

theorem costEntropy_sum_superadditive {I T : Type} [Fintype I] [Fintype T]
    (a : T → I → ℝ) (ha : ∀ t i, 0 ≤ a t i) :
    (∑ t, costEntropy (a t)) ≤ costEntropy (fun i => ∑ t, a t i) := by
  classical
  have h (S : Finset T) : (∑ t ∈ S, costEntropy (a t)) ≤
      costEntropy (fun i => ∑ t ∈ S, a t i) := by
    induction S using Finset.induction_on with
    | empty => simp
    | @insert t S ht ih =>
      rw [Finset.sum_insert ht]
      have hs := costEntropy_superadditive (ha t)
        (fun i => Finset.sum_nonneg (s := S) (fun u _ => ha u i))
      have he : (fun i => a t i + ∑ u ∈ S, a u i) =
          (fun i => ∑ u ∈ insert t S, a u i) := by
        funext i
        rw [Finset.sum_insert ht]
      rw [he] at hs
      exact (add_le_add le_rfl ih).trans hs
  exact h Finset.univ

end ThresholdHC.EntropyTailLower
