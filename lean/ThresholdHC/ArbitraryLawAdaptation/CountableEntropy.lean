import ThresholdHC.ArbitraryLawAdaptation.BandPenalty
import ThresholdHC.EntropyTailQuantile.CostEntropySeries
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-! Countable entropy as an extended-valued supremum of finite prefixes.
Finite-coordinate limits preserve a uniform entropy bound. No finite bound
on the full inverse-square cost or entropy is imposed. -/

noncomputable section
open Real Filter
open scoped BigOperators ENNReal Topology
namespace ThresholdHC.ArbitraryLawAdaptation
open ThresholdHC.EntropyTailQuantile

def countableEntropy (a : ℕ → ℝ) : ℝ≥0∞ :=
  ⨆ n : ℕ, ENNReal.ofReal (costEntropy (fun i : Fin n => a i.val))

theorem prefix_le_countableEntropy (a : ℕ → ℝ) (n : ℕ) :
    ENNReal.ofReal (costEntropy (fun i : Fin n => a i.val)) ≤ countableEntropy a :=
  le_iSup (fun m => ENNReal.ofReal (costEntropy (fun i : Fin m => a i.val))) n

theorem countableEntropy_mono {a b : ℕ → ℝ} (ha : ∀ i, 0 ≤ a i)
    (hab : ∀ i, a i ≤ b i) : countableEntropy a ≤ countableEntropy b := by
  apply iSup_le
  intro n
  exact (ENNReal.ofReal_le_ofReal (costEntropy_mono (fun i : Fin n => ha i.val)
    (fun i => hab i.val))).trans (prefix_le_countableEntropy b n)

theorem countableEntropy_limit_le {v : ℕ → ℕ → ℝ} {a : ℕ → ℝ} {C : ℝ≥0∞}
    (hv : ∀ j, Tendsto (fun n => v n j) atTop (𝓝 (a j)))
    (hbound : ∀ n, countableEntropy (v n) ≤ C) : countableEntropy a ≤ C := by
  apply iSup_le
  intro m
  have hvec : Tendsto (fun n => fun i : Fin m => v n i.val) atTop
      (𝓝 (fun i : Fin m => a i.val)) := tendsto_pi_nhds.mpr (fun i => hv i.val)
  have hg := continuous_costEntropy.continuousAt.tendsto.comp hvec
  have he := ENNReal.continuous_ofReal.continuousAt.tendsto.comp hg
  exact le_of_tendsto he (Eventually.of_forall fun n =>
    (prefix_le_countableEntropy (v n) m).trans (hbound n))

/-- Discarding cells as well as merging them cannot increase entropy. -/
theorem costEntropy_partial_pushforward {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq κ] {b : ι → ℝ} (hb : ∀ i, 0 ≤ b i) (dest : ι → Option κ) :
    costEntropy (fun k => ∑ i, if dest i = some k then b i else 0) ≤ costEntropy b := by
  classical
  let out (k : Option κ) : ℝ := ∑ i, if dest i = k then b i else 0
  let kept : Option κ → ℝ := fun k => match k with
    | none => 0
    | some j => out (some j)
  have ho (k : Option κ) : 0 ≤ out k := Finset.sum_nonneg fun i _ => by
    split_ifs
    · exact hb i
    · exact le_rfl
  have hk (k : Option κ) : 0 ≤ kept k := by cases k; exact le_rfl; exact ho _
  have hle (k : Option κ) : kept k ≤ out k := by cases k; exact ho _; exact le_rfl
  have he : costEntropy kept = costEntropy (fun k => out (some k)) := by
    simp [costEntropy,costTotal,kept,Fintype.sum_option]
  exact he.symm.le.trans ((costEntropy_mono hk hle).trans (costEntropy_pushforward hb dest))

theorem costEntropy_finite_destination_prefix {ι : Type*} [Fintype ι]
    {b : ι → ℝ} (hb : ∀ i, 0 ≤ b i) (dest : ι → ℕ) (m : ℕ) :
    costEntropy (fun j : Fin m => ∑ i, if dest i = j.val then b i else 0) ≤ costEntropy b := by
  classical
  let tag (i : ι) : Option (Fin m) := if h : dest i < m then some ⟨dest i,h⟩ else none
  have he (i : ι) (j : Fin m) : (tag i = some j) ↔ (dest i = j.val) := by
    by_cases h : dest i < m
    · simp [tag,h,Fin.ext_iff]
    · have hne : dest i ≠ j.val := by
        intro he
        exact h (he.symm ▸ j.isLt)
      simp [tag,h,hne]
  simpa only [he] using costEntropy_partial_pushforward hb tag

theorem tendsto_square_ranges :
    Tendsto (fun n : ℕ => (Finset.range n).product (Finset.range n)) atTop atTop := by
  apply tendsto_atTop.mpr
  intro s
  filter_upwards [eventually_ge_atTop (s.sup (fun x => max x.1 x.2)+1)] with n hn
  intro x hx
  have hs := Finset.le_sup (f := fun x : ℕ × ℕ => max x.1 x.2) hx
  exact Finset.mem_product.mpr ⟨Finset.mem_range.mpr (by omega),Finset.mem_range.mpr (by omega)⟩

theorem summable_tendsto_square {b : ℕ × ℕ → ℝ} (hb : Summable b) :
    Tendsto (fun n => ∑ x : Fin n × Fin n, b (x.1.val,x.2.val)) atTop (𝓝 (∑' x, b x)) := by
  have h := hb.hasSum.comp tendsto_square_ranges
  have he (n : ℕ) : (∑ x ∈ (Finset.range n).product (Finset.range n), b x) =
      ∑ x : Fin n × Fin n, b (x.1.val,x.2.val) := by
    rw [Finset.product_eq_sprod,Finset.sum_product,Fintype.sum_prod_type]
    rw [Finset.sum_range]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_range]
  simpa only [Function.comp_def,he] using h

end ThresholdHC.ArbitraryLawAdaptation
