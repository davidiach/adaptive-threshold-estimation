import Mathlib.MeasureTheory.Order.Lattice
import Mathlib.Probability.Independence.InfinitePi

noncomputable section
open MeasureTheory ProbabilityTheory
namespace ThresholdHC.Confidence

abbrev MedianIndex (m : ℕ) := Fin (2*m+1)

def MedianSet (m : ℕ) := {s : Finset (MedianIndex m) // s.card = m+1}

instance medianSetFintype (m : ℕ) : Fintype (MedianSet m) := by
  classical
  unfold MedianSet
  infer_instance

instance medianSetNonempty (m : ℕ) : Nonempty (MedianSet m) := by
  obtain ⟨s, _, hs⟩ := Finset.exists_subset_card_eq
    (s := (Finset.univ : Finset (MedianIndex m))) (n := m+1) (by simp; omega)
  exact ⟨⟨s, hs⟩⟩

theorem medianSet_nonempty {m : ℕ} (s : MedianSet m) : s.val.Nonempty :=
  Finset.card_pos.mp (by rw [s.property]; omega)

def subsetMinimum {m : ℕ} (s : MedianSet m) (f : MedianIndex m → ℝ) : ℝ :=
  s.val.inf' (medianSet_nonempty s) f

def median (m : ℕ) (f : MedianIndex m → ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun s : MedianSet m => subsetMinimum s f)

theorem measurable_subsetMinimum {Ω : Type} [MeasurableSpace Ω] {m : ℕ}
    (s : MedianSet m) (f : MedianIndex m → Ω → ℝ) (hf : ∀ i, Measurable (f i)) :
    Measurable (fun z => subsetMinimum s (fun i => f i z)) := by
  have he : (fun z => subsetMinimum s (fun i => f i z)) =
      s.val.inf' (medianSet_nonempty s) f := by
    funext z
    exact (Finset.inf'_apply (medianSet_nonempty s) f z).symm
  rw [he]
  exact Finset.measurable_sup' (α := OrderDual ℝ) (medianSet_nonempty s) (fun i _ => hf i)

theorem measurable_median {Ω : Type} [MeasurableSpace Ω] (m : ℕ)
    (f : MedianIndex m → Ω → ℝ) (hf : ∀ i, Measurable (f i)) :
    Measurable (fun z => median m (fun i => f i z)) := by
  convert (Finset.measurable_sup' Finset.univ_nonempty
    (fun s _ => measurable_subsetMinimum s f hf)) using 1
  funext z
  exact (Finset.sup'_apply Finset.univ_nonempty
    (fun s : MedianSet m => fun z => subsetMinimum s (fun i => f i z)) z).symm

theorem medianSet_card_le (m : ℕ) : Fintype.card (MedianSet m) ≤ 2^(2*m+1) := by
  calc
    Fintype.card (MedianSet m) ≤ Fintype.card (Finset (MedianIndex m)) :=
      Fintype.card_le_of_injective Subtype.val Subtype.val_injective
    _ = 2^(2*m+1) := by simp

/-- A strict majority of values in an interval puts the median in that interval. -/
theorem median_interval (m : ℕ) (f : MedianIndex m → ℝ) (a b : ℝ)
    (hgood : m+1 ≤ (Finset.univ.filter (fun i => a ≤ f i ∧ f i ≤ b)).card) :
    a ≤ median m f ∧ median m f ≤ b := by
  classical
  let good := Finset.univ.filter (fun i => a ≤ f i ∧ f i ≤ b)
  let bad := Finset.univ.filter (fun i => ¬ (a ≤ f i ∧ f i ≤ b))
  have hc : good.card + bad.card = 2*m+1 := by
    simpa [good,bad] using (Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset (MedianIndex m))) (fun i => a ≤ f i ∧ f i ≤ b))
  obtain ⟨s, hsg, hsc⟩ := Finset.exists_subset_card_eq hgood
  let S : MedianSet m := ⟨s, hsc⟩
  constructor
  · apply le_trans ?_ (Finset.le_sup' (fun s : MedianSet m => subsetMinimum s f) (Finset.mem_univ S))
    apply Finset.le_inf'
    intro i hi
    exact (Finset.mem_filter.mp (hsg hi)).2.1
  · apply Finset.sup'_le
    intro S _
    have hex : ∃ i ∈ S.val, i ∈ good := by
      by_contra hn
      push_neg at hn
      have hsub : S.val ⊆ bad := by
        intro i hi
        simp only [bad, Finset.mem_filter, Finset.mem_univ, true_and]
        simpa [good] using hn i hi
      have hcard := Finset.card_le_card hsub
      rw [S.property] at hcard
      change m+1 ≤ good.card at hgood
      omega
    obtain ⟨i, hi, hig⟩ := hex
    exact (Finset.inf'_le f hi).trans (Finset.mem_filter.mp hig).2.2

/-- A bad median requires an entire majority-sized subset of bad coordinates. -/
theorem median_bad_subset (m : ℕ) (f : MedianIndex m → ℝ) (θ r : ℝ)
    (hbad : r < |median m f-θ|) :
    ∃ s : MedianSet m, ∀ i ∈ s.val, r < |f i-θ| := by
  classical
  let good := Finset.univ.filter (fun i => θ-r ≤ f i ∧ f i ≤ θ+r)
  let bad := Finset.univ.filter (fun i => ¬ (θ-r ≤ f i ∧ f i ≤ θ+r))
  have hc : good.card + bad.card = 2*m+1 := by
    simpa [good,bad] using (Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset (MedianIndex m))) (fun i => θ-r ≤ f i ∧ f i ≤ θ+r))
  have hg : ¬ m+1 ≤ good.card := by
    intro hg
    have hm := median_interval m f (θ-r) (θ+r) hg
    have hab : |median m f-θ| ≤ r := abs_le.mpr ⟨by linarith,by linarith⟩
    linarith
  obtain ⟨s, hsb, hsc⟩ := Finset.exists_subset_card_eq (show m+1 ≤ bad.card by omega)
  refine ⟨⟨s,hsc⟩, ?_⟩
  intro i hi
  have hn := (Finset.mem_filter.mp (hsb hi)).2
  apply lt_of_not_ge
  intro hab
  have ha := abs_le.mp hab
  exact hn ⟨by linarith,by linarith⟩

end ThresholdHC.Confidence
