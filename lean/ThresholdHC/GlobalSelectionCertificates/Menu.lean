import ThresholdHC.FiniteLawCertificates.Objective
import ThresholdHC.BandwiseSuffix.Full

noncomputable section
open MeasureTheory
open scoped ENNReal BigOperators Topology
namespace ThresholdHC.GlobalSelectionCertificates
open ThresholdHC.Tier6 ThresholdHC.FiniteLawCertificates
open ThresholdHC.EntropyTail ThresholdHC.BandwiseSuffix
open ThresholdHC.DeterministicCertificates

/-- Strictly positive finite weights identify the actual support, not a supplied support premise. -/
theorem atomic_support {n : ℕ} (d : Fin n → Gap) (w : Fin n → ℚ)
    (hw : ∀ i, 0 < w i) : (atomicMeasure d w).support = Set.range d := by
  classical
  apply Set.Subset.antisymm
  · apply Measure.support_subset_of_isClosed (Set.finite_range d).isClosed
    rw [mem_ae_iff]
    simp only [atomicMeasure, Measure.finsetSum_apply]
    apply Finset.sum_eq_zero
    intro i _
    simp [Measure.smul_apply]
  · rintro _ ⟨i,rfl⟩
    rw [Measure.mem_support_iff_forall]
    intro U hU
    have hm : d i ∈ U := mem_of_mem_nhds hU
    have hle : ENNReal.ofReal (w i:ℝ) ≤ atomicMeasure d w U := by
      unfold atomicMeasure
      rw [Measure.finsetSum_apply]
      have h := Finset.single_le_sum (fun j _ => bot_le : ∀ j ∈ Finset.univ,
        0 ≤ (ENNReal.ofReal (w j:ℝ) • Measure.dirac (d j)) U) (Finset.mem_univ i)
      simpa [Measure.smul_apply, Measure.dirac_apply_of_mem hm] using h
    exact (ENNReal.ofReal_pos.mpr (by exact_mod_cast hw i)).trans_le hle

def fractions {n : ℕ} (s : Fin n → Bool) : Fin n → ℚ := fun i => if s i then 1 else 0

theorem fractions_valid {n : ℕ} (s : Fin n → Bool) :
    ∀ i, 0 ≤ fractions s i ∧ fractions s i ≤ 1 := by
  intro i
  cases h : s i <;> simp [fractions,h]

/-- Finite, exact suffix predicate; assigned bands are separately checked against the original bands. -/
def suffixCheck {n : ℕ} (g : Fin n → ℚ) (bands : Fin n → ℕ) (s : Fin n → Bool) : Bool :=
  decide (∀ i j, bands i = bands j → g i < g j → s i = true → s j = true)

/-- The complete rational suffix family contains an optimizer of original K against all submeasures. -/
theorem suffix_attains {n m : ℕ} (g w : Fin n → ℚ) (labels : Fin m → ℕ)
    (bands : Fin n → ℕ) (ρ B : ℚ) (hg : ∀ i, 0 < g i ∧ g i ≤ 1/2)
    (hw : ∀ i, 0 < w i) (hsum : ∑ i, w i = 1)
    (hl : Function.Injective labels) (hc : ∀ i, ∃ j, inBand (g i) (labels j) = true)
    (hb : ∀ i, inBand (g i) (bands i) = true)
    (hρ : 0 < ρ) (hρ1 : ρ ≤ 1/4) (hB : 0 < B) :
    ∃ s : Fin n → Bool, suffixCheck g bands s = true ∧
      (selection (atomicMeasure (points g hg) w) (ρ:ℝ) (B:ℝ)).toReal =
        (objectiveExpr g w (fractions s) labels ρ B).eval := by
  classical
  let μ := atomicMeasure (points g hg) w
  let : IsProbabilityMeasure μ := atomicMeasure_probability _ _ (fun i => (hw i).le) hsum
  have hsupp : μ.support = Set.range (points g hg) := atomic_support _ _ hw
  have hf : μ.support.Finite := by rw [hsupp]; exact Set.finite_range _
  have hρ1' : (ρ:ℝ) ≤ 1/4 := by
    have h := Rat.cast_le (K := ℝ).mpr hρ1
    norm_num at h ⊢
    exact h
  obtain ⟨S,hS,hsuf,_,hK⟩ := bandwise_suffix μ hf (ρ := (ρ:ℝ)) (B := (B:ℝ))
    (by exact_mod_cast hρ) hρ1' (by exact_mod_cast hB)
  let s : Fin n → Bool := fun i => decide (points g hg i ∈ S)
  have hs : suffixCheck g bands s = true := by
    simp only [suffixCheck, decide_eq_true_eq]
    intro i j hij hgj hi
    apply of_decide_eq_true at hi
    apply decide_eq_true
    apply hsuf (bands i) hi
    · rw [hsupp]; exact Set.mem_range_self j
    · exact (points_mem_band g hg i _).mpr (hb i)
    · rw [hij]; exact (points_mem_band g hg j _).mpr (hb j)
    · change (g i:ℝ) < (g j:ℝ)
      exact_mod_cast hgj
  have hrestrict : μ.restrict S = atomicMeasure (points g hg) (fun i => w i*fractions s i) := by
    rw [atomicMeasure_restrict]
    congr 1
    funext i
    simp [fractions,s]
  refine ⟨s,hs,?_⟩
  rw [hK,hrestrict,capped_objective_eq g w (fractions s) labels ρ B hg
    (fun i => (hw i).le) (fractions_valid s) hρ.le hB hl hc,
    ENNReal.toReal_ofReal (objectiveExpr_nonneg g w (fractions s) labels ρ B hρ.le
      (fun i => (hw i).le) (fractions_valid s))]

theorem selection_le_expr {n m : ℕ} (g w s : Fin n → ℚ) (labels : Fin m → ℕ)
    (ρ B : ℚ) (hg : ∀ i, 0 < g i ∧ g i ≤ 1/2) (hw : ∀ i, 0 ≤ w i)
    (hs : ∀ i, 0 ≤ s i ∧ s i ≤ 1) (hρ : 0 ≤ ρ) (hB : 0 < B)
    (hl : Function.Injective labels) (hc : ∀ i, ∃ j, inBand (g i) (labels j) = true) :
    (selection (atomicMeasure (points g hg) w) (ρ:ℝ) (B:ℝ)).toReal ≤
      (objectiveExpr g w s labels ρ B).eval := by
  have hle := le_min (selection_le_rho (atomicMeasure (points g hg) w) (ρ:ℝ) (B:ℝ))
    (selection_le_objective (selected_le (points g hg) w s hw hs) (ρ:ℝ) (B:ℝ))
  rw [capped_objective_eq g w s labels ρ B hg hw hs hρ hB hl hc] at hle
  have ht := ENNReal.toReal_mono ENNReal.ofReal_ne_top hle
  rwa [ENNReal.toReal_ofReal (objectiveExpr_nonneg g w s labels ρ B hρ hw hs)] at ht

/-- All candidate lower endpoints and one feasible upper endpoint imply a global enclosure. -/
theorem global_enclosure {α : Type*} (valid : α → Prop) (J : α → ℝ) (K : ℝ)
    (candidates : List α) (witness : α) (lower upper : ℚ)
    (hattains : ∃ s, valid s ∧ K = J s)
    (hcomplete : ∀ s, valid s → s ∈ candidates)
    (hlower : ∀ s ∈ candidates, (lower:ℝ) ≤ J s)
    (hfeasible : K ≤ J witness) (hupper : J witness ≤ (upper:ℝ)) :
    (lower:ℝ) ≤ K ∧ K ≤ J witness ∧ J witness ≤ (upper:ℝ) := by
  obtain ⟨s,hs,hK⟩ := hattains
  exact ⟨hK.symm ▸ hlower s (hcomplete s hs), hfeasible, hupper⟩

theorem global_optimality {α : Type*} (valid : α → Prop) (J : α → ℝ) (K : ℝ)
    (candidates : List α) (witness : α)
    (hattains : ∃ s, valid s ∧ K = J s)
    (hcomplete : ∀ s, valid s → s ∈ candidates)
    (hminimal : ∀ s ∈ candidates, J witness ≤ J s) (hfeasible : K ≤ J witness) :
    J witness = K := by
  obtain ⟨s,hs,hK⟩ := hattains
  exact le_antisymm (hK.symm ▸ hminimal s (hcomplete s hs)) hfeasible

theorem relative_certificate {K J : ℝ} {lo hi ε : ℚ}
    (hε : 0 ≤ ε) (h : (lo:ℝ) ≤ K ∧ K ≤ J ∧ J ≤ (hi:ℝ))
    (hstop : hi ≤ (1+ε)*lo) : J ≤ (1+(ε:ℝ))*K := by
  have h' : (hi:ℝ) ≤ (1+(ε:ℝ))*(lo:ℝ) := by exact_mod_cast hstop
  exact h.2.2.trans (h'.trans (mul_le_mul_of_nonneg_left h.1 (by exact_mod_cast (show 0 ≤ 1+ε by linarith))))

end ThresholdHC.GlobalSelectionCertificates
