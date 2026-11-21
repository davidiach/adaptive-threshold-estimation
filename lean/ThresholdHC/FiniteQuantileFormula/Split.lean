import ThresholdHC.FiniteQuantileFormula.Atoms
import ThresholdHC.EntropyTailQuantile.CutDecomposition

/-! The quantile split fg:eq:quantile-split of a finite law. The split index `k`
is the first atom whose cumulative weight reaches `ρ`; the general-law threshold
is `d k`, the boundary fraction is `(ρ - ∑_{ℓ<k} w_ℓ)/w_k`, and the general-law
tail and core are the atomic measures with weights `τ_i` and `w_i - τ_i`. -/

noncomputable section
open MeasureTheory
open scoped ENNReal BigOperators Classical
namespace ThresholdHC.FiniteQuantileFormula
open ThresholdHC.Tier6 ThresholdHC.EntropyTailQuantile

variable {n : ℕ}

theorem sum_Iic_eq (w : Fin n → ℝ) (i : Fin n) :
    ∑ l ∈ Finset.Iic i, w l = ∑ l ∈ Finset.Iio i, w l + w i := by
  rw [← Finset.Iio_insert, Finset.sum_insert Finset.notMem_Iio_self, add_comm]

theorem split_exists (w : Fin n → ℝ) (hw : ∀ i, 0 ≤ w i) (hsum : ∑ i, w i = 1)
    {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) :
    ∃ k : Fin n, ∑ l ∈ Finset.Iio k, w l < ρ ∧ ρ ≤ ∑ l ∈ Finset.Iic k, w l := by
  have hne : (Finset.univ : Finset (Fin n)).Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty] at h
    rw [h, Finset.sum_empty] at hsum
    exact zero_ne_one hsum
  let m := Finset.univ.max' hne
  have hm : ρ ≤ ∑ l ∈ Finset.Iic m, w l := by
    have he : Finset.Iic m = Finset.univ := by
      ext l
      simp only [Finset.mem_Iic, Finset.mem_univ, iff_true]
      exact Finset.le_max' _ l (Finset.mem_univ l)
    rw [he, hsum]
    exact hρ1
  let P := Finset.univ.filter (fun i : Fin n => ρ ≤ ∑ l ∈ Finset.Iic i, w l)
  have hP : P.Nonempty := ⟨m, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hm⟩⟩
  let k := P.min' hP
  have hk : k ∈ P := P.min'_mem hP
  refine ⟨k, ?_, (Finset.mem_filter.mp hk).2⟩
  by_cases hI : (Finset.Iio k).Nonempty
  · let j := (Finset.Iio k).max' hI
    have hj : j < k := Finset.mem_Iio.mp ((Finset.Iio k).max'_mem hI)
    have hjP : j ∉ P := fun h => (not_le_of_gt hj) (P.min'_le j h)
    have hsub : Finset.Iio k ⊆ Finset.Iic j := fun l hl =>
      Finset.mem_Iic.mpr ((Finset.Iio k).le_max' l hl)
    have hle := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun l _ _ => hw l)
    have hlt : ∑ l ∈ Finset.Iic j, w l < ρ := by
      by_contra h
      exact hjP (Finset.mem_filter.mpr ⟨Finset.mem_univ _, le_of_not_gt h⟩)
    exact hle.trans_lt hlt
  · rw [Finset.not_nonempty_iff_eq_empty] at hI
    rw [hI, Finset.sum_empty]
    exact hρ

theorem tailWeight_nonneg (w : Fin n → ℝ) (hw : ∀ i, 0 ≤ w i) (ρ : ℝ) (i : Fin n) :
    0 ≤ tailWeight w ρ i := le_min (hw i) (le_max_right _ _)

theorem tailWeight_le (w : Fin n → ℝ) (ρ : ℝ) (i : Fin n) : tailWeight w ρ i ≤ w i :=
  min_le_left _ _

theorem tailWeight_of_lt (w : Fin n → ℝ) (hw : ∀ i, 0 ≤ w i) {ρ : ℝ} {k i : Fin n}
    (hk : ∑ l ∈ Finset.Iio k, w l < ρ) (hi : i < k) : tailWeight w ρ i = w i := by
  have hsub : Finset.Iic i ⊆ Finset.Iio k := fun l hl =>
    Finset.mem_Iio.mpr ((Finset.mem_Iic.mp hl).trans_lt hi)
  have hle := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun l _ _ => hw l)
  rw [sum_Iic_eq] at hle
  unfold tailWeight
  rw [max_eq_left (by linarith [hw i]), min_eq_left (by linarith)]

theorem tailWeight_self (w : Fin n → ℝ) {ρ : ℝ} {k : Fin n}
    (hk : ∑ l ∈ Finset.Iio k, w l < ρ) (hk' : ρ ≤ ∑ l ∈ Finset.Iic k, w l) :
    tailWeight w ρ k = ρ - ∑ l ∈ Finset.Iio k, w l := by
  rw [sum_Iic_eq] at hk'
  unfold tailWeight
  rw [max_eq_left (by linarith), min_eq_right (by linarith)]

theorem tailWeight_of_gt (w : Fin n → ℝ) (hw : ∀ i, 0 ≤ w i) {ρ : ℝ} {k i : Fin n}
    (hk' : ρ ≤ ∑ l ∈ Finset.Iic k, w l) (hi : k < i) : tailWeight w ρ i = 0 := by
  have hsub : Finset.Iic k ⊆ Finset.Iio i := fun l hl =>
    Finset.mem_Iio.mpr ((Finset.mem_Iic.mp hl).trans_lt hi)
  have hle := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun l _ _ => hw l)
  unfold tailWeight
  rw [max_eq_right (by linarith), min_eq_right (hw i)]

/-- Copy of `FiniteLawCertificates.quantileThreshold_eq_of_mass`. -/
theorem threshold_eq_of_mass (μ : Measure Gap) [IsProbabilityMeasure μ]
    {ρ t : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (hbelow : μ.real {x : Gap | (x:ℝ) < t} < ρ)
    (habove : ρ ≤ μ.real {x : Gap | (x:ℝ) ≤ t}) :
    quantileThreshold μ ρ = t := by
  have hp := quantileThreshold_properties μ hρ hρ1
  apply le_antisymm
  · by_contra h
    exact (not_lt_of_ge habove) (hp.2.2.2 t (lt_of_not_ge h))
  · by_contra h
    have ht : quantileThreshold μ ρ < t := lt_of_not_ge h
    have hm : μ.real {x : Gap | (x:ℝ) ≤ quantileThreshold μ ρ} ≤
        μ.real {x : Gap | (x:ℝ) < t} :=
      measureReal_mono (fun x hx => hx.trans_lt ht)
    exact (not_le_of_gt hbelow) (hp.2.2.1.trans hm)

private theorem ite_weight_nonneg {w : Fin n → ℝ} (hw : ∀ i, 0 ≤ w i) (i : Fin n) (c : Prop)
    {_ : Decidable c} : 0 ≤ (if c then w i else 0) := by
  split_ifs
  · exact hw i
  · exact le_rfl

theorem finite_split (d : Fin n → Gap) (w : Fin n → ℝ) (μ : Measure Gap)
    [IsProbabilityMeasure μ] (hd : StrictMono (fun i => (d i : ℝ))) (hw : ∀ i, 0 < w i)
    (hsum : ∑ i, w i = 1) (hμ : μ = ∑ i, ENNReal.ofReal (w i) • Measure.dirac (d i))
    {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) :
    ∃ k : Fin n, quantileThreshold μ ρ = d k ∧
      quantileTail μ ρ = ∑ i, ENNReal.ofReal (tailWeight w ρ i) • Measure.dirac (d i) ∧
      quantileCore μ ρ =
        ∑ i, ENNReal.ofReal (w i - tailWeight w ρ i) • Measure.dirac (d i) := by
  have hw0 : ∀ i, 0 ≤ w i := fun i => (hw i).le
  obtain ⟨k, hk, hk'⟩ := split_exists w hw0 hsum hρ hρ1
  have hlt : ∀ a b : Fin n, (d a : ℝ) < d b ↔ a < b := fun a b => hd.lt_iff_lt
  have hle : ∀ a b : Fin n, (d a : ℝ) ≤ d b ↔ a ≤ b := fun a b => hd.le_iff_le
  have heq : ∀ a b : Fin n, (d a : ℝ) = d b ↔ a = b := fun a b => hd.injective.eq_iff
  have hlt' : ∀ a b : Fin n, d a < d b ↔ a < b := fun a b => Subtype.coe_lt_coe.symm.trans (hlt a b)
  have hle' : ∀ a b : Fin n, d a ≤ d b ↔ a ≤ b := fun a b => Subtype.coe_le_coe.symm.trans (hle a b)
  subst hμ
  have hmlt : (∑ i, ENNReal.ofReal (w i) • Measure.dirac (d i)).real
      {x : Gap | (x:ℝ) < d k} = ∑ l ∈ Finset.Iio k, w l := by
    rw [atoms_real d w hw0, ← Finset.sum_filter]
    apply Finset.sum_congr _ (fun _ _ => rfl)
    ext i
    simp [hlt']
  have hmle : (∑ i, ENNReal.ofReal (w i) • Measure.dirac (d i)).real
      {x : Gap | (x:ℝ) ≤ d k} = ∑ l ∈ Finset.Iic k, w l := by
    rw [atoms_real d w hw0, ← Finset.sum_filter]
    apply Finset.sum_congr _ (fun _ _ => rfl)
    ext i
    simp [hle']
  have hmeq : (∑ i, ENNReal.ofReal (w i) • Measure.dirac (d i)).real
      {x : Gap | (x:ℝ) = d k} = w k := by
    rw [atoms_real d w hw0]
    simp [heq]
  have ht : quantileThreshold (∑ i, ENNReal.ofReal (w i) • Measure.dirac (d i)) ρ = d k :=
    threshold_eq_of_mass _ hρ hρ1 (hmlt ▸ hk) (hmle ▸ hk')
  have hb : quantileBoundaryFraction (∑ i, ENNReal.ofReal (w i) • Measure.dirac (d i)) ρ =
      (ρ - ∑ l ∈ Finset.Iio k, w l) / w k := by
    unfold quantileBoundaryFraction
    rw [ht, hmlt, hmeq]
  have hk2 := hk'
  rw [sum_Iic_eq] at hk2
  have hr0 : 0 ≤ (ρ - ∑ l ∈ Finset.Iio k, w l) / w k :=
    div_nonneg (by linarith) (hw0 k)
  have hr1 : (ρ - ∑ l ∈ Finset.Iio k, w l) / w k ≤ 1 :=
    (div_le_one (hw k)).mpr (by linarith)
  have hrw : (ρ - ∑ l ∈ Finset.Iio k, w l) / w k * w k = ρ - ∑ l ∈ Finset.Iio k, w l :=
    div_mul_cancel₀ _ (hw k).ne'
  have hτk := tailWeight_self w hk hk'
  refine ⟨k, ht, ?_, ?_⟩
  · unfold quantileTail
    rw [ht, hb, atoms_restrict, atoms_restrict, atoms_smul _ _ hr0, atoms_add]
    rotate_left
    · exact fun i => ite_weight_nonneg hw0 i _
    · exact fun i => mul_nonneg hr0 (ite_weight_nonneg hw0 i _)
    apply Finset.sum_congr rfl
    intro i _
    refine congrArg (fun x => ENNReal.ofReal x • Measure.dirac (d i)) ?_
    rcases lt_trichotomy i k with h | h | h
    · simp [hlt', heq, h, h.ne, tailWeight_of_lt w hw0 hk h]
    · subst h
      simp [hτk, hrw]
    · simp [hlt', heq, h.ne', not_lt_of_gt h, tailWeight_of_gt w hw0 hk' h]
  · rw [quantileCore_eq_upperCut _ hρ hρ1, ht, hb, upperCut, atoms_restrict, atoms_restrict,
      atoms_smul _ _ (sub_nonneg.mpr hr1), atoms_add]
    rotate_left
    · exact fun i => ite_weight_nonneg hw0 i _
    · exact fun i => mul_nonneg (sub_nonneg.mpr hr1) (ite_weight_nonneg hw0 i _)
    apply Finset.sum_congr rfl
    intro i _
    refine congrArg (fun x => ENNReal.ofReal x • Measure.dirac (d i)) ?_
    rcases lt_trichotomy i k with h | h | h
    · simp [hlt', heq, h.ne, not_lt_of_gt h, tailWeight_of_lt w hw0 hk h]
    · subst h
      simp only [lt_self_iff_false, ite_false, Set.mem_ofPred_eq, ite_true, zero_add, hτk]
      linarith
    · simp [hlt', heq, h, h.ne', tailWeight_of_gt w hw0 hk' h]

end ThresholdHC.FiniteQuantileFormula
