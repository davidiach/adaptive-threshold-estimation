import ThresholdHC.EntropyTail.Bridge
import ThresholdHC.EntropyTail.Band
import ThresholdHC.EntropyTail.Objective

noncomputable section
namespace ThresholdHC.EntropyTailLower
open MeasureTheory Real Filter
open ThresholdHC.Tier6 ThresholdHC.EntropyTailQuantile
open scoped BigOperators ENNReal Topology

def selectedCanonicalBands (S : Finset ℕ) : Set Gap := ⋃ j ∈ S, ThresholdHC.EntropyTail.band j

theorem selectedCanonicalBands_measurable (S : Finset ℕ) : MeasurableSet (selectedCanonicalBands S) :=
  Finset.measurableSet_biUnion S (fun j _ => ThresholdHC.EntropyTail.measurableSet_band j)

theorem selectedCanonicalBands_inter (S : Finset ℕ) (j : ℕ) :
    ThresholdHC.EntropyTail.band j ∩ selectedCanonicalBands S =
      if j ∈ S then ThresholdHC.EntropyTail.band j else ∅ := by
  classical
  by_cases hj : j ∈ S
  · rw [ite_eq_left hj]
    apply Set.inter_eq_left.mpr
    intro d hd
    exact Set.mem_iUnion.mpr ⟨j,Set.mem_iUnion.mpr ⟨hj,hd⟩⟩
  · rw [ite_eq_right hj]
    apply Set.eq_empty_iff_forall_notMem.mpr
    rintro d ⟨hd,hu⟩
    rcases Set.mem_iUnion.mp hu with ⟨k,hk⟩
    rcases Set.mem_iUnion.mp hk with ⟨hk,hdk⟩
    have hjk : j ≠ k := by intro he; subst k; exact hj hk
    exact Set.disjoint_left.mp (ThresholdHC.EntropyTail.band_disjoint hjk) hd hdk

theorem selectedCanonicalBands_bandCost (μ : Measure Gap) (S : Finset ℕ) (j : ℕ) :
    ThresholdHC.EntropyTailQuantile.bandCost (μ.restrict (selectedCanonicalBands S)) j =
      if j ∈ S then ThresholdHC.EntropyTailQuantile.bandCost μ j else 0 := by
  classical
  unfold ThresholdHC.EntropyTailQuantile.bandCost
  rw [ThresholdHC.EntropyTail.quantile_band_eq,Measure.restrict_restrict
    (ThresholdHC.EntropyTail.measurableSet_band j),selectedCanonicalBands_inter]
  split_ifs
  · rfl
  · simp

theorem canonical_bandCost_upper (μ : Measure Gap) [IsFiniteMeasure μ] (j : ℕ) :
    ThresholdHC.EntropyTailQuantile.bandCost μ j ≤
      4*μ.real (ThresholdHC.EntropyTail.band j)/((1/2:ℝ)^(j+1))^2 := by
  let b := (1/2:ℝ)^(j+1)
  have hb : 0 < b := by dsimp [b]; positivity
  have hi := ThresholdHC.EntropyTailQuantile.band_inverseSquare_integrable μ j
  rw [ThresholdHC.EntropyTail.quantile_band_eq] at hi
  have hbound : (∫ d : Gap in ThresholdHC.EntropyTail.band j, (d:ℝ)⁻¹^2 ∂μ) ≤
      ∫ _d : Gap in ThresholdHC.EntropyTail.band j, (4/b^2:ℝ) ∂μ := by
    apply integral_mono_ae hi (integrable_const _)
    filter_upwards [ae_restrict_mem (ThresholdHC.EntropyTail.measurableSet_band j)] with d hd
    have hdb : b/2 ≤ (d:ℝ) := by
      have he : b/2 = (1/2:ℝ)^(j+2) := by dsimp [b]; rw [show j+2=(j+1)+1 by omega,pow_succ]; ring
      rw [he]
      exact hd.1.le
    have hinv : (d:ℝ)⁻¹ ≤ (b/2)⁻¹ := inv_anti₀ (by positivity) hdb
    have hsq := pow_le_pow_left₀ (inv_nonneg.mpr d.property.1.le) hinv 2
    convert hsq using 1 <;> field_simp; ring
  unfold ThresholdHC.EntropyTailQuantile.bandCost
  rw [ThresholdHC.EntropyTail.quantile_band_eq]
  calc
    _ ≤ _ := hbound
    _ = _ := by simp only [integral_const,measureReal_restrict_apply MeasurableSet.univ,
      Set.univ_inter,smul_eq_mul]; dsimp [b]; ring

theorem canonical_band_tail_upper (μ : Measure Gap) [IsFiniteMeasure μ] (h : ℝ) (hh : 0 ≤ h)
    (j : ℕ) :
    tailModulus (μ.restrict (ThresholdHC.EntropyTail.band j)) h ≤
      2*μ.real (ThresholdHC.EntropyTail.band j)*min 1 (h/((1/2:ℝ)^(j+1))) := by
  let b := (1/2:ℝ)^(j+1)
  have hb : 0 < b := by dsimp [b]; positivity
  have hbound : tailModulus (μ.restrict (ThresholdHC.EntropyTail.band j)) h ≤
      ∫ _d : Gap in ThresholdHC.EntropyTail.band j, (2*min 1 (h/b):ℝ) ∂μ := by
    apply integral_mono_ae (tailKernel_integrable _ hh) (integrable_const _)
    filter_upwards [ae_restrict_mem (ThresholdHC.EntropyTail.measurableSet_band j)] with d hd
    have hdb : b/2 ≤ (d:ℝ) := by
      have he : b/2 = (1/2:ℝ)^(j+2) := by dsimp [b]; rw [show j+2=(j+1)+1 by omega,pow_succ]; ring
      rw [he]
      exact hd.1.le
    by_cases hx : 1 ≤ h/b
    · rw [min_eq_left hx]
      exact (min_le_left _ _).trans (by norm_num)
    · rw [min_eq_right (le_of_not_ge hx)]
      apply (min_le_right _ _).trans
      apply (div_le_iff₀ d.property.1).mpr
      have hmul := mul_le_mul_of_nonneg_left hdb (div_nonneg hh hb.le)
      have he : (h/b)*(b/2) = h/2 := by field_simp [hb.ne']
      rw [he] at hmul
      nlinarith only [hmul]
  calc
    _ ≤ _ := hbound
    _ = _ := by simp only [integral_const,measureReal_restrict_apply MeasurableSet.univ,
      Set.univ_inter,smul_eq_mul]; dsimp [b]; ring

theorem canonical_prefix_remainder_tendsto_zero (μ : Measure Gap) [IsFiniteMeasure μ] :
    Tendsto (fun n : ℕ => μ ((selectedCanonicalBands (Finset.range n))ᶜ)) atTop (𝓝 0) := by
  have hmono : Monotone (fun n : ℕ => selectedCanonicalBands (Finset.range n)) := by
    intro n m hnm d hd
    rcases Set.mem_iUnion.mp hd with ⟨j,hj⟩
    rcases Set.mem_iUnion.mp hj with ⟨hj,hdj⟩
    exact Set.mem_iUnion.mpr ⟨j,Set.mem_iUnion.mpr ⟨Finset.mem_range.mpr
      ((Finset.mem_range.mp hj).trans_le hnm),hdj⟩⟩
  have hanti : Antitone (fun n : ℕ => (selectedCanonicalBands (Finset.range n))ᶜ) :=
    fun _ _ h => Set.compl_subset_compl.mpr (hmono h)
  have hempty : (⋂ n : ℕ, (selectedCanonicalBands (Finset.range n))ᶜ) = (∅ : Set Gap) := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro d hd
    obtain ⟨j,hj⟩ := ThresholdHC.EntropyTail.exists_band d
    have hn := Set.mem_iInter.mp hd (j+1)
    apply hn
    exact Set.mem_iUnion.mpr ⟨j,Set.mem_iUnion.mpr ⟨Finset.mem_range.mpr (by omega),hj⟩⟩
  have ht := tendsto_measure_iInter_atTop
    (fun n => (selectedCanonicalBands_measurable (Finset.range n)).compl.nullMeasurableSet)
    hanti ⟨0,measure_ne_top μ _⟩
  simpa only [hempty,measure_empty,Function.comp_def] using ht

theorem selectedCanonicalBands_gamma_upper (μ : Measure Gap) [IsFiniteMeasure μ]
    (n : ℕ) (S : Finset ℕ) (hS : ∀ j ∈ S, j < n) :
    ThresholdHC.EntropyTail.gamma (μ.restrict (selectedCanonicalBands S)) ≤
      ENNReal.ofReal (4*costEntropy (fun i : Fin n => if i.val ∈ S then
        μ.real (ThresholdHC.EntropyTail.band i.val)/((1/2:ℝ)^(i.val+1))^2 else 0)) := by
  classical
  let ν := μ.restrict (selectedCanonicalBands S)
  have hz (j : ℕ) (hj : n ≤ j) : ThresholdHC.EntropyTailQuantile.bandCost ν j = 0 := by
    have hjS : j ∉ S := by intro h; have := hS j h; omega
    exact (selectedCanonicalBands_bandCost μ S j).trans (ite_eq_right hjS)
  have hp : measureCostEntropy ν ≤ ENNReal.ofReal
      (costEntropy (fun i : Fin n => ThresholdHC.EntropyTailQuantile.bandCost ν i)) := by
    apply iSup_le
    intro m
    exact ENNReal.ofReal_le_ofReal (costEntropy_prefix_le_of_eventually_zero
      (ThresholdHC.EntropyTailQuantile.bandCost_nonneg ν) hz m)
  have hi (i : Fin n) : ThresholdHC.EntropyTailQuantile.bandCost ν i ≤
      4*(if i.val ∈ S then μ.real (ThresholdHC.EntropyTail.band i.val)/
        ((1/2:ℝ)^(i.val+1))^2 else 0) := by
    rw [selectedCanonicalBands_bandCost]
    by_cases hi : i.val ∈ S
    · simp only [hi,ite_true]
      convert canonical_bandCost_upper μ i using 1 <;> ring
    · simp [hi]
  have he := costEntropy_mono (fun i : Fin n => ThresholdHC.EntropyTailQuantile.bandCost_nonneg ν i) hi
  rw [costEntropy_smul] at he
  exact (ThresholdHC.EntropyTail.gamma_le_quantile_measureCostEntropy ν).trans
    (hp.trans (ENNReal.ofReal_le_ofReal he))

theorem selectedCanonicalBands_tail_sum (μ : Measure Gap) [IsFiniteMeasure μ]
    (S : Finset ℕ) (h : ℝ) (hh : 0 ≤ h) :
    tailModulus (μ.restrict (selectedCanonicalBands S)) h =
      ∑ j ∈ S, tailModulus (μ.restrict (ThresholdHC.EntropyTail.band j)) h := by
  classical
  unfold tailModulus selectedCanonicalBands
  exact integral_biUnion_finset S
    (fun j _ => ThresholdHC.EntropyTail.measurableSet_band j)
    (fun _ _ _ _ hij => ThresholdHC.EntropyTail.band_disjoint hij)
    (fun _ _ => (tailKernel_integrable μ hh).integrableOn)

theorem canonical_selected_tail_upper (μ : Measure Gap) [IsFiniteMeasure μ]
    (n : ℕ) (S : Finset ℕ) (h : ℝ) (hh : 0 ≤ h) :
    tailModulus (μ-μ.restrict (selectedCanonicalBands S)) h ≤
      2*(∑ j ∈ Finset.range n, if j ∈ S then 0 else
        μ.real (ThresholdHC.EntropyTail.band j)*min 1 (h/((1/2:ℝ)^(j+1)))) +
      μ.real ((selectedCanonicalBands (Finset.range n))ᶜ) := by
  classical
  let U := selectedCanonicalBands S
  let V := selectedCanonicalBands (Finset.range n \ S)
  let W := (selectedCanonicalBands (Finset.range n))ᶜ
  have hsub : Uᶜ ⊆ V ∪ W := by
    intro d hd
    by_cases hp : d ∈ selectedCanonicalBands (Finset.range n)
    · apply Or.inl
      rcases Set.mem_iUnion.mp hp with ⟨j,hj⟩
      rcases Set.mem_iUnion.mp hj with ⟨hj,hdj⟩
      have hjS : j ∉ S := by
        intro h
        exact hd (Set.mem_iUnion.mpr ⟨j,Set.mem_iUnion.mpr ⟨h,hdj⟩⟩)
      exact Set.mem_iUnion.mpr ⟨j,Set.mem_iUnion.mpr ⟨Finset.mem_sdiff.mpr ⟨hj,hjS⟩,hdj⟩⟩
    · exact Or.inr hp
  have hmeasure : μ-μ.restrict U ≤ μ.restrict V+μ.restrict W := by
    apply le_trans (Measure.sub_le_of_le_add
      (Measure.restrict_compl_add_restrict (selectedCanonicalBands_measurable S)).ge)
    exact (Measure.restrict_mono hsub le_rfl).trans (Measure.restrict_union_le _ _)
  have htail := tailModulus_mono hmeasure hh
  rw [tailModulus_add _ _ hh] at htail
  have hmass := tailModulus_le_mass (μ.restrict W) hh
  rw [measureReal_restrict_apply MeasurableSet.univ,Set.univ_inter] at hmass
  have hV : tailModulus (μ.restrict V) h ≤
      2*∑ j ∈ Finset.range n, if j ∈ S then 0 else
        μ.real (ThresholdHC.EntropyTail.band j)*min 1 (h/((1/2:ℝ)^(j+1))) := by
    rw [selectedCanonicalBands_tail_sum μ _ h hh]
    have hs := Finset.sum_le_sum (s := Finset.range n \ S)
      (fun j _ => canonical_band_tail_upper μ h hh j)
    have he : (Finset.range n \ S) = (Finset.range n).filter (fun j => j ∉ S) := by
      ext j; simp
    refine hs.trans_eq ?_
    rw [he,Finset.sum_filter,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    by_cases hj : j ∈ S <;> simp [hj,mul_assoc]
  exact htail.trans (add_le_add hV hmass)

end ThresholdHC.EntropyTailLower
