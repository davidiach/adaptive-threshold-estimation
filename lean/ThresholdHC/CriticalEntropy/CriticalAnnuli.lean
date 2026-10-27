import ThresholdHC.CriticalEntropy.CriticalLaw

/-! Select good gaps by annulus averaging and charge their work to the null population. -/

noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace ThresholdHC.CriticalEntropy

/-- A positive surviving annulus contains a point whose work is controlled by
its average. No lower bound of one on the work is assumed. -/
theorem exists_good_point_low_work {μ : Measure ℝ} [IsFiniteMeasure μ]
    (G I : Set ℝ) (hG : MeasurableSet G) (hI : MeasurableSet I)
    (hpos : 0 < μ.real I) (hbad : μ.real Gᶜ ≤ μ.real I/2)
    (w : ℝ → ℝ) (hw : Integrable w μ) (hw₀ : ∀ d, 0 ≤ w d) :
    ∃ d ∈ G ∩ I, w d ≤ 4/μ.real I*(∫ x in I, w x ∂μ) := by
  have hsplit := measureReal_inter_add_sdiff (μ := μ) (s := I) hG
  have hdiff : μ.real (I \ G) ≤ μ.real Gᶜ := measureReal_mono (fun d hd => hd.2)
  have hmass : μ.real I/2 ≤ μ.real (I ∩ G) := by linarith
  have hmasspos : 0 < μ.real (I ∩ G) := by linarith
  have hne : μ.restrict (I ∩ G) ≠ 0 := by
    rw [ne_eq,Measure.restrict_eq_zero]
    intro he
    have hz : μ.real (I ∩ G) = 0 := by simp [measureReal_def,he]
    linarith
  have hn : (μ.restrict (I ∩ G)) (I ∩ G)ᶜ = 0 := by
    rw [Measure.restrict_apply (hI.inter hG).compl]
    simp
  obtain ⟨d,hd,hdw⟩ := exists_notMem_null_le_average hne hw.integrableOn hn
  have hdm : d ∈ I ∩ G := not_not.mp hd
  rw [setAverage_eq,smul_eq_mul] at hdw
  have hint : (∫ x in I ∩ G, w x ∂μ) ≤ (∫ x in I, w x ∂μ) :=
    integral_mono_measure (Measure.restrict_mono inter_subset_left le_rfl)
      (Filter.Eventually.of_forall hw₀) hw.integrableOn
  have hnonneg : 0 ≤ (∫ x in I, w x ∂μ) := integral_nonneg hw₀
  refine ⟨d,⟨hdm.2,hdm.1⟩,hdw.trans ?_⟩
  have havg : (μ.real (I ∩ G))⁻¹*(∫ x in I ∩ G, w x ∂μ) ≤
      2/μ.real I*(∫ x in I, w x ∂μ) := by
    rw [← div_eq_inv_mul,div_le_iff₀ hmasspos]
    have hscale : (∫ x in I, w x ∂μ) ≤
        2/μ.real I*(∫ x in I, w x ∂μ)*μ.real (I ∩ G) := by
      have hr : 1 ≤ 2*μ.real (I ∩ G)/μ.real I :=
        (le_div_iff₀ hpos).mpr (by linarith)
      calc
        _ = 1*(∫ x in I, w x ∂μ) := (one_mul _).symm
        _ ≤ (2*μ.real (I ∩ G)/μ.real I)*(∫ x in I, w x ∂μ) :=
          mul_le_mul_of_nonneg_right hr hnonneg
        _ = _ := by ring
    exact hint.trans hscale
  apply havg.trans
  gcongr
  norm_num

theorem criticalAnnulus_work_factor (j : ℕ) :
    (criticalUpper j)^2*(4/criticalGapLaw.real (criticalAnnulus j)) = 1/3 := by
  rw [criticalAnnulus_mass]
  have hpow : (16 : ℝ)^j = ((4 : ℝ)^j)^2 := by
    simp only [pow_two,← mul_pow]
    norm_num
  rw [hpow]
  unfold criticalUpper
  field_simp

theorem critical_annulus_work_sum (K : ℕ) (d : Fin K → ℝ)
    (w : ℝ → ℝ) (hw : Integrable w criticalGapLaw) (hw₀ : ∀ x, 0 ≤ w x)
    (hd : ∀ i, d i ∈ criticalAnnulus (i.val+3))
    (hlow : ∀ i, w (d i) ≤ 4/criticalGapLaw.real (criticalAnnulus (i.val+3))*
      (∫ x in criticalAnnulus (i.val+3), w x ∂criticalGapLaw)) :
    (∑ i, (d i)^2*w (d i)) ≤ (1/3)*(∫ x, w x ∂criticalGapLaw) := by
  have hb (i : Fin K) : (d i)^2*w (d i) ≤
      (1/3)*(∫ x in criticalAnnulus (i.val+3), w x ∂criticalGapLaw) := by
    have hd₀ : 0 ≤ d i := by
      have hp := criticalUpper_pos (i.val+3)
      have hd' := (hd i).1
      linarith
    have hsq : (d i)^2 ≤ (criticalUpper (i.val+3))^2 := by
      nlinarith [(hd i).2]
    calc
      _ ≤ (criticalUpper (i.val+3))^2*w (d i) := mul_le_mul_of_nonneg_right hsq (hw₀ _)
      _ ≤ (criticalUpper (i.val+3))^2*(4/criticalGapLaw.real (criticalAnnulus (i.val+3))*
          (∫ x in criticalAnnulus (i.val+3), w x ∂criticalGapLaw)) :=
        mul_le_mul_of_nonneg_left (hlow i) (sq_nonneg _)
      _ = _ := by rw [← mul_assoc,criticalAnnulus_work_factor]
  have hpair : Pairwise (fun i j : Fin K => Disjoint
      (criticalAnnulus (i.val+3)) (criticalAnnulus (j.val+3))) := by
    intro i j hij
    apply criticalAnnulus_disjoint
    intro he
    apply hij
    apply Fin.ext
    omega
  have he := integral_iUnion_fintype
    (μ := criticalGapLaw) (f := w) (s := fun i : Fin K => criticalAnnulus (i.val+3))
    (fun _ => measurableSet_Ioc) hpair (fun _ => hw.integrableOn)
  have hi : (∑ i : Fin K, ∫ x in criticalAnnulus (i.val+3), w x ∂criticalGapLaw) ≤
      ∫ x, w x ∂criticalGapLaw := by
    rw [← he]
    exact integral_mono_measure Measure.restrict_le_self (Filter.Eventually.of_forall hw₀) hw
  calc
    _ ≤ ∑ i : Fin K, (1/3)*(∫ x in criticalAnnulus (i.val+3), w x ∂criticalGapLaw) :=
      Finset.sum_le_sum (fun i _ => hb i)
    _ = (1/3)*∑ i : Fin K, (∫ x in criticalAnnulus (i.val+3), w x ∂criticalGapLaw) :=
      (Finset.mul_sum _ _ _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left hi (by norm_num)

theorem critical_annulus_good_points (G : Set ℝ) (hG : MeasurableSet G)
    (m : ℝ) (hbad : criticalGapLaw.real Gᶜ ≤ 70*m) (K : ℕ)
    (hmass : ∀ i : Fin K, 140*m ≤ criticalGapLaw.real (criticalAnnulus (i.val+3)))
    (w : ℝ → ℝ) (hw : Integrable w criticalGapLaw) (hw₀ : ∀ x, 0 ≤ w x) :
    ∃ d : Fin K → EntropyGap,
      (∀ i, (d i : ℝ) ∈ G ∩ criticalAnnulus (i.val+3)) ∧
      (∀ i j, j.val = i.val+1 → 2*(d j : ℝ) ≤ (d i : ℝ)) ∧
      (∑ i, (d i : ℝ)^2*w (d i)) ≤ (1/3)*(∫ x, w x ∂criticalGapLaw) := by
  have hp (i : Fin K) : 0 < criticalGapLaw.real (criticalAnnulus (i.val+3)) := by
    rw [criticalAnnulus_mass]
    positivity
  have he (i : Fin K) : ∃ x ∈ G ∩ criticalAnnulus (i.val+3),
      w x ≤ 4/criticalGapLaw.real (criticalAnnulus (i.val+3))*
        (∫ x in criticalAnnulus (i.val+3), w x ∂criticalGapLaw) :=
    exists_good_point_low_work G (criticalAnnulus (i.val+3)) hG measurableSet_Ioc
      (hp i) (by linarith [hmass i]) w hw hw₀
  choose x hx hlow using he
  have hxpos (i : Fin K) : 0 < x i := by
    have h := (hx i).2.1
    have hu := criticalUpper_pos (i.val+3)
    linarith
  have hxsmall (i : Fin K) : x i ≤ 1/128 := by
    have h := (hx i).2.2
    have hu := criticalUpper_antitone (show 3 ≤ i.val+3 by omega)
    norm_num [criticalUpper] at hu
    change criticalUpper (i.val+3) ≤ (1 : ℝ)/256 at hu
    linarith
  let d : Fin K → EntropyGap := fun i => ⟨x i,hxpos i,hxsmall i⟩
  refine ⟨d,hx,?_,?_⟩
  · intro i j hij
    exact (criticalAnnulus_adjacent (i.val+3) (x i) (x j) (hx i).2
      (by simpa [hij,Nat.add_assoc] using (hx j).2)).le
  · exact critical_annulus_work_sum K x w hw hw₀ (fun i => (hx i).2) hlow

end ThresholdHC.CriticalEntropy
