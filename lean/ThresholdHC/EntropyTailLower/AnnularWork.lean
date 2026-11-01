import ThresholdHC.EntropyTailLower.WeightedSign

/-! General annular averaging for the entropy-tail lower proof.
The measure and the positive annular masses are arbitrary; no quadratic
population law or equal cost weights are assumed. -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace ThresholdHC.EntropyTailLower
open ThresholdHC.CriticalEntropy

theorem exists_point_below_annular_average {D : Type*} [MeasurableSpace D]
    {μ : Measure D} [IsFiniteMeasure μ]
    (G I : Set D) (hG : MeasurableSet G) (hI : MeasurableSet I)
    (hpos : 0 < μ.real I) (hbad : μ.real Gᶜ ≤ μ.real I/2)
    (w : D → ℝ) (hw : Integrable w μ) (hw0 : ∀ d, 0 ≤ w d) :
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
      (Filter.Eventually.of_forall hw0) hw.integrableOn
  have hnonneg : 0 ≤ (∫ x in I, w x ∂μ) := integral_nonneg hw0
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

theorem annular_work_sum (μ : Measure EntropyGap) [IsFiniteMeasure μ]
    {K : ℕ} (I : Fin K → Set EntropyGap) (b : Fin K → ℝ)
    (hb : ∀ i, 0 < b i) (hI : ∀ i, MeasurableSet (I i))
    (hdisjoint : Pairwise (fun i j => Disjoint (I i) (I j)))
    (hmass : ∀ i, 0 < μ.real (I i))
    (d : Fin K → EntropyGap) (hd : ∀ i, (d i:ℝ) ≤ b i)
    (w : EntropyGap → ℝ) (hw : Integrable w μ) (hw0 : ∀ x, 0 ≤ w x)
    (hlow : ∀ i, w (d i) ≤ 4/μ.real (I i)*(∫ x in I i, w x ∂μ)) :
    (∑ i, (μ.real (I i)/(b i)^2)*((d i:ℝ)^2*w (d i))) ≤ 4*(∫ x, w x ∂μ) := by
  have hterm (i : Fin K) : (μ.real (I i)/(b i)^2)*((d i:ℝ)^2*w (d i)) ≤
      4*(∫ x in I i, w x ∂μ) := by
    have hsq := (sq_le_sq₀ (d i).property.1.le (hb i).le).mpr (hd i)
    calc
      _ ≤ (μ.real (I i)/(b i)^2)*((b i)^2*w (d i)) := by gcongr; exact hw0 _
      _ ≤ (μ.real (I i)/(b i)^2)*((b i)^2*
          (4/μ.real (I i)*(∫ x in I i, w x ∂μ))) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact mul_le_mul_of_nonneg_left (hlow i) (sq_nonneg _)
      _ = _ := by field_simp [(hb i).ne', (hmass i).ne']
  have he := integral_iUnion_fintype (μ := μ) (f := w) hI hdisjoint (fun _ => hw.integrableOn)
  have htotal : (∑ i, ∫ x in I i, w x ∂μ) ≤ ∫ x, w x ∂μ := by
    rw [← he]
    exact integral_mono_measure Measure.restrict_le_self (Filter.Eventually.of_forall hw0) hw
  calc
    _ ≤ ∑ i, 4*(∫ x in I i, w x ∂μ) := Finset.sum_le_sum (fun i _ => hterm i)
    _ = 4*∑ i, ∫ x in I i, w x ∂μ := (Finset.mul_sum _ _ _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left htotal (by norm_num)

/-- A common observable sign test must pay the full cost entropy of any
separated annular family on which at least half of every band is good. -/
theorem annular_sign_entropy {R : Type} [MeasurableSpace R]
    (ν : Measure R) [IsProbabilityMeasure ν] (A : SignTest R)
    (μ : Measure EntropyGap) [IsFiniteMeasure μ]
    {K : ℕ} (I : Fin K → Set EntropyGap) (b : Fin K → ℝ)
    (hb : ∀ i, 0 < b i) (hI : ∀ i, MeasurableSet (I i))
    (hdisjoint : Pairwise (fun i j => Disjoint (I i) (I j)))
    (hmass : ∀ i, 0 < μ.real (I i))
    (hband : ∀ i d, d ∈ I i → b i/2 < (d:ℝ) ∧ (d:ℝ) ≤ b i)
    (hsep : ∀ i j, j.val = i.val+1 → 4*b j ≤ b i)
    (G : Set EntropyGap) (hG : MeasurableSet G)
    (hbad : ∀ i, μ.real Gᶜ ≤ μ.real (I i)/2)
    (hw : Integrable (fun d : EntropyGap =>
      (expectedSignTestWork ν (signParameter d false) A).toReal) μ)
    (hfinite : ∀ d ∈ G, expectedSignTestWork ν (signParameter d false) A ≠ ∞)
    (herror : ∀ d ∈ G, ∀ s, (ν.prod (Tier2.tapeMeasure (signParameter d s))).real
      {z | A.output z ≠ s} ≤ 1/10) :
    ThresholdHC.EntropyTailQuantile.costEntropy (fun i => μ.real (I i)/(b i)^2) ≤
      16384*(∫ d : EntropyGap, (expectedSignTestWork ν (signParameter d false) A).toReal ∂μ) := by
  classical
  let w := fun d : EntropyGap => (expectedSignTestWork ν (signParameter d false) A).toReal
  have hw0 : ∀ d, 0 ≤ w d := fun _ => ENNReal.toReal_nonneg
  have hp (i : Fin K) := exists_point_below_annular_average G (I i) hG (hI i)
    (hmass i) (hbad i) w hw hw0
  choose d hd hlow using hp
  have hgap : ∀ i j, j.val = i.val+1 → 2*(d j:ℝ) ≤ (d i:ℝ) := by
    intro i j hij
    have hi := hband i (d i) (hd i).2
    have hj := hband j (d j) (hd j).2
    linarith [hsep i j hij]
  have hs := weighted_sign_entropy ν A K d hgap (fun i => hfinite _ (hd i).1)
    (fun i => herror _ (hd i).1) (fun i => μ.real (I i)/(b i)^2) (fun i => by positivity)
  have hsum := annular_work_sum μ I b hb hI hdisjoint hmass d
    (fun i => (hband i (d i) (hd i).2).2) w hw hw0 hlow
  exact hs.trans (by nlinarith)

end ThresholdHC.EntropyTailLower
