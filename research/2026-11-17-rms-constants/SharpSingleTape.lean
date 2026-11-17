import SharpTapeMixture

/-! The sign-independent causal channel has the exact heterogeneous one-coin law. -/
noncomputable section
namespace ThresholdHC.SharpRMS
open MeasureTheory ProbabilityTheory Set Tier6 CriticalEntropy ObservableSimulation
open scoped ENNReal

def sourceTarget (g : Gap) (q : SignLaw) : SignLaw :=
  attenuatedSign g.val (2*q.val g-1) g.property.1.le
    (abs_le.mpr ⟨by linarith [(q.property.2 g).1],by linarith [(q.property.2 g).2]⟩)

theorem source_target_mean (μ : Measure Gap) [IsProbabilityMeasure μ] (g : Gap) (q : SignLaw) :
    signMean μ (sourceTarget g q).val = (1+(2*q.val g-1)*modulus μ g.val)/2 :=
  attenuated_target ..

private theorem original_set (μ : Measure Gap) [IsProbabilityMeasure μ] (q : SignLaw)
    (S : Set (ℕ → Bool)) (hs : MeasurableSet S) :
    originalPopulationTapeLaw μ q S = ∫⁻ d, ENNReal.ofReal (q.val d)*Tier2.tapeMeasure (gapParameter true d) S+
        ENNReal.ofReal (1-q.val d)*Tier2.tapeMeasure (gapParameter false d) S ∂μ := by
  simpa only [lintegral_indicator_one hs] using original_tape_lintegral μ q (S.indicator 1) (measurable_one.indicator hs)

private theorem original_dirac (g : Gap) (q : SignLaw) :
    originalPopulationTapeLaw (Measure.dirac g) q =
    ENNReal.ofReal (q.val g) • Tier2.tapeMeasure (gapParameter true g) +
    ENNReal.ofReal (1-q.val g) • Tier2.tapeMeasure (gapParameter false g) := by
  ext S hs
  rw [original_set _ q S hs,lintegral_dirac]
  rfl

private theorem pure_word (d g : Gap) (e : Bool) (w : List Bool) :
    (uniformTapeMeasure.prod (Tier2.tapeMeasure (gapParameter e g))) (virtualEvent d g 0 0 w) =
    ENNReal.ofReal (conditionalWord (2*d.val) (clippedGap g.val d) (observedSign e) (w.count true) (w.count false)) := by
  have f : min 1 ((2*g.val)/(2*d.val))=clippedGap g.val d := by
    unfold clippedGap
    rw [mul_div_mul_left _ _ (by norm_num : (2:ℝ) ≠ 0)]
  have h := virtual_word_probability d g e w 0 0
  dsimp only at h
  rw [f] at h
  have one : conditionalWord (2*d.val) (clippedGap g.val d) (observedSign e) 0 0 = 1 := by
    simp [conditionalWord,wordMass]
    ring
  simpa only [one,ENNReal.ofReal_one,one_mul,Nat.zero_add] using h

private theorem mixed_word (d g : Gap) (q : SignLaw) (w : List Bool) :
    (uniformTapeMeasure.prod (originalPopulationTapeLaw (Measure.dirac g) q)) (virtualEvent d g 0 0 w) =
    ENNReal.ofReal ((sourceTarget g q).val d)*Tier2.tapeMeasure (gapParameter true d) {x | begins w x}+
    ENNReal.ofReal (1-(sourceTarget g q).val d)*Tier2.tapeMeasure (gapParameter false d) {x | begins w x} := by
  rw [original_dirac,Measure.prod_add,Measure.prod_smul_right,Measure.prod_smul_right,
      Measure.add_apply,Measure.smul_apply,Measure.smul_apply]
  simp only [smul_eq_mul,pure_word,iid_word]
  let A := wordMass ((1+2*d.val)/2) (w.count true) (w.count false)
  let C := wordMass ((1-2*d.val)/2) (w.count true) (w.count false)
  let f := clippedGap g.val d
  let r := q.val g
  let c := (1+(2*r-1)*f)/2
  have p : (gapParameter true d).val = (1+2*d.val)/2 := by simp [gapParameter]; ring
  have n : (gapParameter false d).val = (1-2*d.val)/2 := by simp [gapParameter]; ring
  have pos (p : unitInterval) : 0 ≤ wordMass p.val (w.count true) (w.count false) :=
    mul_nonneg (pow_nonneg p.property.1 _) (pow_nonneg (sub_nonneg.mpr p.property.2) _)
  have ha : 0 ≤ A := by simpa only [A,←p] using pos (gapParameter true d)
  have hc : 0 ≤ C := by simpa only [C,←n] using pos (gapParameter false d)
  have hf : 0 ≤ f := le_min zero_le_one (div_nonneg g.property.1.le d.property.1.le)
  have hf' : f ≤ 1 := min_le_left ..
  have hr := q.property.2 g
  have ht := (sourceTarget g q).property.2 d
  change c ∈ Icc 0 1 at ht
  rw [p,n]
  change ENNReal.ofReal r * ENNReal.ofReal (((1+f*1)/2)*A+((1-f*1)/2)*C) +
         ENNReal.ofReal (1-r) * ENNReal.ofReal (((1+f*(-1))/2)*A+((1-f*(-1))/2)*C) =
         ENNReal.ofReal c * ENNReal.ofReal A + ENNReal.ofReal (1-c) * ENNReal.ofReal C
  have hp : 0 ≤ (1+f)/2 := by linarith
  have hn : 0 ≤ (1-f)/2 := by linarith
  have hr0 : 0 ≤ r := hr.1
  have hr1 : 0 ≤ 1-r := sub_nonneg.mpr hr.2
  simp only [mul_one,mul_neg_one,sub_neg_eq_add,←sub_eq_add_neg]
  rw [←ENNReal.ofReal_mul hr0,←ENNReal.ofReal_mul hr1,←ENNReal.ofReal_mul ht.1,←ENNReal.ofReal_mul (sub_nonneg.mpr ht.2),
      ←ENNReal.ofReal_add (mul_nonneg hr0 (add_nonneg (mul_nonneg hp ha) (mul_nonneg hn hc)))
        (mul_nonneg hr1 (add_nonneg (mul_nonneg hn ha) (mul_nonneg hp hc))),
      ←ENNReal.ofReal_add (mul_nonneg ht.1 ha) (mul_nonneg (sub_nonneg.mpr ht.2) hc)]
  congr 1
  dsimp [c]
  ring

theorem single_tape_law (μ : Measure Gap) [IsProbabilityMeasure μ] (g : Gap) (q : SignLaw) :
    ((μ.prod uniformTapeMeasure).prod (originalPopulationTapeLaw (Measure.dirac g) q)).map
       (fun z => virtualTape z.1.1 g 0 0 z.1.2 z.2) = originalPopulationTapeLaw μ (sourceTarget g q) := by
  let T := originalPopulationTapeLaw (Measure.dirac g) q
  let V := fun z : (Gap × (ℕ → ℝ)) × (ℕ → Bool) => virtualTape z.1.1 g 0 0 z.1.2 z.2
  have mv : Measurable V := measurable_virtualTape_joint g 0 0
  let e := MeasurableEquiv.prodAssoc (α:=Gap) (β:=ℕ → ℝ) (γ:=ℕ → Bool)
  have mp := measurePreserving_prodAssoc μ uniformTapeMeasure T
  apply tape_ext_words
  intro w
  let S := {x | begins w x}
  have hs : MeasurableSet S := measurable_begins w
  let E := (V ∘ e.symm) ⁻¹' S
  have he : MeasurableSet E := hs.preimage (mv.comp e.symm.measurable)
  change (((μ.prod uniformTapeMeasure).prod T).map V) S = _
  rw [Measure.map_apply mv hs]
  change ((μ.prod uniformTapeMeasure).prod T) (e ⁻¹' E) = _
  rw [mp.measure_preimage he.nullMeasurableSet,Measure.prod_apply he,original_set μ (sourceTarget g q) S hs]
  exact lintegral_congr (fun d => mixed_word d g q w)

end ThresholdHC.SharpRMS
