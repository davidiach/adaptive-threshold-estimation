import ThresholdHC.TwoFlipDominance.Kernel
import ThresholdHC.TwoFlipDominance.LocalForm
import ThresholdHC.TwoFlipFeedback.LowerBayes

/-! The dominance step under the almost-sure cap (`feedback.tex`, dominance
paragraph: finite words have strictly positive probability under the null).
The seeds that would request a third flip after the answers `b, b'` show that
word with positive null probability, while the almost-sure cap at the
null law `q ≡ 0` makes the event of a third flip null. So those seeds form a
null set, almost every seed stops after two flips, and the combinatorial step
puts almost every seed of a local design in the normal form. -/

noncomputable section
namespace ThresholdHC.TwoFlipDominance
open MeasureTheory
open scoped ENNReal
open ThresholdHC.Tier3 ThresholdHC.Tier6 ThresholdHC.HardBudget ThresholdHC.TwoFlipFeedback
open ThresholdHC.CriticalEntropy

/-- Seeds that request a third flip after the answers `b, b'`. -/
def thirdFlipSeeds {R : Type} [MeasurableSpace R] (A : AdaptiveEstimator R) (b b' : Bool) :
    Set R :=
  {r | A.policy r [] ≠ none ∧ A.policy r [b] ≠ none ∧ A.policy r [b, b'] ≠ none}

theorem measurableSet_thirdFlipSeeds {R : Type} [MeasurableSpace R] (A : AdaptiveEstimator R)
    (b b' : Bool) : MeasurableSet (thirdFlipSeeds A b b') := by
  have h (xs : List Bool) : MeasurableSet {r | A.policy r xs ≠ none} :=
    (A.policy_measurable xs none).compl
  exact (h []).inter ((h [b]).inter (h [b, b']))

/-- On those seeds the word `b, b'` has positive null probability. -/
theorem third_weight_pos {R : Type} [MeasurableSpace R] (A : AdaptiveEstimator R) (b b' : Bool)
    (r : R) (hr : r ∈ thirdFlipSeeds A b b') :
    0 < seedWeight twoGapLaw A nullLaw r ![some b, some b'] := by
  obtain ⟨h0, h1, _⟩ := hr
  obtain ⟨c, hc⟩ := Option.ne_none_iff_exists'.mp h0
  obtain ⟨c', hc'⟩ := Option.ne_none_iff_exists'.mp h1
  unfold seedWeight
  by_cases he : c' = c
  · subst he
    rw [weight_same twoGapLaw (A.policy r) gapValue nullLaw.val measurable_subtype_coe
      nullLaw.property.1 c' hc b hc' b' _ rfl rfl, twoBit_null]
    cases b <;> cases b' <;> norm_num [twoNull]
  · rw [weight_fresh twoGapLaw (A.policy r) gapValue nullLaw.val measurable_subtype_coe
      nullLaw.property.1 c hc b c' hc' he b' _ rfl rfl, oneBit_null, oneBit_null]
    cases b <;> cases b' <;> norm_num [oneNull]

/-- Under the almost-sure cap the seeds requesting a third flip form a null set. -/
theorem third_flip_null {R : Type} [MeasurableSpace R] (A : AdaptiveEstimator R)
    (hcap : AlmostSureCap A 2) (b b' : Bool) :
    ∀ᵐ r ∂A.randomLaw, r ∉ thirdFlipSeeds A b b' := by
  have hB := measurableSet_thirdFlipSeeds A b b'
  let w0 : Prefix 2 := ![some b, some b']
  let f : R × Prefix 2 → ℝ := fun z =>
    (thirdFlipSeeds A b b').indicator 1 z.1 * (if z.2 = w0 then 1 else 0)
  have hf : Measurable f :=
    ((measurable_one.indicator hB).comp measurable_fst).mul
      ((measurable_of_countable (fun w : Prefix 2 => if w = w0 then (1:ℝ) else 0)).comp
        measurable_snd)
  have hind (r : R) : 0 ≤ (thirdFlipSeeds A b b').indicator (1 : R → ℝ) r ∧
      (thirdFlipSeeds A b b').indicator (1 : R → ℝ) r ≤ 1 := by
    by_cases h : r ∈ thirdFlipSeeds A b b' <;> simp [h]
  have hfb (z : R × Prefix 2) : |f z| ≤ 1 := by
    have h := hind z.1
    simp only [f]
    by_cases h2 : z.2 = w0
    · simp only [h2, ite_true, mul_one]
      rw [abs_of_nonneg h.1]
      exact h.2
    · simp [h2]
  have hk := prefix_kernel_integral twoGapLaw A nullLaw f hf 1 hfb
  have hzero : ∫ z, f (z.1.1, processPrefix 2 z.2) ∂experimentLaw twoGapLaw A nullLaw = 0 := by
    apply integral_eq_zero_of_ae
    filter_upwards [ThresholdHC.StoppingProgram.original_path_valid twoGapLaw A nullLaw,
      hcap nullLaw nullLaw_rare] with z hz hw
    simp only [f, Pi.zero_apply]
    by_cases h1 : z.1.1 ∈ thirdFlipSeeds A b b'
    · by_cases h2 : processPrefix 2 z.2 = w0
      · exfalso
        have hh : processHistory z.2 2 = [b, b'] := by
          change (List.ofFn (processPrefix 2 z.2)).filterMap id = [b, b']
          rw [h2]
          simp [w0, List.ofFn_succ]
        have hne : A.policy z.1.1 (processHistory z.2 2) ≠ none := by
          rw [hh]
          exact h1.2.2
        have h3 := (ThresholdHC.StoppingProgram.valid_path_continuation_work (A.policy z.1.1)
          z.2 hz 2 hne).trans hw
        rw [show ((2:ℕ):ℝ≥0∞) = ENNReal.ofReal 2 by simp] at h3
        have h4 := (ENNReal.ofReal_le_ofReal_iff (by norm_num)).mp h3
        norm_num at h4
      · simp [h2]
    · simp [h1]
  let g : R → ℝ := fun r => ∑ w, seedWeight twoGapLaw A nullLaw r w * f (r, w)
  have hg_eq (r : R) : g r = seedWeight twoGapLaw A nullLaw r w0 *
      (thirdFlipSeeds A b b').indicator 1 r := by
    simp only [g]
    rw [Finset.sum_eq_single w0]
    · simp [f]
    · intro w _ hw
      simp [f, hw]
    · intro h
      exact absurd (Finset.mem_univ w0) h
  have hw0 (r : R) : 0 ≤ seedWeight twoGapLaw A nullLaw r w0 ∧
      seedWeight twoGapLaw A nullLaw r w0 ≤ 1 := by
    have ht := seedWeight_total twoGapLaw A nullLaw r
    refine ⟨ht.1 w0, ?_⟩
    rw [← ht.2]
    exact Finset.single_le_sum (fun w _ => ht.1 w) (Finset.mem_univ w0)
  have hg_nonneg (r : R) : 0 ≤ g r := by
    rw [hg_eq]
    exact mul_nonneg (hw0 r).1 (hind r).1
  have hg_meas : Measurable g :=
    Finset.measurable_sum _ fun w _ => (measurable_seedWeight twoGapLaw A nullLaw w).mul
      (hf.comp (measurable_id.prodMk measurable_const))
  have hg_int : Integrable g A.randomLaw := by
    refine (integrable_const (1:ℝ)).mono' hg_meas.aestronglyMeasurable (ae_of_all _ fun r => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (hg_nonneg r), hg_eq]
    have h1 := hw0 r
    have h2 := hind r
    nlinarith
  have hint : ∫ r, g r ∂A.randomLaw = 0 := hk.symm.trans hzero
  have hae := (integral_eq_zero_iff_of_nonneg hg_nonneg hg_int).mp hint
  filter_upwards [hae] with r hr hmem
  have hpos := third_weight_pos A b b' r hmem
  have e : g r = 0 := hr
  rw [hg_eq, Set.indicator_of_mem hmem] at e
  simp only [Pi.one_apply, mul_one] at e
  exact absurd e (ne_of_gt hpos)

/-- Under the almost-sure cap almost every seed stops after two flips. -/
theorem ae_depth_two {R : Type} [MeasurableSpace R] (A : AdaptiveEstimator R)
    (hcap : AlmostSureCap A 2) : ∀ᵐ r ∂A.randomLaw, StopsAtTwo (A.policy r) := by
  have h : ∀ᵐ r ∂A.randomLaw, ∀ b b' : Bool, r ∉ thirdFlipSeeds A b b' :=
    ae_all_iff.mpr fun b => ae_all_iff.mpr fun b' => third_flip_null A hcap b b'
  filter_upwards [h] with r hr b b' h0 h1
  by_contra h2
  exact hr b b' ⟨h0, h1, h2⟩

/-- The dominance step, seed-conditional form. -/
theorem seed_dominance {R : Type} [MeasurableSpace R] (A : AdaptiveEstimator R)
    (hcap : AlmostSureCap A 2) (hA : LocalAcquisition A) :
    ∀ᵐ r ∂A.randomLaw, StopsAtTwo (A.policy r) ∧ NormalAt (A.policy r) := by
  filter_upwards [ae_depth_two A hcap] with r hr
  obtain ⟨cont, hcont⟩ := hA r
  exact ⟨hr, local_normal_form (A.policy r) cont hcont hr⟩

end ThresholdHC.TwoFlipDominance
