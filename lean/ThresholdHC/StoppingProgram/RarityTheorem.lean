import ThresholdHC.StoppingProgram.FractionalCutoff

/-! The complete fractional upper-tail support formula, with an actual
globally rare optimizer and a cutoff in the bounded positive range. -/

noncomputable section
open MeasureTheory Set
open scoped ENNReal

namespace ThresholdHC.StoppingProgram
open ThresholdHC.Tier6 (Gap SignLaw signMean)
open ThresholdHC.RareAboveTwo

theorem rareFunctional_eq_sSup (μ : Measure Gap) (ρ : ℝ) (f : Gap → ℝ) :
    rareFunctional μ ρ f = sSup {r : ℝ | ∃ q : SignLaw, RarePrior μ ρ q ∧ r = ∫ d, q.val d*f d ∂μ} := by
  unfold rareFunctional compactMaximum
  congr 1
  ext r
  constructor
  · rintro ⟨u,⟨q,hq,hu⟩,rfl⟩
    exact ⟨q,hq,by simpa only [add_zero] using hu ()⟩
  · rintro ⟨q,hq,rfl⟩
    refine ⟨fun _ : Unit => ∫ d, q.val d*f d ∂μ,⟨q,hq,fun _ => by simp⟩,rfl⟩

theorem fractional_rarity_support_of_memLp (μ : Measure Gap) [IsProbabilityMeasure μ]
    {ρ M : ℝ} (hρ : 0 < ρ) (hM : 0 ≤ M) (f : Gap → ℝ) (hf : Measurable f)
    (hLp : MemLp f 2 μ) (hb : ∀ᵐ d ∂μ, f d ≤ M) :
    ∃ ell c : ℝ, 0 ≤ ell ∧ ell ≤ M ∧ ∃ hc : 0 ≤ c ∧ c ≤ 1,
      let q := fractionalUpperPrior f hf ell c hc
      RarePrior μ ρ q ∧ rareFunctional μ ρ f = ∫ d, q.val d*f d ∂μ ∧
      rareFunctional μ ρ f = ρ*ell+∫ d, max (f d-ell) 0 ∂μ ∧
      (∀ t : ℝ, 0 ≤ t → rareFunctional μ ρ f ≤ ρ*t+∫ d, max (f d-t) 0 ∂μ) ∧
      (0 < ell → signMean μ q.val = ρ) := by
  obtain ⟨⟨q,hq,hqe⟩,ell,hell,hbound,he,hmin⟩ := rarity_support_formula_bounded_above μ hρ hM f hf hLp hb
  have hi := hLp.integrable (by norm_num : (1:ℝ≥0∞) ≤ 2)
  have hcut := upper_tail_equality_cutoff μ hell f hi q hq (hqe.symm.trans he)
  let c := levelAverage μ f ell q
  have hc : 0 ≤ c ∧ c ≤ 1 := (levelAverage_properties μ f hf ell q).1
  let r := fractionalUpperPrior f hf ell c hc
  have hpreserve := fractional_cutoff_preserves μ f hf hi ell q hcut.2
  change signMean μ r.val = signMean μ q.val ∧ (∫ d, r.val d*f d ∂μ) = ∫ d, q.val d*f d ∂μ at hpreserve
  refine ⟨ell,c,hell,hbound,hc,?_,hqe.trans hpreserve.2.symm,he,hmin,?_⟩
  · change signMean μ r.val ≤ ρ
    exact hpreserve.1.trans_le hq
  · intro hellpos
    change signMean μ r.val = ρ
    rw [hpreserve.1]
    have hzero := (mul_eq_zero.mp hcut.1).resolve_left hellpos.ne'
    linarith

theorem fractional_rarity_support (μ : Measure Gap) [IsProbabilityMeasure μ]
    {ρ M : ℝ} (hρ : 0 < ρ) (hM : 0 ≤ M) (f : Gap → ℝ) (hf : Measurable f)
    (hb : ∀ d, ‖f d‖ ≤ M) :
    ∃ ell c : ℝ, 0 ≤ ell ∧ ell ≤ M ∧ ∃ hc : 0 ≤ c ∧ c ≤ 1,
      let q := fractionalUpperPrior f hf ell c hc
      RarePrior μ ρ q ∧ rareFunctional μ ρ f = ∫ d, q.val d*f d ∂μ ∧
      rareFunctional μ ρ f = ρ*ell+∫ d, max (f d-ell) 0 ∂μ ∧
      (∀ t : ℝ, 0 ≤ t → rareFunctional μ ρ f ≤ ρ*t+∫ d, max (f d-t) 0 ∂μ) ∧
      (0 < ell → signMean μ q.val = ρ) := by
  exact fractional_rarity_support_of_memLp μ hρ hM f hf
    (MemLp.of_bound hf.aestronglyMeasurable M (Filter.Eventually.of_forall hb))
    (Filter.Eventually.of_forall (fun d => (le_abs_self (f d)).trans
      (by simpa only [Real.norm_eq_abs] using hb d)))

theorem fractional_rarity_support_explicit (μ : Measure Gap) [IsProbabilityMeasure μ]
    {ρ M : ℝ} (hρ : 0 < ρ) (hM : 0 ≤ M) (f : Gap → ℝ) (hf : Measurable f)
    (hLp : MemLp f 2 μ) (hb : ∀ᵐ d ∂μ, f d ≤ M) :
    ∃ (ell c : ℝ) (q : SignLaw), 0 ≤ ell ∧ ell ≤ M ∧ 0 ≤ c ∧ c ≤ 1 ∧
      (∀ d, q.val d = if ell < f d then 1 else if f d = ell then c else 0) ∧
      signMean μ q.val ≤ ρ ∧
      sSup {r : ℝ | ∃ p : SignLaw, signMean μ p.val ≤ ρ ∧ r = ∫ d, p.val d*f d ∂μ} =
        ∫ d, q.val d*f d ∂μ ∧
      (∫ d, q.val d*f d ∂μ) = ρ*ell+∫ d, max (f d-ell) 0 ∂μ ∧
      (∀ t : ℝ, 0 ≤ t → ρ*ell+(∫ d, max (f d-ell) 0 ∂μ) ≤
        ρ*t+∫ d, max (f d-t) 0 ∂μ) ∧
      (0 < ell → signMean μ q.val = ρ) := by
  obtain ⟨ell,c,hell,hM',hc,hq,hqe,he,hmin,hsat⟩ :=
    fractional_rarity_support_of_memLp μ hρ hM f hf hLp hb
  refine ⟨ell,c,fractionalUpperPrior f hf ell c hc,hell,hM',hc.1,hc.2,
    fun _ => rfl,hq,?_,hqe.symm.trans he,?_,hsat⟩
  · exact (rareFunctional_eq_sSup μ ρ f).symm.trans hqe
  · intro t ht
    exact he.symm.trans_le (hmin t ht)

end ThresholdHC.StoppingProgram
