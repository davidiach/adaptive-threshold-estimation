import ThresholdHC.Tier4.FiniteDensity
import ThresholdHC.Tier3.TranscriptRatio

noncomputable section
open MeasureTheory InformationTheory
open scoped ENNReal

namespace ThresholdHC.Tier5
open ThresholdHC.Tier3

local instance (m : ℕ) : MeasurableSpace (Option (Fin m)) := ⊤

theorem integrable_of_abs_bound {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsFiniteMeasure μ] (f : X → ℝ) (hf : Measurable f)
    (C : ℝ) (hb : ∀ x, |f x| ≤ C) : Integrable f μ :=
  Integrable.of_bound hf.aestronglyMeasurable C (by simpa only [Real.norm_eq_abs] using
    (Filter.Eventually.of_forall hb : ∀ᵐ x ∂μ, |f x| ≤ C))

theorem measurable_variable_finite_eval {X A : Type*} [MeasurableSpace X]
    [MeasurableSpace A] [Countable A] [MeasurableSingletonClass A]
    (a : X → A) (ha : Measurable a) (f : A → X → ℝ)
    (hf : ∀ i, Measurable (f i)) : Measurable (fun x => f (a x) x) :=
  (measurable_from_prod_countable_left (f := fun z : X × A => f z.2 z.1) hf).comp
    (measurable_id.prodMk ha)

theorem measurable_variable_pathProb {Seed : Type} [MeasurableSpace Seed] {m n : ℕ}
    (pol : Seed → List Bool → Option (Fin m)) (hp : MeasurablePolicy pol)
    (p : Seed → Fin m → ℝ) (hpm : ∀ i, Measurable (fun u => p u i))
    (w : Prefix n) : Measurable (fun u => pathProb (pol u) (p u) w) := by
  unfold pathProb
  apply Finset.measurable_prod
  intro t ht
  refine measurable_variable_finite_eval (fun u => pol u (histBefore w t))
    (measurable_to_countable' (hp (histBefore w t)))
    (fun a u => match a, w t with
      | none, none => 1
      | some i, some true => p u i
      | some i, some false => 1-p u i
      | _, _ => 0) ?_
  intro a
  cases a with
  | none => cases w t <;> exact measurable_const
  | some i =>
    cases w t with
    | none => exact measurable_const
    | some b =>
      cases b with
      | false => exact measurable_const.sub (hpm i)
      | true => exact hpm i

theorem measurable_variable_transcriptLaw {Seed : Type} [MeasurableSpace Seed] {m n : ℕ}
    (pol : Seed → List Bool → Option (Fin m)) (hp : MeasurablePolicy pol)
    (d q : Seed → Fin m → ℝ)
    (hdm : ∀ i, Measurable (fun u => d u i))
    (hqm : ∀ i, Measurable (fun u => q u i)) (w : Prefix n) :
    Measurable (fun u => transcriptLaw (pol u) (d u) (q u) w) := by
  unfold transcriptLaw
  apply Finset.measurable_sum
  intro s hs
  apply Measurable.mul
  · apply Finset.measurable_prod
    intro i hi
    split_ifs <;> fun_prop
  · apply measurable_variable_pathProb pol hp
    intro i
    split_ifs <;> fun_prop

theorem ratio_le_of_comparison {p q K : ℝ} (hq : 0 ≤ q) (hK : 0 ≤ K)
    (hpq : p ≤ K * q) : p / q ≤ K := by
  by_cases hz : q = 0
  · simp [hz, hK]
  · exact (div_le_iff₀ (lt_of_le_of_ne hq (Ne.symm hz))).mpr hpq

theorem abs_log_ratio_le {p q K : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q) (hK : 0 ≤ K)
    (hpq : p ≤ K * q) (hqp : q ≤ K * p) : |Real.log (p/q)| ≤ K := by
  have hrat := ratio_le_of_comparison hq hK hpq
  have hinv : (p/q)⁻¹ ≤ K := by simpa only [inv_div] using ratio_le_of_comparison hp hK hqp
  exact abs_le.mpr ⟨(neg_le_neg hinv).trans (Real.neg_inv_le_log (div_nonneg hp hq)),
    (Real.log_le_self (div_nonneg hp hq)).trans hrat⟩

theorem klDiv_of_bounded_likelihood {X : Type} [MeasurableSpace X]
    (P Q : Measure X) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (r : X → ℝ) (hrm : Measurable r) (hr0 : ∀ x, 0 ≤ r x)
    (K : ℝ) (hlog : ∀ x, |Real.log (r x)| ≤ K)
    (hQP : Q.withDensity (fun x => ENNReal.ofReal (r x)) = P) :
    klDiv P Q = ENNReal.ofReal (∫ x, Real.log (r x) ∂P) := by
  have hac : P ≪ Q := hQP ▸ withDensity_absolutelyContinuous Q _
  have hrn : P.rnDeriv Q =ᵐ[Q] (fun x => ENNReal.ofReal (r x)) := by
    rw [← hQP]
    exact Measure.rnDeriv_withDensity Q hrm.ennreal_ofReal
  have hllr : llr P Q =ᵐ[P] (fun x => Real.log (r x)) := by
    filter_upwards [hac.ae_le hrn] with x hx
    simp [llr, hx, ENNReal.toReal_ofReal (hr0 x)]
  have hint : Integrable (llr P Q) P := by
    rw [integrable_congr hllr]
    exact integrable_of_abs_bound P _ hrm.log K hlog
  rw [klDiv_of_ac_of_integrable hac hint, probReal_univ, probReal_univ,
    add_sub_cancel_right, integral_congr_ae hllr]

end ThresholdHC.Tier5
