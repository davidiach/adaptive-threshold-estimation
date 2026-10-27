import ThresholdHC.Proofs.Tier2.ClassifierProbability
import ThresholdHC.Proofs.Tier2.TranscriptLikelihood
import ThresholdHC.Tier4.FiniteDensity
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.InformationTheory.KullbackLeibler.DataProcessing

/-!
Exact information in deterministic Bernoulli prefixes, including an arbitrary
independent random seed. These are actual probability measures, not assumed
information bounds. Stopping events and the entropy packing are separate steps.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Real
open scoped ENNReal

namespace ThresholdHC.CriticalEntropy

theorem streamProb_pos (p : ℝ) (hp : 0 < p) (hp1 : p < 1)
    {n : ℕ} (x : Fin n → Bool) : 0 < streamProb p x := by
  apply Finset.prod_pos
  intro i hi
  split <;> linarith

/-- Product Bernoulli information is exactly the number of flips times the
one-flip binary divergence. -/
theorem stream_kl_identity (p q : ℝ) (hp : 0 < p) (hp1 : p < 1)
    (hq : 0 < q) (hq1 : q < 1) (n : ℕ) :
    klFT (streamProb p : (Fin n → Bool) → ℝ) (streamProb q) = n * klB p q := by
  classical
  have hbit (r : ℝ) (hr : 0 < r) (hr1 : r < 1) (b : Bool) :
      (if b then r else 1-r) ≠ 0 := by
    split <;> linarith
  have hlog (x : Fin n → Bool) :
      log (streamProb p x / streamProb q x) =
        ∑ i : Fin n, log ((if x i then p else 1-p) / (if x i then q else 1-q)) := by
    unfold streamProb
    rw [← Finset.prod_div_distrib, log_prod]
    intro i hi
    exact div_ne_zero (hbit p hp hp1 _) (hbit q hq hq1 _)
  unfold klFT
  simp_rw [hlog, Finset.mul_sum]
  rw [Finset.sum_comm]
  have hterm (i : Fin n) :
      (∑ x : Fin n → Bool, streamProb p x *
        log ((if x i then p else 1-p) / (if x i then q else 1-q))) = klB p q := by
    unfold streamProb
    rw [Proofs.sum_prod_coordinate (fun (_ : Fin n) (b : Bool) => if b then p else 1-p)
      (fun b => log ((if b then p else 1-p) / (if b then q else 1-q))) i]
    simp [klB]
  simp_rw [hterm]
  simp

theorem finiteMeasure_positive (p : unitInterval) (hp : 0 < (p : ℝ))
    (hp1 : (p : ℝ) < 1) {n : ℕ} (x : Fin n → Bool) :
    0 < Tier2.finiteMeasure p n {x} := by
  have h := streamProb_pos p hp hp1 x
  rw [← Tier2.finiteMeasure_real_singleton p x] at h
  exact (ENNReal.toReal_pos_iff.mp h).1

/-- Exact Radon--Nikodym identity for finite Bernoulli tapes. -/
theorem finiteMeasure_density (p q : unitInterval) (hq : 0 < (q : ℝ))
    (hq1 : (q : ℝ) < 1) (n : ℕ) :
    (Tier2.finiteMeasure q n).withDensity
      (fun x => ENNReal.ofReal (streamProb (p : ℝ) x / streamProb (q : ℝ) x)) =
      Tier2.finiteMeasure p n := by
  apply Measure.ext_of_singleton
  intro x
  rw [withDensity_apply _ (measurableSet_singleton x), lintegral_singleton]
  rw [← Tier2.finiteMeasure_real_singleton p x,
    ← Tier2.finiteMeasure_real_singleton q x]
  rw [measureReal_def, measureReal_def]
  rw [ENNReal.ofReal_div_of_pos
    (ENNReal.toReal_pos (ne_of_gt (finiteMeasure_positive q hq hq1 x)) (measure_ne_top _ _))]
  rw [ENNReal.ofReal_toReal (measure_ne_top _ _),
    ENNReal.ofReal_toReal (measure_ne_top _ _)]
  exact ENNReal.div_mul_cancel (ne_of_gt (finiteMeasure_positive q hq hq1 x))
    (measure_ne_top _ _)

/-- Arbitrary common independent randomness costs no information. The seed
space need not be finite, countable, or standard Borel. -/
theorem seeded_prefix_kl {R : Type} [MeasurableSpace R]
    (ν : Measure R) [IsProbabilityMeasure ν]
    (p q : unitInterval) (hp : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (hq : 0 < (q : ℝ)) (hq1 : (q : ℝ) < 1) (n : ℕ) :
    InformationTheory.klDiv (ν.prod (Tier2.finiteMeasure p n))
      (ν.prod (Tier2.finiteMeasure q n)) = ENNReal.ofReal (n * klB p q) := by
  let r : (Fin n → Bool) → ℝ := fun x => streamProb (p : ℝ) x / streamProb (q : ℝ) x
  have hm : Measurable (fun x => ENNReal.ofReal (r x)) := measurable_of_countable _
  have hd : (ν.prod (Tier2.finiteMeasure q n)).withDensity
      (fun z => ENNReal.ofReal (r z.2)) = ν.prod (Tier2.finiteMeasure p n) := by
    rw [← prod_withDensity_right hm, finiteMeasure_density p q hq hq1 n]
  rw [Tier4.klDiv_of_finite_likelihood _ _ Prod.snd measurable_snd r
    (fun z => (div_pos (streamProb_pos p hp hp1 z.2)
      (streamProb_pos q hq hq1 z.2)).le) hd]
  congr 1
  rw [integral_fun_snd (fun x => log (r x)), probReal_univ, one_smul,
    Tier2.integral_finiteMeasure]
  exact stream_kl_identity p q hp hp1 hq hq1 n

/-- The Bernoulli KL bound used for both early stopping and comparison with
the fair-coin reference. The constants are derived, not hypotheses. -/
theorem binary_kl_le_chisq (p q : ℝ) (hp : 0 < p) (hp1 : p < 1)
    (hq : 0 < q) (hq1 : q < 1) : klB p q ≤ (p-q)^2 / (q*(1-q)) := by
  have h1 := mul_le_mul_of_nonneg_left
    (log_le_sub_one_of_pos (div_pos hp hq)) hp.le
  have h2 := mul_le_mul_of_nonneg_left
    (log_le_sub_one_of_pos (div_pos (by linarith : 0 < 1-p)
      (by linarith : 0 < 1-q))) (by linarith : 0 ≤ 1-p)
  have he : p*(p/q-1) + (1-p)*((1-p)/(1-q)-1) = (p-q)^2/(q*(1-q)) := by
    field_simp
    ring
  unfold klB
  linarith

theorem seeded_prefix_kl_le_chisq {R : Type} [MeasurableSpace R]
    (ν : Measure R) [IsProbabilityMeasure ν]
    (p q : unitInterval) (hp : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (hq : 0 < (q : ℝ)) (hq1 : (q : ℝ) < 1) (n : ℕ) :
    InformationTheory.klDiv (ν.prod (Tier2.finiteMeasure p n))
      (ν.prod (Tier2.finiteMeasure q n)) ≤
      ENNReal.ofReal (n * ((p : ℝ)-q)^2 / ((q : ℝ)*(1-q))) := by
  rw [seeded_prefix_kl ν p q hp hp1 hq hq1 n]
  apply ENNReal.ofReal_le_ofReal
  simpa only [mul_div_assoc] using mul_le_mul_of_nonneg_left
    (binary_kl_le_chisq p q hp hp1 hq hq1) (Nat.cast_nonneg n : (0 : ℝ) ≤ n)

/-- Deterministic prefixes of the actual infinite iid experiment have the
finite product law, retaining the algorithm's independent seed. -/
theorem seeded_tape_prefix_map {R : Type} [MeasurableSpace R]
    (ν : Measure R) [IsProbabilityMeasure ν] (p : unitInterval) (n : ℕ) :
    (ν.prod (Tier2.tapeMeasure p)).map (Prod.map id (Tier2.tapePrefix n)) =
      ν.prod (Tier2.finiteMeasure p n) := by
  rw [← Measure.map_prod_map ν (Tier2.tapeMeasure p) measurable_id (Tier2.measurable_prefix n),
    Measure.map_id, Tier2.prefix_map]

/-- Any measurable statistic of the seed and the first `n` flips obeys the
derived Bernoulli information bound. In particular, the statistic may record
an early stopping decision. No termination under the fair coin is assumed. -/
theorem prefix_observable_kl_le {R X : Type} [MeasurableSpace R] [MeasurableSpace X]
    (ν : Measure R) [IsProbabilityMeasure ν]
    (p q : unitInterval) (hp : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (hq : 0 < (q : ℝ)) (hq1 : (q : ℝ) < 1) (n : ℕ)
    (f : R × (Fin n → Bool) → X) (hf : Measurable f) :
    InformationTheory.klDiv
      ((ν.prod (Tier2.tapeMeasure p)).map (f ∘ Prod.map id (Tier2.tapePrefix n)))
      ((ν.prod (Tier2.tapeMeasure q)).map (f ∘ Prod.map id (Tier2.tapePrefix n))) ≤
      ENNReal.ofReal (n * ((p : ℝ)-q)^2 / ((q : ℝ)*(1-q))) := by
  have hm : Measurable (Prod.map (id : R → R) (Tier2.tapePrefix n)) :=
    measurable_id.prodMap (Tier2.measurable_prefix n)
  rw [← Measure.map_map hf hm, ← Measure.map_map hf hm,
    seeded_tape_prefix_map, seeded_tape_prefix_map]
  exact (InformationTheory.klDiv_map_le _ _ hf).trans
    (seeded_prefix_kl_le_chisq ν p q hp hp1 hq hq1 n)

end ThresholdHC.CriticalEntropy
