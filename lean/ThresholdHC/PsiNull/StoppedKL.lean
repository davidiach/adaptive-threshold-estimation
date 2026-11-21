import ThresholdHC.CriticalEntropy.CappedObservation
import ThresholdHC.CriticalEntropy.BernoulliPrefix
import ThresholdHC.EntropyTailUpper.PredictableWald
import ThresholdHC.Tier4.FiniteDensity

/-! The stopped KL chain rule for seeded capped observable procedures.

For a `StoppedProcedure` whose stopping time is bounded by a deterministic cap
`m`, the law of the capped transcript (seed, stopped word) under the coin
parameter `p` has the Bernoulli word probability as density with respect to
`stoppedReference`. The per-seed bounded Wald identity then gives the exact
identity `KL(P_p ‖ P_q) = E_p[T] · klB(p, q)` for `p, q` in `(0,1)`, for every seed
space `R : Type` and output type. -/
noncomputable section
namespace ThresholdHC.PsiNull
open MeasureTheory InformationTheory
open scoped ENNReal
open ThresholdHC.CriticalEntropy

/-- Density of the capped transcript law of a seeded capped procedure under a
single coin parameter `p`, with respect to the parameter-free stopped reference
measure. The density is the Bernoulli probability of the observed stopped word. -/
theorem tape_cappedTranscript_density {R E : Type} [MeasurableSpace R] [MeasurableSpace E]
    (ν : Measure R) [IsProbabilityMeasure ν] (A : StoppedProcedure R E) (m : ℕ)
    (hcap : ∀ z, A.stop z ≤ m) (p : unitInterval) :
    (ν.prod (Tier2.tapeMeasure p)).map (cappedTranscript A m) =
      (stoppedReference ν A m).withDensity
        (fun z => ENNReal.ofReal (streamProb (p : ℝ) z.2.2)) := by
  apply measure_ext_prod_finite
  intro w S hS
  rw [Measure.map_apply (measurable_cappedTranscript A m) (hS.prod (measurableSet_singleton w)),
    withDensity_apply _ (hS.prod (measurableSet_singleton w))]
  have hpre : cappedTranscript A m ⁻¹' (S ×ˢ {w}) =
      {z : R × (ℕ → Bool) |
        z.1 ∈ S ∧ A.stop z = w.1.val ∧ Tier2.tapePrefix w.1.val z.2 = w.2} := by
    ext z
    exact cappedTranscript_mem_cell A m z (hcap z) w S
  have he : (∫⁻ z in S ×ˢ {w}, ENNReal.ofReal (streamProb (p : ℝ) z.2.2)
      ∂stoppedReference ν A m) =
      ∫⁻ _z in S ×ˢ {w}, ENNReal.ofReal (streamProb (p : ℝ) w.2) ∂stoppedReference ν A m := by
    apply setLIntegral_congr_fun (hS.prod (measurableSet_singleton w))
    intro z hz
    dsimp only
    rw [show z.2 = w from hz.2]
  rw [hpre, stopped_word_probability ν p A w.2 S hS, he, setLIntegral_const,
    stoppedReference_cell ν A m w S hS, streamProb_heads, mul_comm]

/-- Seeded bounded Wald identity: summing a score of the observed flips up to
the (capped) stopping time has expectation equal to the expected work times the
one-flip mean of the score. The seed space is arbitrary. -/
theorem seeded_capped_wald {R E : Type} [MeasurableSpace R] [MeasurableSpace E]
    (ν : Measure R) [IsProbabilityMeasure ν] (A : StoppedProcedure R E) (m : ℕ)
    (hcap : ∀ z, A.stop z ≤ m) (p : unitInterval) (f : Bool → ℝ) :
    (∫ z, (∑ i ∈ Finset.range (A.stop z).toNat, f (z.2 i)) ∂ν.prod (Tier2.tapeMeasure p)) =
      (expectedStoppedProcedureWork ν p A).toReal * EntropyTailUpper.bitScoreMean p f := by
  have hfin (z : R × (ℕ → Bool)) : A.stop z ≠ ⊤ := ne_top_of_le_ne_top (by simp) (hcap z)
  have hle (z : R × (ℕ → Bool)) : (A.stop z).toNat ≤ m := by
    simpa using ENat.toNat_le_toNat (hcap z) (by simp)
  have hτ : Measurable (fun z : R × (ℕ → Bool) => (A.stop z).toNat) :=
    (measurable_of_countable ENat.toNat).comp A.measurable_stop
  have hG : Measurable (fun x : ℕ × (ℕ → Bool) => ∑ i ∈ Finset.range x.1, f (x.2 i)) := by
    apply measurable_from_prod_countable_right
    intro n
    change Measurable (fun y : ℕ → Bool => ∑ i ∈ Finset.range n, f (y i))
    exact Finset.measurable_sum _
      (fun i _ => (measurable_of_countable f).comp (measurable_pi_apply i))
  have hFm : Measurable (fun z : R × (ℕ → Bool) =>
      ∑ i ∈ Finset.range (A.stop z).toNat, f (z.2 i)) :=
    hG.comp (hτ.prodMk measurable_snd)
  have hFi : Integrable (fun z : R × (ℕ → Bool) =>
      ∑ i ∈ Finset.range (A.stop z).toNat, f (z.2 i)) (ν.prod (Tier2.tapeMeasure p)) := by
    apply Integrable.of_bound hFm.aestronglyMeasurable (m * (|f true| + |f false|))
    refine ae_of_all _ (fun z => ?_)
    rw [Real.norm_eq_abs]
    calc |∑ i ∈ Finset.range (A.stop z).toNat, f (z.2 i)|
        ≤ ∑ i ∈ Finset.range (A.stop z).toNat, |f (z.2 i)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i ∈ Finset.range (A.stop z).toNat, (|f true| + |f false|) := by
          apply Finset.sum_le_sum
          intro i _
          cases z.2 i
          · linarith [abs_nonneg (f true)]
          · linarith [abs_nonneg (f false)]
      _ = (A.stop z).toNat * (|f true| + |f false|) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      _ ≤ m * (|f true| + |f false|) :=
          mul_le_mul_of_nonneg_right (by exact_mod_cast hle z) (by positivity)
  have hTm : Measurable (fun z : R × (ℕ → Bool) => ((A.stop z).toNat : ℝ)) :=
    (measurable_of_countable (fun n : ℕ => (n : ℝ))).comp hτ
  have hTi : Integrable (fun z : R × (ℕ → Bool) => ((A.stop z).toNat : ℝ))
      (ν.prod (Tier2.tapeMeasure p)) := by
    apply Integrable.of_bound hTm.aestronglyMeasurable m
    refine ae_of_all _ (fun z => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _)]
    exact_mod_cast hle z
  have hseed (r : R) :
      (∫ ω, (∑ i ∈ Finset.range (A.stop (r,ω)).toNat, f (ω i)) ∂Tier2.tapeMeasure p) =
        (∫ ω, ((A.stop (r,ω)).toNat : ℝ) ∂Tier2.tapeMeasure p) *
          EntropyTailUpper.bitScoreMean p f := by
    apply EntropyTailUpper.bounded_wald p f (fun ω => (A.stop (r,ω)).toNat) m
      (fun ω => hle (r,ω))
    intro ω ω' h
    have hn : A.stop (r,ω) = ((A.stop (r,ω)).toNat : ℕ∞) :=
      (ENat.natCast_toNat (hfin (r,ω))).symm
    have h' := (stopped_prefix_ext A r ω ω' _ h hn).1
    rw [h', ENat.toNat_natCast]
  have hwork : (expectedStoppedProcedureWork ν p A).toReal =
      ∫ z, ((A.stop z).toNat : ℝ) ∂ν.prod (Tier2.tapeMeasure p) := by
    unfold expectedStoppedProcedureWork
    rw [← integral_toReal (measurable_stoppedProcedureWork A).aemeasurable
      (ae_of_all _ (fun z => ?_))]
    · apply integral_congr_ae (ae_of_all _ (fun z => ?_))
      obtain ⟨n, hn⟩ : ∃ n : ℕ, A.stop z = n := ⟨_, (ENat.natCast_toNat (hfin z)).symm⟩
      simp [stoppedProcedureWork, hn]
    · obtain ⟨n, hn⟩ : ∃ n : ℕ, A.stop z = n := ⟨_, (ENat.natCast_toNat (hfin z)).symm⟩
      simp [stoppedProcedureWork, hn]
  have hprod : (∫ z, ((A.stop z).toNat : ℝ) ∂ν.prod (Tier2.tapeMeasure p)) =
      ∫ r, ∫ ω, ((A.stop (r,ω)).toNat : ℝ) ∂Tier2.tapeMeasure p ∂ν := integral_prod _ hTi
  rw [integral_prod _ hFi, hwork, hprod, ← integral_mul_const]
  exact integral_congr_ae (ae_of_all _ (fun r => hseed r))

/-- Stopped KL chain rule for a seeded capped procedure: for coin parameters `p`
and `q` in the open interval `(0,1)`, the divergence between the transcript laws
is exactly the expected work under `p` times the one-flip binary divergence
`klB p q`. -/
theorem capped_transcript_kl {R E : Type} [MeasurableSpace R] [MeasurableSpace E]
    (ν : Measure R) [IsProbabilityMeasure ν] (A : StoppedProcedure R E) (m : ℕ)
    (hcap : ∀ z, A.stop z ≤ m) (p q : unitInterval) (hp : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (hq : 0 < (q : ℝ)) (hq1 : (q : ℝ) < 1) :
    klDiv ((ν.prod (Tier2.tapeMeasure p)).map (cappedTranscript A m))
      ((ν.prod (Tier2.tapeMeasure q)).map (cappedTranscript A m)) =
      ENNReal.ofReal ((expectedStoppedProcedureWork ν p A).toReal * klB p q) := by
  let r : CappedWord m → ℝ := fun w => streamProb (p : ℝ) w.2 / streamProb (q : ℝ) w.2
  let score : Bool → ℝ := fun b =>
    Real.log ((if b then (p : ℝ) else 1-p) / (if b then (q : ℝ) else 1-q))
  have hsq : Measurable (fun z : R × CappedWord m =>
      ENNReal.ofReal (streamProb (q : ℝ) z.2.2)) :=
    (measurable_of_countable (fun w : CappedWord m =>
      ENNReal.ofReal (streamProb (q : ℝ) w.2))).comp measurable_snd
  have hr : Measurable (fun z : R × CappedWord m => ENNReal.ofReal (r z.2)) :=
    (measurable_of_countable (fun w : CappedWord m => ENNReal.ofReal (r w))).comp measurable_snd
  have hQP : ((ν.prod (Tier2.tapeMeasure q)).map (cappedTranscript A m)).withDensity
      (fun z => ENNReal.ofReal (r z.2)) =
      (ν.prod (Tier2.tapeMeasure p)).map (cappedTranscript A m) := by
    rw [tape_cappedTranscript_density ν A m hcap q, tape_cappedTranscript_density ν A m hcap p,
      ← withDensity_mul _ hsq hr]
    congr 1
    funext z
    simp only [Pi.mul_apply, r]
    rw [← ENNReal.ofReal_mul (streamProb_pos _ hq hq1 _).le,
      mul_div_cancel₀ _ (streamProb_pos _ hq hq1 _).ne']
  rw [Tier4.klDiv_of_finite_likelihood _ _ Prod.snd measurable_snd r
    (fun z => (div_pos (streamProb_pos _ hp hp1 _) (streamProb_pos _ hq hq1 _)).le) hQP]
  congr 1
  rw [integral_map (f := fun x : R × CappedWord m => Real.log (r x.2))
    (measurable_cappedTranscript A m).aemeasurable
    ((measurable_of_countable (fun w : CappedWord m => Real.log (r w))).comp
      measurable_snd).aestronglyMeasurable]
  have hpt (z : R × (ℕ → Bool)) : Real.log (r (cappedTranscript A m z).2) =
      ∑ i ∈ Finset.range (A.stop z).toNat, score (z.2 i) := by
    have hfin : A.stop z ≠ ⊤ := ne_top_of_le_ne_top (by simp) (hcap z)
    have hle : (A.stop z).toNat ≤ m := by simpa using ENat.toNat_le_toNat (hcap z) (by simp)
    rw [cappedTranscript_of_stop A m _ hle z (ENat.natCast_toNat hfin).symm]
    change Real.log (streamProb (p : ℝ) (Tier2.tapePrefix _ z.2) /
      streamProb (q : ℝ) (Tier2.tapePrefix _ z.2)) = _
    unfold streamProb
    rw [← Finset.prod_div_distrib, Real.log_prod]
    · exact Fin.sum_univ_eq_sum_range (fun i => score (z.2 i)) _
    · intro i _
      exact div_ne_zero (by split <;> linarith) (by split <;> linarith)
  have hscore : EntropyTailUpper.bitScoreMean p score = klB p q := by
    simp [EntropyTailUpper.bitScoreMean, score, klB]
  rw [integral_congr_ae (ae_of_all _ hpt), seeded_capped_wald ν A m hcap p score, hscore]

end ThresholdHC.PsiNull
