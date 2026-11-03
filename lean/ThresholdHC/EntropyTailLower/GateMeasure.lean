import ThresholdHC.EntropyTailLower.GateLikelihood
import ThresholdHC.EntropyTailLower.FairGateWork
import ThresholdHC.CriticalEntropy.CappedObservation

/-! Transfer the gate likelihood factors to its actual seeded stopped-transcript
law. This gives event and nonnegative-observable comparisons, including the
actual expected work, and bounds fair activation by original biased-coin work.
Rejection/restart renewal and conditioned-estimator moments are not asserted. -/

noncomputable section
open MeasureTheory ProbabilityTheory Set Real
open scoped ENNReal
namespace ThresholdHC.EntropyTailLower
open ThresholdHC.Tier2 ThresholdHC.CriticalEntropy ThresholdHC.EntropyTailUpper

def coinTranscriptLaw {R E : Type} [MeasurableSpace R] [MeasurableSpace E]
    (ν : Measure R) (p : unitInterval) (A : StoppedProcedure R E) (M : ℕ) :
    Measure (R × CappedWord M) :=
  (ν.prod (tapeMeasure p)).map (cappedTranscript A M)

theorem coinTranscriptLaw_cell {R E : Type} [MeasurableSpace R] [MeasurableSpace E]
    (ν : Measure R) [IsProbabilityMeasure ν] (p : unitInterval)
    (A : StoppedProcedure R E) (M : ℕ) (hcap : ∀ z, A.stop z ≤ M)
    (w : CappedWord M) (S : Set R) (hS : MeasurableSet S) :
    coinTranscriptLaw ν p A M (S ×ˢ {w}) =
      ν (stoppedSeedCell A w.2 S)*wordLikelihood p w.1.val (wordHeads w.2) := by
  unfold coinTranscriptLaw
  rw [Measure.map_apply (measurable_cappedTranscript A M) (hS.prod (measurableSet_singleton w))]
  have he : cappedTranscript A M ⁻¹' (S ×ˢ {w}) =
      {z : R × (ℕ → Bool) | z.1 ∈ S ∧ A.stop z = w.1.val ∧ tapePrefix w.1.val z.2 = w.2} := by
    ext z
    exact cappedTranscript_mem_cell A M z (hcap z) w S
  rw [he,stopped_word_probability ν p A w.2 S hS]
  rfl

theorem coinTranscriptLaw_density {R E : Type} [MeasurableSpace R] [MeasurableSpace E]
    (ν : Measure R) [IsProbabilityMeasure ν] (p : unitInterval)
    (A : StoppedProcedure R E) (M : ℕ) (hcap : ∀ z, A.stop z ≤ M) :
    coinTranscriptLaw ν p A M = (stoppedReference ν A M).withDensity
      (fun z => wordLikelihood p z.2.1.val (wordHeads z.2.2)) := by
  apply measure_ext_prod_finite
  intro w S hS
  rw [coinTranscriptLaw_cell ν p A M hcap w S hS,
    withDensity_apply _ (hS.prod (measurableSet_singleton w))]
  have he : (∫⁻ z in S ×ˢ {w}, wordLikelihood p z.2.1.val (wordHeads z.2.2)
      ∂stoppedReference ν A M) =
      ∫⁻ _z in S ×ˢ {w}, wordLikelihood p w.1.val (wordHeads w.2) ∂stoppedReference ν A M := by
    apply setLIntegral_congr_fun (hS.prod (measurableSet_singleton w))
    intro z hz
    dsimp only
    rw [show z.2 = w from hz.2]
  rw [he,setLIntegral_const,stoppedReference_cell ν A M w S hS,mul_comm]

theorem measurable_stoppedReference_support {R E : Type} [MeasurableSpace R] [MeasurableSpace E]
    (A : StoppedProcedure R E) (M : ℕ) :
    MeasurableSet {z : R × CappedWord M | (z.1,z.2.2) ∈ A.stopPrefix z.2.1.val} := by
  have he : {z : R × CappedWord M | (z.1,z.2.2) ∈ A.stopPrefix z.2.1.val} =
      ⋃ w : CappedWord M, {r : R | (r,w.2) ∈ A.stopPrefix w.1.val} ×ˢ {w} := by
    ext z
    simp
  rw [he]
  apply MeasurableSet.iUnion
  intro w
  exact ((measurable_id.prodMk measurable_const) (A.measurable_stopPrefix w.1.val)).prod
    (measurableSet_singleton w)

theorem gate_reference_word_likelihood {R E : Type} [MeasurableSpace R] [MeasurableSpace E]
    (A : StoppedProcedure R E) (a : ℝ) (ha : 0 < a) (ha4 : a ≤ 1/4)
    (p : unitInterval) (hp : |(p:ℝ)-1/2| ≤ a)
    (r : R) (w : CappedWord ⌈(a^2)⁻¹⌉₊)
    (hw : (r,w.2) ∈ (activationGate A ⌈(a^2)⁻¹⌉₊ ⌈a⁻¹⌉₊).stopPrefix w.1.val) :
    ENNReal.ofReal (exp (-12))*wordLikelihood ⟨1/2,by norm_num⟩ w.1.val (wordHeads w.2) ≤
        wordLikelihood p w.1.val (wordHeads w.2) ∧
      wordLikelihood p w.1.val (wordHeads w.2) ≤
        ENNReal.ofReal (exp 12)*wordLikelihood ⟨1/2,by norm_num⟩ w.1.val (wordHeads w.2) := by
  let ω := completePrefix w.1.val w.2
  have hs : (activationGate A ⌈(a^2)⁻¹⌉₊ ⌈a⁻¹⌉₊).stop (r,ω) = w.1.val := by
    apply ((activationGate A ⌈(a^2)⁻¹⌉₊ ⌈a⁻¹⌉₊).stop_observable w.1.val (r,ω)).mp
    simpa [ω,tapePrefix_completePrefix] using hw
  have hc : activationGateCost A ⌈(a^2)⁻¹⌉₊ ⌈a⁻¹⌉₊ (r,ω) = w.1.val := by
    change (activationGateCost A ⌈(a^2)⁻¹⌉₊ ⌈a⁻¹⌉₊ (r,ω):ℕ∞) = (w.1.val:ℕ∞) at hs
    exact_mod_cast hs
  have hl := activationGate_prefix_likelihood A a ((p:ℝ)-1/2) ha ha4 hp (r,ω)
  dsimp only at hl
  rw [hc] at hl
  simp only [ω,tapePrefix_completePrefix] at hl
  have hk : wordHeads w.2 ≤ w.1.val := by
    unfold wordHeads
    simpa using Finset.card_filter_le (s := Finset.univ) (fun i => w.2 i = true)
  have hf : (p:ℝ)^wordHeads w.2*(1-(p:ℝ))^(w.1.val-wordHeads w.2) =
      (1/2:ℝ)^w.1.val*gatePrefixLikelihood ((p:ℝ)-1/2) w.1.val (wordHeads w.2) := by
    convert gatePrefixLikelihood_factor ((p:ℝ)-1/2) w.1.val (wordHeads w.2) hk using 1
    ring
  have hfair : wordLikelihood ⟨1/2,by norm_num⟩ w.1.val (wordHeads w.2) =
      ENNReal.ofReal ((1/2:ℝ)^w.1.val) := by
    unfold wordLikelihood
    norm_num only
    rw [← pow_add,Nat.add_sub_of_le hk]
  have he : wordLikelihood p w.1.val (wordHeads w.2) =
      wordLikelihood ⟨1/2,by norm_num⟩ w.1.val (wordHeads w.2)*
        ENNReal.ofReal (gatePrefixLikelihood ((p:ℝ)-1/2) w.1.val (wordHeads w.2)) := by
    rw [hfair,wordLikelihood,hf,ENNReal.ofReal_mul (by positivity)]
  rw [he]
  constructor
  · rw [mul_comm (ENNReal.ofReal (exp (-12))) _]
    exact mul_le_mul' le_rfl (ENNReal.ofReal_le_ofReal hl.1)
  · rw [mul_comm (ENNReal.ofReal (exp 12)) _]
    exact mul_le_mul' le_rfl (ENNReal.ofReal_le_ofReal hl.2)

theorem activationGate_transcript_comparison {R E : Type} [MeasurableSpace R] [MeasurableSpace E]
    (ν : Measure R) [IsProbabilityMeasure ν] (A : StoppedProcedure R E)
    (a : ℝ) (ha : 0 < a) (ha4 : a ≤ 1/4)
    (p : unitInterval) (hp : |(p:ℝ)-1/2| ≤ a) :
    ENNReal.ofReal (exp (-12)) • coinTranscriptLaw ν ⟨1/2,by norm_num⟩
      (activationGate A ⌈(a^2)⁻¹⌉₊ ⌈a⁻¹⌉₊) ⌈(a^2)⁻¹⌉₊ ≤
        coinTranscriptLaw ν p (activationGate A ⌈(a^2)⁻¹⌉₊ ⌈a⁻¹⌉₊) ⌈(a^2)⁻¹⌉₊ ∧
      coinTranscriptLaw ν p (activationGate A ⌈(a^2)⁻¹⌉₊ ⌈a⁻¹⌉₊) ⌈(a^2)⁻¹⌉₊ ≤
        ENNReal.ofReal (exp 12) • coinTranscriptLaw ν ⟨1/2,by norm_num⟩
          (activationGate A ⌈(a^2)⁻¹⌉₊ ⌈a⁻¹⌉₊) ⌈(a^2)⁻¹⌉₊ := by
  let G := activationGate A ⌈(a^2)⁻¹⌉₊ ⌈a⁻¹⌉₊
  have hcap : ∀ z, G.stop z ≤ ⌈(a^2)⁻¹⌉₊ := fun z => (activationGate_stop_le A _ _ z).2
  have hd := coinTranscriptLaw_density ν p G _ hcap
  have hf := coinTranscriptLaw_density ν ⟨1/2,by norm_num⟩ G _ hcap
  have hb : ∀ᵐ z ∂stoppedReference ν G ⌈(a^2)⁻¹⌉₊,
      ENNReal.ofReal (exp (-12))*wordLikelihood ⟨1/2,by norm_num⟩ z.2.1.val (wordHeads z.2.2) ≤
          wordLikelihood p z.2.1.val (wordHeads z.2.2) ∧
        wordLikelihood p z.2.1.val (wordHeads z.2.2) ≤
          ENNReal.ofReal (exp 12)*wordLikelihood ⟨1/2,by norm_num⟩ z.2.1.val (wordHeads z.2.2) := by
    unfold stoppedReference
    apply ae_restrict_of_forall_mem (measurable_stoppedReference_support G _)
    intro z hz
    exact gate_reference_word_likelihood A a ha ha4 p hp z.1 z.2 hz
  change ENNReal.ofReal (exp (-12)) • coinTranscriptLaw ν ⟨1/2,by norm_num⟩ G _ ≤
      coinTranscriptLaw ν p G _ ∧ coinTranscriptLaw ν p G _ ≤
        ENNReal.ofReal (exp 12) • coinTranscriptLaw ν ⟨1/2,by norm_num⟩ G _
  rw [hd,hf,← withDensity_smul' _ _ ENNReal.ofReal_ne_top,
    ← withDensity_smul' _ _ ENNReal.ofReal_ne_top]
  exact ⟨withDensity_mono (hb.mono (fun _ h => h.1)),
    withDensity_mono (hb.mono (fun _ h => h.2))⟩

theorem activationGate_lintegral_comparison {R E : Type} [MeasurableSpace R] [MeasurableSpace E]
    (ν : Measure R) [IsProbabilityMeasure ν] (A : StoppedProcedure R E)
    (a : ℝ) (ha : 0 < a) (ha4 : a ≤ 1/4)
    (p : unitInterval) (hp : |(p:ℝ)-1/2| ≤ a)
    (f : R × CappedWord ⌈(a^2)⁻¹⌉₊ → ℝ≥0∞) (hf : Measurable f) :
    ENNReal.ofReal (exp (-12))*(∫⁻ z, f (cappedTranscript
      (activationGate A ⌈(a^2)⁻¹⌉₊ ⌈a⁻¹⌉₊) ⌈(a^2)⁻¹⌉₊ z) ∂ν.prod (tapeMeasure ⟨1/2,by norm_num⟩)) ≤
      (∫⁻ z, f (cappedTranscript (activationGate A ⌈(a^2)⁻¹⌉₊ ⌈a⁻¹⌉₊) ⌈(a^2)⁻¹⌉₊ z)
        ∂ν.prod (tapeMeasure p)) ∧
      (∫⁻ z, f (cappedTranscript (activationGate A ⌈(a^2)⁻¹⌉₊ ⌈a⁻¹⌉₊) ⌈(a^2)⁻¹⌉₊ z)
        ∂ν.prod (tapeMeasure p)) ≤
      ENNReal.ofReal (exp 12)*(∫⁻ z, f (cappedTranscript
        (activationGate A ⌈(a^2)⁻¹⌉₊ ⌈a⁻¹⌉₊) ⌈(a^2)⁻¹⌉₊ z) ∂ν.prod (tapeMeasure ⟨1/2,by norm_num⟩)) := by
  obtain ⟨hl,hu⟩ := activationGate_transcript_comparison ν A a ha ha4 p hp
  have h₁ := lintegral_mono' hl (le_refl f)
  have h₂ := lintegral_mono' hu (le_refl f)
  simp only [lintegral_smul_measure,coinTranscriptLaw,
    lintegral_map hf (measurable_cappedTranscript _ _)] at h₁ h₂
  exact ⟨h₁,h₂⟩

theorem activationGate_work_comparison {R E : Type} [MeasurableSpace R] [MeasurableSpace E]
    (ν : Measure R) [IsProbabilityMeasure ν] (A : StoppedProcedure R E)
    (a : ℝ) (ha : 0 < a) (ha4 : a ≤ 1/4)
    (p : unitInterval) (hp : |(p:ℝ)-1/2| ≤ a) :
    ENNReal.ofReal (exp (-12))*expectedStoppedProcedureWork ν ⟨1/2,by norm_num⟩
      (activationGate A ⌈(a^2)⁻¹⌉₊ ⌈a⁻¹⌉₊) ≤
        expectedStoppedProcedureWork ν p (activationGate A ⌈(a^2)⁻¹⌉₊ ⌈a⁻¹⌉₊) ∧
      expectedStoppedProcedureWork ν p (activationGate A ⌈(a^2)⁻¹⌉₊ ⌈a⁻¹⌉₊) ≤
        ENNReal.ofReal (exp 12)*expectedStoppedProcedureWork ν ⟨1/2,by norm_num⟩
          (activationGate A ⌈(a^2)⁻¹⌉₊ ⌈a⁻¹⌉₊) := by
  let f : R × CappedWord ⌈(a^2)⁻¹⌉₊ → ℝ≥0∞ := fun z => z.2.1.val
  have hf : Measurable f :=
    (measurable_of_countable (fun w : CappedWord ⌈(a^2)⁻¹⌉₊ => (w.1.val:ℝ≥0∞))).comp measurable_snd
  have h := activationGate_lintegral_comparison ν A a ha ha4 p hp f hf
  have he (z : R × (ℕ → Bool)) : f (cappedTranscript
      (activationGate A ⌈(a^2)⁻¹⌉₊ ⌈a⁻¹⌉₊) ⌈(a^2)⁻¹⌉₊ z) =
      stoppedProcedureWork (activationGate A ⌈(a^2)⁻¹⌉₊ ⌈a⁻¹⌉₊) z := by
    rw [cappedTranscript_of_stop _ _ (activationGateCost A ⌈(a^2)⁻¹⌉₊ ⌈a⁻¹⌉₊ z)
      (activationGate_bounds A _ _ z).1 z rfl]
    change (activationGateCost A ⌈(a^2)⁻¹⌉₊ ⌈a⁻¹⌉₊ z:ℝ≥0∞) =
      ((activationGateCost A ⌈(a^2)⁻¹⌉₊ ⌈a⁻¹⌉₊ z:ℕ∞):ℝ≥0∞)
    simp
  simpa only [he,expectedStoppedProcedureWork] using h

def transcriptOutput {R E : Type} [MeasurableSpace R] [MeasurableSpace E]
    (A : StoppedProcedure R E) (M : ℕ) (z : R × CappedWord M) : E :=
  A.outputPrefix z.2.1.val (z.1,z.2.2)

theorem measurable_transcriptOutput {R E : Type} [MeasurableSpace R] [MeasurableSpace E]
    (A : StoppedProcedure R E) (M : ℕ) : Measurable (transcriptOutput A M) := by
  apply measurable_from_prod_countable_left
  intro w
  change Measurable (fun r : R => A.outputPrefix w.1.val (r,w.2))
  exact (A.measurable_outputPrefix w.1.val).comp (measurable_id.prodMk measurable_const)

theorem transcriptOutput_eq {R E : Type} [MeasurableSpace R] [MeasurableSpace E]
    (A : StoppedProcedure R E) (M : ℕ) (z : R × (ℕ → Bool)) (hcap : A.stop z ≤ M) :
    transcriptOutput A M (cappedTranscript A M z) = A.output z := by
  have ht : A.stop z ≠ ⊤ := ne_top_of_le_ne_top (by simp) hcap
  have hn : A.stop z = ((A.stop z).toNat:ℕ∞) := (ENat.natCast_toNat ht).symm
  have hM : (A.stop z).toNat ≤ M := by
    simpa using ENat.toNat_le_toNat hcap (by simp)
  rw [cappedTranscript_of_stop A M _ hM z hn]
  exact (A.output_observable _ z hn).symm

theorem activationGate_probability_comparison {R E : Type} [MeasurableSpace R] [MeasurableSpace E]
    (ν : Measure R) [IsProbabilityMeasure ν] (A : StoppedProcedure R E)
    (a : ℝ) (ha : 0 < a) (ha4 : a ≤ 1/4)
    (p : unitInterval) (hp : |(p:ℝ)-1/2| ≤ a) :
    ENNReal.ofReal (exp (-12))*(ν.prod (tapeMeasure ⟨1/2,by norm_num⟩))
      {z | (activationGate A ⌈(a^2)⁻¹⌉₊ ⌈a⁻¹⌉₊).output z = true} ≤
      (ν.prod (tapeMeasure p)) {z | (activationGate A ⌈(a^2)⁻¹⌉₊ ⌈a⁻¹⌉₊).output z = true} ∧
      (ν.prod (tapeMeasure p)) {z | (activationGate A ⌈(a^2)⁻¹⌉₊ ⌈a⁻¹⌉₊).output z = true} ≤
        ENNReal.ofReal (exp 12)*(ν.prod (tapeMeasure ⟨1/2,by norm_num⟩))
          {z | (activationGate A ⌈(a^2)⁻¹⌉₊ ⌈a⁻¹⌉₊).output z = true} := by
  let G := activationGate A ⌈(a^2)⁻¹⌉₊ ⌈a⁻¹⌉₊
  let S := {z | transcriptOutput G ⌈(a^2)⁻¹⌉₊ z = true}
  have hS : MeasurableSet S :=
    measurableSet_eq_fun (measurable_transcriptOutput G _) measurable_const
  have hf : Measurable (S.indicator (fun _ => (1:ℝ≥0∞))) := measurable_const.indicator hS
  have h := activationGate_lintegral_comparison ν A a ha ha4 p hp _ hf
  have he (z : R × (ℕ → Bool)) : S.indicator (fun _ => (1:ℝ≥0∞))
      (cappedTranscript G ⌈(a^2)⁻¹⌉₊ z) =
      {z | G.output z = true}.indicator (fun _ => (1:ℝ≥0∞)) z := by
    simp only [Set.indicator,S,Set.mem_ofPred_eq,
      transcriptOutput_eq G _ z (activationGate_stop_le A _ _ z).2]
  change _ ≤ _ ∧ _ ≤ _ at h
  simp only [← show G = activationGate A ⌈(a^2)⁻¹⌉₊ ⌈a⁻¹⌉₊ from rfl,he] at h
  have hm : MeasurableSet {z | G.output z = true} :=
    measurableSet_eq_fun G.measurable_output measurable_const
  simpa only [lintegral_indicator hm,lintegral_one,Measure.restrict_apply_univ] using h

theorem activationGate_fair_work_le_biased {R E : Type} [MeasurableSpace R] [MeasurableSpace E]
    (ν : Measure R) [IsProbabilityMeasure ν] (A : StoppedProcedure R E)
    (a : ℝ) (ha : 0 < a) (ha4 : a ≤ 1/4)
    (p : unitInterval) (hp : |(p:ℝ)-1/2| ≤ a) :
    expectedStoppedProcedureWork ν ⟨1/2,by norm_num⟩
      (activationGate A ⌈(a^2)⁻¹⌉₊ ⌈a⁻¹⌉₊) ≤
      ENNReal.ofReal (exp 12)*expectedStoppedProcedureWork ν p A := by
  have hl := (activationGate_work_comparison ν A a ha ha4 p hp).1
  have he : ENNReal.ofReal (exp 12)*ENNReal.ofReal (exp (-12)) = 1 := by
    rw [← ENNReal.ofReal_mul (exp_pos _).le,← exp_add]
    norm_num
  have h := mul_le_mul' (le_refl (ENNReal.ofReal (exp 12))) hl
  rw [← mul_assoc,he,one_mul] at h
  exact h.trans (mul_le_mul' le_rfl (expected_activationGate_work_le ν p A _ _))

/-- Activation under the fair law is controlled by original expected work
under every nearby biased coin, retaining infinite work honestly. -/
theorem activationGate_fair_probability_le_biased_work {R E : Type}
    [MeasurableSpace R] [MeasurableSpace E]
    (ν : Measure R) [IsProbabilityMeasure ν] (A : StoppedProcedure R E)
    (a : ℝ) (ha : 0 < a) (ha4 : a ≤ 1/4)
    (p : unitInterval) (hp : |(p:ℝ)-1/2| ≤ a) :
    (ν.prod (tapeMeasure ⟨1/2,by norm_num⟩))
      {z | (activationGate A ⌈(a^2)⁻¹⌉₊ ⌈a⁻¹⌉₊).output z = true} ≤
      ENNReal.ofReal (2*exp 12*a^2)*expectedStoppedProcedureWork ν p A := by
  have hprob := ENNReal.ofReal_le_ofReal (activationGate_fair_scaled_probability ν A a ha)
  rw [measureReal_def,ENNReal.ofReal_toReal (measure_ne_top _ _),
    ENNReal.ofReal_mul (by positivity),
    ENNReal.ofReal_toReal (expected_activationGate_work_finite ν _ A _ _)] at hprob
  calc
    _ ≤ ENNReal.ofReal (2*a^2)*expectedStoppedProcedureWork ν ⟨1/2,by norm_num⟩
        (activationGate A ⌈(a^2)⁻¹⌉₊ ⌈a⁻¹⌉₊) := hprob
    _ ≤ ENNReal.ofReal (2*a^2)*(ENNReal.ofReal (exp 12)*expectedStoppedProcedureWork ν p A) :=
      mul_le_mul' le_rfl (activationGate_fair_work_le_biased ν A a ha ha4 p hp)
    _ = _ := by
      rw [← mul_assoc,← ENNReal.ofReal_mul (by positivity)]
      congr 2
      ring

end ThresholdHC.EntropyTailLower
