import ThresholdHC.EntropyTailLower.EarlyLikelihood
import ThresholdHC.EntropyTailLower.EarlyOutput
import ThresholdHC.EntropyTailLower.FractionalPrior

/-! Integrate actual stopped-prefix likelihoods against the observable early
output. The signwise squared mean difference is bounded by the original
population moment/work product, for arbitrary probability laws. Derive
positive fair activation in the stated small-work regime. -/

noncomputable section
open MeasureTheory ProbabilityTheory Set Real
open scoped ENNReal
namespace ThresholdHC.EntropyTailLower
open ThresholdHC.Tier2 ThresholdHC.CriticalEntropy ThresholdHC.BlindUpper

theorem wordLikelihood_fair_factor (p : unitInterval) (n k : ℕ) (hk : k ≤ n) :
    wordLikelihood p n k = wordLikelihood ⟨1/2,by norm_num⟩ n k *
      ENNReal.ofReal (gatePrefixLikelihood ((p:ℝ)-1/2) n k) := by
  have hf : (p:ℝ)^k*(1-(p:ℝ))^(n-k) =
      (1/2:ℝ)^n*gatePrefixLikelihood ((p:ℝ)-1/2) n k := by
    convert gatePrefixLikelihood_factor ((p:ℝ)-1/2) n k hk using 1
    ring
  have hfair : wordLikelihood ⟨1/2,by norm_num⟩ n k = ENNReal.ofReal ((1/2:ℝ)^n) := by
    unfold wordLikelihood
    norm_num only
    rw [← pow_add,Nat.add_sub_of_le hk]
  rw [hfair,wordLikelihood,hf,ENNReal.ofReal_mul (by positivity)]

theorem coinTranscriptLaw_fair_density {R E : Type} [MeasurableSpace R] [MeasurableSpace E]
    (ν : Measure R) [IsProbabilityMeasure ν] (p : unitInterval)
    (A : StoppedProcedure R E) (M : ℕ) (hcap : ∀ z, A.stop z ≤ M) :
    coinTranscriptLaw ν p A M = (coinTranscriptLaw ν ⟨1/2,by norm_num⟩ A M).withDensity
      (fun z => ENNReal.ofReal (gatePrefixLikelihood ((p:ℝ)-1/2) z.2.1.val (wordHeads z.2.2))) := by
  have hm (p : unitInterval) : Measurable (fun z : R × CappedWord M =>
      wordLikelihood p z.2.1.val (wordHeads z.2.2)) :=
    (measurable_of_countable (fun w : CappedWord M => wordLikelihood p w.1.val (wordHeads w.2))).comp measurable_snd
  have hL : Measurable (fun z : R × CappedWord M =>
      ENNReal.ofReal (gatePrefixLikelihood ((p:ℝ)-1/2) z.2.1.val (wordHeads z.2.2))) :=
    (measurable_of_countable (fun w : CappedWord M =>
      ENNReal.ofReal (gatePrefixLikelihood ((p:ℝ)-1/2) w.1.val (wordHeads w.2)))).comp measurable_snd
  rw [coinTranscriptLaw_density ν p A M hcap,coinTranscriptLaw_density ν _ A M hcap,
    ← withDensity_mul _ (hm _) hL]
  congr 1
  funext z
  apply wordLikelihood_fair_factor
  unfold wordHeads
  simpa using Finset.card_filter_le (s := Finset.univ) (fun i => z.2.2 i = true)

theorem coinTranscriptLaw_integral_fair {R E : Type} [MeasurableSpace R] [MeasurableSpace E]
    (ν : Measure R) [IsProbabilityMeasure ν] (p : unitInterval) (hp : |(p:ℝ)-1/2| ≤ 1/4)
    (A : StoppedProcedure R E) (M : ℕ) (hcap : ∀ z, A.stop z ≤ M)
    (F : R × CappedWord M → ℝ) (hF : Measurable F) :
    (∫ z, F (cappedTranscript A M z) ∂ν.prod (tapeMeasure p)) =
      ∫ z, gatePrefixLikelihood ((p:ℝ)-1/2) (cappedTranscript A M z).2.1.val
        (wordHeads (cappedTranscript A M z).2.2)*F (cappedTranscript A M z)
        ∂ν.prod (tapeMeasure ⟨1/2,by norm_num⟩) := by
  let L : R × CappedWord M → ℝ := fun z => gatePrefixLikelihood ((p:ℝ)-1/2) z.2.1.val (wordHeads z.2.2)
  have hL : Measurable L := (measurable_of_countable (fun w : CappedWord M =>
    gatePrefixLikelihood ((p:ℝ)-1/2) w.1.val (wordHeads w.2))).comp measurable_snd
  calc
    _ = ∫ z, F z ∂coinTranscriptLaw ν p A M :=
      (integral_map (measurable_cappedTranscript A M).aemeasurable hF.aestronglyMeasurable).symm
    _ = ∫ z, L z*F z ∂coinTranscriptLaw ν ⟨1/2,by norm_num⟩ A M := by
      rw [coinTranscriptLaw_fair_density ν p A M hcap]
      change (∫ z, F z ∂(coinTranscriptLaw ν ⟨1/2,by norm_num⟩ A M).withDensity
        (fun z => ENNReal.ofReal (L z))) = _
      rw [integral_withDensity_eq_integral_toReal_smul
        (show Measurable (fun z => ENNReal.ofReal (L z)) from ENNReal.measurable_ofReal.comp hL)
        (ae_of_all _ (fun _ => ENNReal.ofReal_lt_top))]
      apply integral_congr_ae
      exact ae_of_all _ (fun z => by
        dsimp only [L]
        rw [ENNReal.toReal_ofReal (gatePrefixLikelihood_positive _ hp _ _).le,smul_eq_mul])
    _ = _ := integral_map (measurable_cappedTranscript A M).aemeasurable (hL.mul hF).aestronglyMeasurable

theorem integral_product_square_le {X : Type} [MeasurableSpace X]
    (μ : Measure X) (f g : X → ℝ) (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    (∫ x, f x*g x ∂μ)^2 ≤ (∫ x, (f x)^2 ∂μ)*(∫ x, (g x)^2 ∂μ) := by
  let I := ∫ x, f x*g x ∂μ
  let B := ∫ x, (g x)^2 ∂μ
  have hB : 0 ≤ B := integral_nonneg (fun x => sq_nonneg _)
  by_cases hz : B = 0
  · have hgz := (integral_eq_zero_iff_of_nonneg (fun x => sq_nonneg (g x)) hg.integrable_sq).mp hz
    have hi : I = 0 := by
      calc
        _ = ∫ _x, (0:ℝ) ∂μ := integral_congr_ae (hgz.mono (fun x hx => by
          have hgx : g x = 0 := sq_eq_zero_iff.mp hx
          simp [hgx]))
        _ = 0 := integral_zero _ _
    change I^2 ≤ _*B
    rw [hi,hz]
    norm_num
  have hBp : 0 < B := lt_of_le_of_ne hB (Ne.symm hz)
  let c := I/B
  have hc : c*B = I := div_mul_cancel₀ _ hz
  have hfg : Integrable (fun x => f x*g x) μ := hf.integrable_mul hg
  have hnonneg : 0 ≤ ∫ x, (f x-c*g x)^2 ∂μ := integral_nonneg (fun x => sq_nonneg _)
  have he : (∫ x, (f x-c*g x)^2 ∂μ) =
      (∫ x, (f x)^2 ∂μ)-2*c*I+c^2*B := by
    calc
      _ = ∫ x, ((f x)^2-(2*c)*(f x*g x)+c^2*(g x)^2) ∂μ :=
        integral_congr_ae (ae_of_all _ (fun x => by ring))
      _ = _ := by
        have hscale := hfg.const_mul (2*c)
        have hadd := integral_add (hf.integrable_sq.sub hscale) (hg.integrable_sq.const_mul (c^2))
        simp only [Pi.sub_apply] at hadd
        rw [hadd,integral_sub hf.integrable_sq hscale,integral_const_mul,integral_const_mul]
  rw [he,← hc] at hnonneg
  have hbound : c^2*B ≤ ∫ x, (f x)^2 ∂μ := by nlinarith only [hnonneg]
  change I^2 ≤ _*B
  rw [← hc]
  nlinarith only [mul_le_mul_of_nonneg_right hbound hBp.le]

theorem earlyProcedure_fair_secondMoment_le {R : Type} [MeasurableSpace R]
    (ν : Measure R) [IsProbabilityMeasure ν] (A : StoppedProcedure R ℝ)
    (a : ℝ) (ha : 0 < a) (ha4 : a ≤ 1/4)
    (p : unitInterval) (hp : |(p:ℝ)-1/2| ≤ a) :
    conditionalSecondMoment ν ⟨1/2,by norm_num⟩ (earlyProcedure A ⌈(a^2)⁻¹⌉₊ ⌈a⁻¹⌉₊) ≤
      ENNReal.ofReal (exp 12)*conditionalSecondMoment ν p A := by
  let E := earlyProcedure A ⌈(a^2)⁻¹⌉₊ ⌈a⁻¹⌉₊
  let G := activationGate A ⌈(a^2)⁻¹⌉₊ ⌈a⁻¹⌉₊
  let F := transcriptOutput E ⌈(a^2)⁻¹⌉₊
  have hF : Measurable F := measurable_transcriptOutput E _
  have he (z : R × (ℕ → Bool)) : F (cappedTranscript G ⌈(a^2)⁻¹⌉₊ z) = E.output z :=
    transcriptOutput_eq E _ z (activationGate_stop_le A _ _ z).2
  have hl := (activationGate_lintegral_comparison ν A a ha ha4 p hp
    (fun z => ENNReal.ofReal ((F z)^2)) (ENNReal.measurable_ofReal.comp (hF.pow_const 2))).1
  change ENNReal.ofReal (exp (-12))*(∫⁻ z, ENNReal.ofReal ((F (cappedTranscript G _ z))^2)
    ∂ν.prod (tapeMeasure ⟨1/2,by norm_num⟩)) ≤
    ∫⁻ z, ENNReal.ofReal ((F (cappedTranscript G _ z))^2) ∂ν.prod (tapeMeasure p) at hl
  simp only [he] at hl
  change ENNReal.ofReal (exp (-12))*conditionalSecondMoment ν ⟨1/2,by norm_num⟩ E ≤
    conditionalSecondMoment ν p E at hl
  have hc : ENNReal.ofReal (exp 12)*ENNReal.ofReal (exp (-12)) = 1 := by
    rw [← ENNReal.ofReal_mul (exp_pos _).le,← exp_add]
    norm_num
  have h := mul_le_mul' (le_refl (ENNReal.ofReal (exp 12))) hl
  rw [← mul_assoc,hc,one_mul] at h
  exact h.trans (mul_le_mul' le_rfl (earlyProcedure_secondMoment_le ν p A _ _))

theorem earlyProcedure_mean_fair {R : Type} [MeasurableSpace R]
    (ν : Measure R) [IsProbabilityMeasure ν] (p : unitInterval) (hp : |(p:ℝ)-1/2| ≤ 1/4)
    (A : StoppedProcedure R ℝ) (M H : ℕ) :
    conditionalMean ν p (earlyProcedure A M H) =
      ∫ z, gatePrefixLikelihood ((p:ℝ)-1/2) (activationGateCost A M H z)
        (wordHeads (tapePrefix (activationGateCost A M H z) z.2))*(earlyProcedure A M H).output z
        ∂ν.prod (tapeMeasure ⟨1/2,by norm_num⟩) := by
  let E := earlyProcedure A M H
  have hcap : ∀ z, E.stop z ≤ M := fun z => (activationGate_stop_le A M H z).2
  have h := coinTranscriptLaw_integral_fair ν p hp E M hcap (transcriptOutput E M)
    (measurable_transcriptOutput E M)
  have ho (z : R × (ℕ → Bool)) := transcriptOutput_eq E M z (hcap z)
  simp only [ho] at h
  change conditionalMean ν p E = _ at h
  rw [h]
  apply integral_congr_ae
  exact ae_of_all _ (fun z => by
    dsimp only
    rw [cappedTranscript_of_stop E M (activationGateCost A M H z) (activationGate_bounds A M H z).1 z rfl])

def stoppedGateLikelihood {R E : Type} [MeasurableSpace R] [MeasurableSpace E]
    (A : StoppedProcedure R E) (M H : ℕ) (d : ℝ) (z : R × (ℕ → Bool)) : ℝ :=
  gatePrefixLikelihood d (cappedTranscript (activationGate A M H) M z).2.1.val
    (wordHeads (cappedTranscript (activationGate A M H) M z).2.2)

theorem measurable_stoppedGateLikelihood {R E : Type} [MeasurableSpace R] [MeasurableSpace E]
    (A : StoppedProcedure R E) (M H : ℕ) (d : ℝ) : Measurable (stoppedGateLikelihood A M H d) :=
  ((measurable_of_countable (fun w : CappedWord M => gatePrefixLikelihood d w.1.val (wordHeads w.2))).comp
    measurable_snd).comp (measurable_cappedTranscript _ _)

theorem stoppedGateLikelihood_eq {R E : Type} [MeasurableSpace R] [MeasurableSpace E]
    (A : StoppedProcedure R E) (M H : ℕ) (d : ℝ) (z : R × (ℕ → Bool)) :
    stoppedGateLikelihood A M H d z = gatePrefixLikelihood d (activationGateCost A M H z)
      (wordHeads (tapePrefix (activationGateCost A M H z) z.2)) := by
  unfold stoppedGateLikelihood
  rw [cappedTranscript_of_stop _ M (activationGateCost A M H z) (activationGate_bounds A M H z).1 z rfl]

theorem earlyProcedure_mean_difference_fair {R : Type} [MeasurableSpace R]
    (ν : Measure R) [IsProbabilityMeasure ν] (A : StoppedProcedure R ℝ)
    (a : ℝ) (ha : 0 < a) (ha4 : a ≤ 1/4)
    (p q : unitInterval) (hp : |(p:ℝ)-1/2| ≤ a) (hpq : (p:ℝ)+(q:ℝ) = 1)
    (hM : conditionalSecondMoment ν ⟨1/2,by norm_num⟩ (earlyProcedure A ⌈(a^2)⁻¹⌉₊ ⌈a⁻¹⌉₊) ≠ ∞) :
    (conditionalMean ν p (earlyProcedure A ⌈(a^2)⁻¹⌉₊ ⌈a⁻¹⌉₊)-
      conditionalMean ν q (earlyProcedure A ⌈(a^2)⁻¹⌉₊ ⌈a⁻¹⌉₊))^2 ≤
      64*exp 24*((p:ℝ)-1/2)^2*
        (conditionalSecondMoment ν ⟨1/2,by norm_num⟩ (earlyProcedure A ⌈(a^2)⁻¹⌉₊ ⌈a⁻¹⌉₊)).toReal*
        (expectedStoppedProcedureWork ν ⟨1/2,by norm_num⟩ (activationGate A ⌈(a^2)⁻¹⌉₊ ⌈a⁻¹⌉₊)).toReal := by
  let E := earlyProcedure A ⌈(a^2)⁻¹⌉₊ ⌈a⁻¹⌉₊
  let ξ := ν.prod (tapeMeasure ⟨1/2,by norm_num⟩)
  let L := stoppedGateLikelihood A ⌈(a^2)⁻¹⌉₊ ⌈a⁻¹⌉₊
  let d := (p:ℝ)-1/2
  have hq : (q:ℝ)-1/2 = -d := by dsimp [d]; linarith
  have hqbound : |(q:ℝ)-1/2| ≤ 1/4 := by rw [hq,abs_neg]; exact hp.trans ha4
  have hY : MemLp E.output 2 ξ :=
    (memLp_map_measure_iff measurable_id.aestronglyMeasurable E.measurable_output.aemeasurable).mp
      ((conditionalSecondMoment_finite_iff ν ⟨1/2,by norm_num⟩ E).mp hM)
  have hL (d' : ℝ) (hd' : |d'| ≤ a) : MemLp (L d') 2 ξ := by
    apply MemLp.of_bound (measurable_stoppedGateLikelihood A _ _ d').aestronglyMeasurable (exp 12)
    exact ae_of_all _ (fun z => by
      change |stoppedGateLikelihood A _ _ d' z| ≤ exp 12
      rw [stoppedGateLikelihood_eq,abs_of_pos (gatePrefixLikelihood_positive d' (hd'.trans ha4) _ _)]
      exact (activationGate_prefix_likelihood A a d' ha ha4 hd' z).2)
  have hLp := hL d hp
  have hLm := hL (-d) (by rw [abs_neg]; exact hp)
  have hmean : conditionalMean ν p E-conditionalMean ν q E =
      ∫ z, E.output z*(L d z-L (-d) z) ∂ξ := by
    rw [earlyProcedure_mean_fair ν p (hp.trans ha4),earlyProcedure_mean_fair ν q hqbound]
    simp_rw [← stoppedGateLikelihood_eq,hq]
    change (∫ z, L d z*E.output z ∂ξ)-(∫ z, L (-d) z*E.output z ∂ξ) = _
    have hs := integral_sub (hLp.integrable_mul hY) (hLm.integrable_mul hY)
    simp only [Pi.mul_apply] at hs
    rw [← hs]
    exact integral_congr_ae (ae_of_all _ (fun z => by dsimp only [Pi.sub_apply,L]; ring))
  have hcs := integral_product_square_le ξ E.output (fun z => L d z-L (-d) z) hY (hLp.sub hLm)
  have hpoint (z : R × (ℕ → Bool)) : (L d z-L (-d) z)^2 ≤
      (64*exp 24*d^2)*(tapeBalance (activationGateCost A ⌈(a^2)⁻¹⌉₊ ⌈a⁻¹⌉₊ z) z.2:ℝ)^2 := by
    have hdiff := activationGate_prefix_likelihood_difference A a d ha ha4 hp z
    have hdif : |L d z-L (-d) z| ≤ 8*exp 12*|d| *
        |(tapeBalance (activationGateCost A ⌈(a^2)⁻¹⌉₊ ⌈a⁻¹⌉₊ z) z.2:ℝ)| := by
      simpa only [L,stoppedGateLikelihood_eq] using hdiff
    have hs := (sq_le_sq₀ (abs_nonneg _) (by positivity)).mpr hdif
    have he : exp 12^2 = exp 24 := by rw [sq,← exp_add]; norm_num
    simpa only [sq_abs,mul_pow,he,show (8:ℝ)^2 = 64 by norm_num] using hs
  have hi := integral_mono (hLp.sub hLm).integrable_sq
    ((integrable_activationGate_square ν ⟨1/2,by norm_num⟩ A _ _).const_mul (64*exp 24*d^2)) hpoint
  rw [integral_const_mul,activationGate_fair_square_identity,
    ← expected_activationGate_work_toReal] at hi
  have hmoment : (∫ z, (E.output z)^2 ∂ξ) = (conditionalSecondMoment ν ⟨1/2,by norm_num⟩ E).toReal :=
    integral_eq_lintegral_of_nonneg_ae (ae_of_all _ (fun z => sq_nonneg _))
      (E.measurable_output.pow_const 2).aestronglyMeasurable
  change (conditionalMean ν p E-conditionalMean ν q E)^2 ≤ _
  rw [hmean]
  calc
    _ ≤ _ := hcs
    _ ≤ (∫ z, (E.output z)^2 ∂ξ)*((64*exp 24*d^2)*
        (expectedStoppedProcedureWork ν ⟨1/2,by norm_num⟩ (activationGate A ⌈(a^2)⁻¹⌉₊ ⌈a⁻¹⌉₊)).toReal) :=
      mul_le_mul_of_nonneg_left hi (integral_nonneg (fun z => sq_nonneg _))
    _ = _ := by rw [hmoment]; ring

theorem population_early_fair_secondMoment_le {D R : Type} [MeasurableSpace D] [MeasurableSpace R]
    (μ : Measure D) [IsProbabilityMeasure μ] (ν : Measure R) [IsProbabilityMeasure ν]
    (p₀ p₁ : D → unitInterval) (h₀ : Measurable p₀) (h₁ : Measurable p₁)
    (A : StoppedProcedure R ℝ) (a : ℝ) (ha : 0 < a) (ha4 : a ≤ 1/4)
    (hclose : ∀ᵐ d ∂μ, |(p₀ d:ℝ)-1/2| ≤ a) :
    conditionalSecondMoment ν ⟨1/2,by norm_num⟩ (earlyProcedure A ⌈(a^2)⁻¹⌉₊ ⌈a⁻¹⌉₊) ≤
      ENNReal.ofReal (exp 12)*populationSecondMoment μ ν p₀ p₁ (fun _ => 0) A := by
  have hp : ∀ᵐ d ∂μ,
      conditionalSecondMoment ν ⟨1/2,by norm_num⟩ (earlyProcedure A ⌈(a^2)⁻¹⌉₊ ⌈a⁻¹⌉₊) ≤
        ENNReal.ofReal (exp 12)*conditionalSecondMoment ν (p₀ d) A :=
    hclose.mono (fun d hd => earlyProcedure_fair_secondMoment_le ν A a ha ha4 (p₀ d) hd)
  have h := lintegral_mono_ae hp
  rw [lintegral_const,measure_univ,mul_one,lintegral_const_mul' _ _ ENNReal.ofReal_ne_top] at h
  rw [population_second_moment_formula _ _ _ _ _ h₀ h₁ measurable_const]
  simpa using h

theorem population_gate_fair_work_le {D R : Type} [MeasurableSpace D] [MeasurableSpace R]
    (μ : Measure D) [IsProbabilityMeasure μ] (ν : Measure R) [IsProbabilityMeasure ν]
    (p₀ p₁ : D → unitInterval) (h₀ : Measurable p₀) (h₁ : Measurable p₁)
    (A : StoppedProcedure R ℝ) (a : ℝ) (ha : 0 < a) (ha4 : a ≤ 1/4)
    (hclose : ∀ᵐ d ∂μ, |(p₀ d:ℝ)-1/2| ≤ a) :
    expectedStoppedProcedureWork ν ⟨1/2,by norm_num⟩ (activationGate A ⌈(a^2)⁻¹⌉₊ ⌈a⁻¹⌉₊) ≤
      ENNReal.ofReal (exp 12)*populationExpectedWork μ ν p₀ p₁ (fun _ => 0) A := by
  have hp : ∀ᵐ d ∂μ,
      expectedStoppedProcedureWork ν ⟨1/2,by norm_num⟩ (activationGate A ⌈(a^2)⁻¹⌉₊ ⌈a⁻¹⌉₊) ≤
        ENNReal.ofReal (exp 12)*expectedStoppedProcedureWork ν (p₀ d) A :=
    hclose.mono (fun d hd => activationGate_fair_work_le_biased ν A a ha ha4 (p₀ d) hd)
  have h := lintegral_mono_ae hp
  rw [lintegral_const,measure_univ,mul_one,lintegral_const_mul' _ _ ENNReal.ofReal_ne_top] at h
  rw [population_work_formula _ _ _ _ _ h₀ h₁ measurable_const]
  simpa using h

theorem population_early_mean_difference {D R : Type} [MeasurableSpace D] [MeasurableSpace R]
    (μ : Measure D) [IsProbabilityMeasure μ] (ν : Measure R) [IsProbabilityMeasure ν]
    (p₀ p₁ : D → unitInterval) (h₀ : Measurable p₀) (h₁ : Measurable p₁)
    (A : StoppedProcedure R ℝ) (a : ℝ) (ha : 0 < a) (ha4 : a ≤ 1/4)
    (hclose : ∀ᵐ d ∂μ, |(p₀ d:ℝ)-1/2| ≤ a)
    (hM : populationSecondMoment μ ν p₀ p₁ (fun _ => 0) A ≠ ∞)
    (hW : populationExpectedWork μ ν p₀ p₁ (fun _ => 0) A ≠ ∞)
    (p q : unitInterval) (hp : |(p:ℝ)-1/2| ≤ a) (hpq : (p:ℝ)+(q:ℝ) = 1) :
    (conditionalMean ν p (earlyProcedure A ⌈(a^2)⁻¹⌉₊ ⌈a⁻¹⌉₊)-
      conditionalMean ν q (earlyProcedure A ⌈(a^2)⁻¹⌉₊ ⌈a⁻¹⌉₊))^2 ≤
      64*exp 48*a^2*(populationSecondMoment μ ν p₀ p₁ (fun _ => 0) A).toReal*
        (populationExpectedWork μ ν p₀ p₁ (fun _ => 0) A).toReal := by
  have hmb := population_early_fair_secondMoment_le μ ν p₀ p₁ h₀ h₁ A a ha ha4 hclose
  have hwb := population_gate_fair_work_le μ ν p₀ p₁ h₀ h₁ A a ha ha4 hclose
  have hmf := ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hM) hmb
  have hmr := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hM) hmb
  have hwr := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hW) hwb
  rw [ENNReal.toReal_mul,ENNReal.toReal_ofReal (exp_pos 12).le] at hmr hwr
  have hbase := earlyProcedure_mean_difference_fair ν A a ha ha4 p q hp hpq hmf
  have hdsq : ((p:ℝ)-1/2)^2 ≤ a^2 := by
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) ha.le).mpr hp
  have he : exp 24*exp 12*exp 12 = exp 48 := by rw [← exp_add,← exp_add]; norm_num
  calc
    _ ≤ _ := hbase
    _ ≤ 64*exp 24*a^2*(exp 12*(populationSecondMoment μ ν p₀ p₁ (fun _ => 0) A).toReal)*
        (exp 12*(populationExpectedWork μ ν p₀ p₁ (fun _ => 0) A).toReal) :=
      mul_le_mul (mul_le_mul (mul_le_mul_of_nonneg_left hdsq (by positivity)) hmr
        ENNReal.toReal_nonneg (by positivity)) hwr ENNReal.toReal_nonneg (by positivity)
    _ = _ := by
      calc
        _ = 64*(exp 24*exp 12*exp 12)*a^2*(populationSecondMoment μ ν p₀ p₁ (fun _ => 0) A).toReal*
          (populationExpectedWork μ ν p₀ p₁ (fun _ => 0) A).toReal := by ring
        _ = _ := by rw [he]

theorem gated_mean_zero_of_fair_activation_zero {R : Type} [MeasurableSpace R]
    (ν : Measure R) [IsProbabilityMeasure ν] (A : StoppedProcedure R ℝ)
    (a : ℝ) (ha : 0 < a) (ha4 : a ≤ 1/4)
    (hzero : (ν.prod (tapeMeasure ⟨1/2,by norm_num⟩)).real
      {z | (activationGate A ⌈(a^2)⁻¹⌉₊ ⌈a⁻¹⌉₊).output z = true} = 0)
    (p : unitInterval) (hp : |(p:ℝ)-1/2| ≤ a) :
    conditionalMean ν p (gatedProcedure A ⌈(a^2)⁻¹⌉₊ ⌈a⁻¹⌉₊) = 0 := by
  have hf : (ν.prod (tapeMeasure ⟨1/2,by norm_num⟩))
      {z | (activationGate A ⌈(a^2)⁻¹⌉₊ ⌈a⁻¹⌉₊).output z = true} = 0 := by
    rw [← ENNReal.ofReal_toReal (measure_ne_top _ _)]
    change ENNReal.ofReal ((ν.prod (tapeMeasure ⟨1/2,by norm_num⟩)).real _) = 0
    rw [hzero]
    simp
  have hb := (activationGate_probability_comparison ν A a ha ha4 p hp).2
  rw [hf,mul_zero] at hb
  have hprob := le_zero_iff.mp hb
  have hae : ∀ᵐ z ∂ν.prod (tapeMeasure p),
      z ∉ {z | (activationGate A ⌈(a^2)⁻¹⌉₊ ⌈a⁻¹⌉₊).output z = true} := by
    rw [ae_iff]
    simpa only [not_not,Set.mem_ofPred_eq] using hprob
  change (∫ z, (gatedProcedure A ⌈(a^2)⁻¹⌉₊ ⌈a⁻¹⌉₊).output z ∂ν.prod (tapeMeasure p)) = 0
  rw [gatedProcedure_output]
  apply integral_eq_zero_of_ae
  filter_upwards [hae] with z hz
  exact Set.indicator_of_notMem hz A.output

theorem capped_guarantee_integrated_mean_separation {D R : Type}
    [MeasurableSpace D] [MeasurableSpace R]
    (μ : Measure D) [IsProbabilityMeasure μ] (ν : Measure R) [IsProbabilityMeasure ν]
    (p₀ p₁ : D → unitInterval) (h₀ : Measurable p₀) (h₁ : Measurable p₁)
    (A : StoppedProcedure R ℝ) (ρ : unitInterval) (hρ : 0 < (ρ:ℝ)) (hρ4 : (ρ:ℝ) ≤ 1/4)
    (m : ℝ) (hguar : CappedPopulationGuarantee μ ν p₀ p₁ A (ρ:ℝ) m) :
    (31:ℝ)/32 ≤ ∫ d, conditionalMean ν (p₁ d) A-conditionalMean ν (p₀ d) A ∂μ := by
  have hc₀ := cappedPrior_const μ (ρ:ℝ) 0 (by norm_num) (by simpa using hρ.le)
  have hcρ := cappedPrior_const μ (ρ:ℝ) ρ (by linarith) le_rfl
  have hm₀ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hguar.moment _ hc₀)
  have hm₁ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hguar.moment _ hcρ)
  have hb₀ := hguar.bias _ hc₀
  have hbρ := hguar.bias _ hcρ
  norm_num at hb₀
  simp only [integral_const,probReal_univ,one_smul] at hbρ
  have he := population_eventPrior_mean μ ν p₀ p₁ h₀ h₁ ρ hρ A hm₀ hm₁ univ MeasurableSet.univ ρ
  have hev : eventPrior (univ : Set D) ρ = (fun _ => ρ) := by funext d; simp [eventPrior]
  rw [hev,setIntegral_univ] at he
  apply (mul_le_mul_iff_right₀ hρ).mp
  linarith [(abs_le.mp hb₀).2,(abs_le.mp hbρ).1]

theorem fair_activation_positive_of_small_work {D R : Type}
    [MeasurableSpace D] [MeasurableSpace R]
    (μ : Measure D) [IsProbabilityMeasure μ] (ν : Measure R) [IsProbabilityMeasure ν]
    (p₀ p₁ : D → unitInterval) (h₀ : Measurable p₀) (h₁ : Measurable p₁)
    (A : StoppedProcedure R ℝ) (ρ : unitInterval) (hρ : 0 < (ρ:ℝ)) (hρ4 : (ρ:ℝ) ≤ 1/4)
    (m : ℝ) (hm : 0 ≤ m) (hguar : CappedPopulationGuarantee μ ν p₀ p₁ A (ρ:ℝ) m)
    (a : ℝ) (ha : 0 < a) (ha4 : a ≤ 1/4)
    (hclose : ∀ᵐ d ∂μ, |(p₀ d:ℝ)-1/2| ≤ a ∧ (p₀ d:ℝ)+(p₁ d:ℝ) = 1)
    (hsmall : 64*exp 48*a^2*m*(populationExpectedWork μ ν p₀ p₁ (fun _ => 0) A).toReal ≤ 1/16) :
    0 < (ν.prod (tapeMeasure ⟨1/2,by norm_num⟩)).real
      {z | (activationGate A ⌈(a^2)⁻¹⌉₊ ⌈a⁻¹⌉₊).output z = true} := by
  by_contra hn
  have hzero := le_antisymm (le_of_not_gt hn) measureReal_nonneg
  have hc₀ := cappedPrior_const μ (ρ:ℝ) 0 (by norm_num) (by simpa using hρ.le)
  have hcρ := cappedPrior_const μ (ρ:ℝ) ρ (by linarith) le_rfl
  have hm₀ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hguar.moment _ hc₀)
  have hm₁ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hguar.moment _ hcρ)
  have hf := population_conditional_finiteness μ ν p₀ p₁ h₀ h₁ ρ hρ A
    hm₀ hm₁ (hguar.work _ hc₀) (hguar.work _ hcρ)
  have hmoment := ENNReal.toReal_mono ENNReal.ofReal_ne_top (hguar.moment _ hc₀)
  rw [ENNReal.toReal_ofReal hm] at hmoment
  have hbound : ∀ᵐ d ∂μ, conditionalMean ν (p₁ d) A-conditionalMean ν (p₀ d) A ≤ 1/4 := by
    filter_upwards [hf.1,hclose] with d hd hp
    have hp₁ : |(p₁ d:ℝ)-1/2| ≤ a := by
      have he : (p₁ d:ℝ)-1/2 = -((p₀ d:ℝ)-1/2) := by linarith [hp.2]
      simpa only [he,abs_neg] using hp.1
    have hz₀ := gated_mean_zero_of_fair_activation_zero ν A a ha ha4 hzero (p₀ d) hp.1
    have hz₁ := gated_mean_zero_of_fair_activation_zero ν A a ha ha4 hzero (p₁ d) hp₁
    have he₀ := early_gated_mean_sum ν (p₀ d) A ((conditionalSecondMoment_finite_iff _ _ _).mpr hd.1)
      ⌈(a^2)⁻¹⌉₊ ⌈a⁻¹⌉₊
    have he₁ := early_gated_mean_sum ν (p₁ d) A ((conditionalSecondMoment_finite_iff _ _ _).mpr hd.2.1)
      ⌈(a^2)⁻¹⌉₊ ⌈a⁻¹⌉₊
    rw [hz₀,add_zero] at he₀
    rw [hz₁,add_zero] at he₁
    have hearly := population_early_mean_difference μ ν p₀ p₁ h₀ h₁ A a ha ha4
      (hclose.mono (fun _ h => h.1)) hm₀ (hguar.work _ hc₀) (p₁ d) (p₀ d) hp₁ (by linarith [hp.2])
    rw [he₀,he₁] at hearly
    have hscale := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hmoment (by positivity : 0 ≤ 64*exp 48*a^2))
      (ENNReal.toReal_nonneg (a := populationExpectedWork μ ν p₀ p₁ (fun _ => 0) A))
    have hs := hearly.trans (hscale.trans hsmall)
    nlinarith only [hs]
  have hi := integral_mono_ae (hf.2.2.sub hf.2.1) (integrable_const (1/4:ℝ)) hbound
  simp only [integral_const,probReal_univ,one_smul,Pi.sub_apply] at hi
  have hlo := capped_guarantee_integrated_mean_separation μ ν p₀ p₁ h₀ h₁ A ρ hρ hρ4 m hguar
  linarith

end ThresholdHC.EntropyTailLower
