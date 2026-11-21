import ThresholdHC.BiasSubtraction.Specification
import ThresholdHC.RareAboveTwo.Psi
import ThresholdHC.BlindUpper.FiniteProcedure
import ThresholdHC.CriticalEntropy.PopulationMixture

/-! The one-flip witness for the remark after Proposition prop:psi-null.

The procedure ignores its seed, reads one flip `X` and returns `Y = X - b`. Its
output lies in `[-b, 1-b]`, so Popoviciu's inequality bounds its variance by
`1/4` under every prior, and its work is identically one. Given the sign, its
mean is `p - b`, so under a prior `q` its bias on the remark's law is
`ε(1/2-d)(1-2q(d)) - b ∈ [-b, b]` whenever `q ≤ 1/2`. The allocation equal to
one at the atom `d` shows `Ψ(d) ≥ ε`, and `Ψ ≤ ρ` keeps `Ψ` finite. Hence a
valid obstruction constant is at most `1/4`, while `(Ψ(d) - c b)_+² / (K d²)` is
at least `ε²(1-c⁺/4)²/(K d²)`. -/
noncomputable section
namespace ThresholdHC.BiasSubtraction
open MeasureTheory ProbabilityTheory
open ThresholdHC.Tier6 ThresholdHC.CriticalEntropy ThresholdHC.ConfidenceLocalization
  ThresholdHC.ObservableSimulation ThresholdHC.RareAboveTwo
open scoped ENNReal

theorem remarkLaw_probability (d : Gap) : IsProbabilityMeasure (remarkLaw d) := by
  constructor
  simp only [remarkLaw, Measure.add_apply, Measure.smul_apply,
    Measure.dirac_apply_of_mem (Set.mem_univ _), smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_add (by norm_num) (by norm_num)]
  norm_num

theorem integral_remarkLaw (d : Gap) (f : Gap → ℝ) :
    ∫ x, f x ∂remarkLaw d = (1 - 1/2^10)*f ⟨1/2, by norm_num⟩ + (1/2^10)*f d := by
  have h₁ : Integrable f (Measure.dirac (⟨1/2, by norm_num⟩ : Gap)) :=
    integrable_dirac (by simp)
  have h₂ : Integrable f (Measure.dirac d) := integrable_dirac (by simp)
  rw [remarkLaw, integral_add_measure (h₁.smul_measure ENNReal.ofReal_ne_top)
    (h₂.smul_measure ENNReal.ofReal_ne_top), integral_smul_measure, integral_smul_measure,
    integral_dirac, integral_dirac, ENNReal.toReal_ofReal (by norm_num),
    ENNReal.toReal_ofReal (by norm_num), smul_eq_mul, smul_eq_mul]

/-- Stop after one flip and return that flip, coded `0/1`, minus `b`. -/
def oneFlipProcedure (b : ℝ) : StoppedProcedure Unit ℝ :=
  BlindUpper.finiteStoppedProcedure (fun _ => 1) (fun z => Tier2.bit (z.2 0) - b)
    measurable_const
    ((Tier2.measurable_bit.comp ((measurable_pi_apply 0).comp measurable_snd)).sub_const b)
    (fun _ ω ω' h => ⟨rfl, by
      have h0 := congrFun h ⟨0, Nat.one_pos⟩
      simp only [Tier2.tapePrefix] at h0
      simp [h0]⟩)

theorem oneFlip_output (b : ℝ) (z : Unit × (ℕ → Bool)) :
    (oneFlipProcedure b).output z = Tier2.bit (z.2 0) - b := rfl

theorem oneFlip_stop (b : ℝ) (z : Unit × (ℕ → Bool)) : (oneFlipProcedure b).stop z = 1 := rfl

theorem oneFlip_output_mem (b : ℝ) (z : Unit × (ℕ → Bool)) :
    (oneFlipProcedure b).output z ∈ Set.Icc (-b) (1 - b) := by
  rw [oneFlip_output]
  constructor <;> cases z.2 0 <;> simp [Tier2.bit]

theorem oneFlip_output_abs (b : ℝ) (z : Unit × (ℕ → Bool)) :
    |(oneFlipProcedure b).output z| ≤ 1 + |b| := by
  have h := oneFlip_output_mem b z
  exact abs_le.mpr ⟨by linarith [h.1, le_abs_self b], by linarith [h.2, neg_abs_le b]⟩

theorem oneFlip_conditionalMean (b : ℝ) (p : unitInterval) :
    conditionalMean (Measure.dirac ()) p (oneFlipProcedure b) = (p : ℝ) - b := by
  unfold conditionalMean
  rw [Measure.dirac_prod, integral_map (measurable_prodMk_left).aemeasurable
    (oneFlipProcedure b).measurable_output.aestronglyMeasurable]
  simp only [oneFlip_output]
  have hint : Integrable (fun x : ℕ → Bool => Tier2.bit (x 0)) (Tier2.tapeMeasure p) :=
    Integrable.of_bound (Tier2.measurable_observations 0).aestronglyMeasurable 1
      (ae_of_all _ (fun x => by unfold Tier2.bit; split <;> norm_num))
  rw [integral_sub hint (integrable_const b)]
  have h := Tier2.observations_mean p 0
  simp only [Tier2.observations] at h
  simp [h]

theorem oneFlip_work {D : Type} [MeasurableSpace D] (μ : Measure D) [IsProbabilityMeasure μ]
    (p₀ p₁ q : D → unitInterval) (b : ℝ) :
    populationExpectedWork μ (Measure.dirac ()) p₀ p₁ q (oneFlipProcedure b) = 1 := by
  have : IsProbabilityMeasure (populationMeasure μ (Measure.dirac ())) := by
    unfold populationMeasure; infer_instance
  unfold populationExpectedWork
  simp [stoppedProcedureWork, oneFlip_stop]

theorem oneFlip_evariance {D : Type} [MeasurableSpace D] (μ : Measure D) [IsProbabilityMeasure μ]
    (p₀ p₁ q : D → unitInterval) (h₀ : Measurable p₀) (h₁ : Measurable p₁) (hq : Measurable q)
    (b : ℝ) :
    evariance ((oneFlipProcedure b).output ∘ populationInput p₀ p₁ q)
      (populationMeasure μ (Measure.dirac ())) ≤ ENNReal.ofReal (1/4) := by
  have : IsProbabilityMeasure (populationMeasure μ (Measure.dirac ())) := by
    unfold populationMeasure; infer_instance
  have hm : Measurable ((oneFlipProcedure b).output ∘ populationInput p₀ p₁ q) :=
    (oneFlipProcedure b).measurable_output.comp (measurable_populationInput p₀ p₁ q h₀ h₁ hq)
  have hb : ∀ᵐ z ∂populationMeasure μ (Measure.dirac ()),
      ((oneFlipProcedure b).output ∘ populationInput p₀ p₁ q) z ∈ Set.Icc (-b) (1 - b) :=
    ae_of_all _ (fun z => oneFlip_output_mem b _)
  rw [← ofReal_variance (memLp_of_bounded hb hm.aestronglyMeasurable 2)]
  apply ENNReal.ofReal_le_ofReal
  calc _ ≤ (((1 - b) - (-b))/2)^2 := variance_le_sq_of_bounded hb hm.aemeasurable
    _ = 1/4 := by ring

theorem oneFlip_populationMean {D : Type} [MeasurableSpace D] (μ : Measure D)
    [IsProbabilityMeasure μ] (p₀ p₁ q : D → unitInterval) (h₀ : Measurable p₀)
    (h₁ : Measurable p₁) (hq : Measurable q) (b : ℝ) :
    populationMean μ (Measure.dirac ()) p₀ p₁ q (oneFlipProcedure b) =
      ∫ x, (q x : ℝ)*((p₁ x : ℝ) - b) + (1-(q x : ℝ))*((p₀ x : ℝ) - b) ∂μ := by
  have : IsProbabilityMeasure (populationMeasure μ (Measure.dirac ())) := by
    unfold populationMeasure; infer_instance
  have hm : Measurable ((oneFlipProcedure b).output ∘ populationInput p₀ p₁ q) :=
    (oneFlipProcedure b).measurable_output.comp (measurable_populationInput p₀ p₁ q h₀ h₁ hq)
  have hint : Integrable (fun z => (oneFlipProcedure b).output (populationInput p₀ p₁ q z))
      (populationMeasure μ (Measure.dirac ())) :=
    Integrable.of_bound hm.aestronglyMeasurable (1 + |b|)
      (ae_of_all _ (fun z => by
        rw [Real.norm_eq_abs]; exact oneFlip_output_abs b _))
  have h := population_integral μ (Measure.dirac ()) p₀ p₁ q _
    (oneFlipProcedure b).measurable_output hint
  change populationMean μ (Measure.dirac ()) p₀ p₁ q (oneFlipProcedure b) = _ at h
  rw [h]
  have e (p : unitInterval) : (∫ z, (oneFlipProcedure b).output z
      ∂(Measure.dirac ()).prod (Tier2.tapeMeasure p)) = (p : ℝ) - b :=
    oneFlip_conditionalMean b p
  simp only [e]

theorem gapParameter_true_val (x : Gap) : (gapParameter true x : ℝ) = 1/2 + x := by
  simp [gapParameter]

theorem gapParameter_false_val (x : Gap) : (gapParameter false x : ℝ) = 1/2 - x := by
  simp [gapParameter, sub_eq_add_neg]

/-- The bias of `Y = X - b` on the remark's law is `ε(1/2-d)(1-2q(d)) - b ∈ [-b, b]`
for every capped prior. Only `q ≤ 1/2` is used. -/
theorem oneFlip_bias (d : Gap) (q : Gap → unitInterval)
    (hq : CappedPrior (remarkLaw d) (1/8) q) :
    |populationMean (remarkLaw d) (Measure.dirac ()) (gapParameter false) (gapParameter true) q
      (oneFlipProcedure (remarkBias d)) - ∫ x, (q x : ℝ) ∂remarkLaw d| ≤ remarkBias d := by
  have := remarkLaw_probability d
  rw [oneFlip_populationMean _ _ _ q (measurable_gapParameter false)
    (measurable_gapParameter true) hq.1, integral_remarkLaw, integral_remarkLaw]
  simp only [gapParameter_true_val, gapParameter_false_val]
  have h1 := (q d).property.1
  have h2 := hq.2.1 d
  have hd := d.property
  have k1 := mul_nonneg (sub_nonneg.2 hd.2) (by linarith : (0:ℝ) ≤ 1 - 2*(q d : ℝ))
  have k2 := mul_nonneg (sub_nonneg.2 hd.2) h1
  rw [abs_le]
  unfold remarkBias
  constructor <;> nlinarith

theorem rarePsi_le_rarity (μ : Measure Gap) [IsProbabilityMeasure μ] (ρ h : ℝ) (hh : 0 ≤ h) :
    rarePsi μ ρ h ≤ ENNReal.ofReal ρ :=
  iSup₂_le fun v hv => ENNReal.ofReal_le_ofReal (rareObjective_le_rarity μ ρ h hh v hv)

/-- The allocation equal to one at the atom `d` shows `Ψ(d) ≥ ε`. -/
theorem remark_psi_lower (d : Gap) (hd : (d : ℝ) < 1/2) :
    ENNReal.ofReal (1/2^10) ≤ rarePsi (remarkLaw d) (1/8) d := by
  have hne : (⟨1/2, by norm_num⟩ : Gap) ≠ d := by
    intro h
    rw [← h] at hd
    norm_num at hd
  have hd0 : (d : ℝ) ≠ 0 := d.property.1.ne'
  let w : Gap → ℝ := fun x => if x = d then 1 else 0
  have hw : w ⟨1/2, by norm_num⟩ = 0 := ite_eq_right hne
  have hwd : w d = 1 := ite_eq_left rfl
  have hfeas : Tier3.FeasibleAllocation (remarkLaw d) (1/8) w := by
    refine ⟨Measurable.ite (measurableSet_singleton d) measurable_const measurable_const,
      ae_of_all _ (fun x => ?_), ?_⟩
    · by_cases hx : x = d <;> simp [w, hx]
    · rw [integral_remarkLaw, hw, hwd]
      norm_num
  have hobj : Tier3.rareObjective (remarkLaw d) (fun x => (x : ℝ)) d w = 1/2^10 := by
    unfold Tier3.rareObjective
    rw [integral_remarkLaw]
    simp only [hw, hwd]
    simp [hd0]
  calc ENNReal.ofReal (1/2^10) = ENNReal.ofReal (Tier3.rareObjective (remarkLaw d)
        (fun x => (x : ℝ)) d w) := by rw [hobj]
    _ ≤ rarePsi (remarkLaw d) (1/8) d :=
      le_iSup₂ (f := fun (v : Gap → ℝ) (_ : Tier3.FeasibleAllocation (remarkLaw d) (1/8) v) =>
        ENNReal.ofReal (Tier3.rareObjective (remarkLaw d) (fun x => (x : ℝ)) d v)) w hfeas

theorem remark_psi_toReal (d : Gap) (hd : (d : ℝ) < 1/2) :
    1/2^10 ≤ (rarePsi (remarkLaw d) (1/8) d).toReal := by
  have := remarkLaw_probability d
  have htop : rarePsi (remarkLaw d) (1/8) d ≠ ∞ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top (rarePsi_le_rarity _ _ _ d.property.1.le)
  exact (ENNReal.ofReal_le_iff_le_toReal htop).mp (remark_psi_lower d hd)

theorem remarkBias_range (d : Gap) : 0 ≤ remarkBias d ∧ remarkBias d ≤ (1/8)/64 := by
  have hd := d.property
  unfold remarkBias
  constructor <;> nlinarith

/-- The one-flip procedure has variance at most `1/4` and null work one, so every
obstruction constant on the remark's law is at most `1/4`. -/
theorem not_obstruction_of_gt (d : Gap) (J : ℝ) (hJ : 1/4 < J) :
    ¬ NullVarianceObstruction (remarkLaw d) (gapParameter false) (gapParameter true) (1/8)
      (remarkBias d) J := by
  intro hobs
  have := remarkLaw_probability d
  have h := hobs (Measure.dirac ()) (oneFlipProcedure (remarkBias d)) 1
    (fun z => by rw [oneFlip_stop]; norm_num)
    ⟨1 + |remarkBias d|, oneFlip_output_abs _⟩ (1/4) (by norm_num)
    (fun q hq => oneFlip_evariance _ _ _ _ (measurable_gapParameter false)
      (measurable_gapParameter true) hq.1 _)
    (fun q hq => oneFlip_bias d q hq)
  rw [oneFlip_work] at h
  norm_num at h
  linarith

/-- With `a = ε(1 - c⁺/4) > 0`, every gap below `a/(K+1)` makes the reduced
right side exceed `1/4`. -/
theorem remark_bound_gt (c : ℝ) (hc : c < 4) (K : ℝ) (hK : 0 < K) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ d : Gap, (d : ℝ) < δ →
      1/4 < (max ((rarePsi (remarkLaw d) (1/8) d).toReal - c*remarkBias d) 0)^2 /
        (K*(d : ℝ)^2) := by
  set a : ℝ := (1/2^10)*(1 - max c 0/4) with ha_def
  have hc' : max c 0 < 4 := max_lt hc (by norm_num)
  have ha : 0 < a := by rw [ha_def]; nlinarith
  refine ⟨min (a/(K+1)) (1/4), lt_min (by positivity) (by norm_num), fun d hd => ?_⟩
  have hd0 := d.property.1
  have hda : (d : ℝ)*(K+1) < a :=
    (lt_div_iff₀ (by linarith)).mp (lt_of_lt_of_le hd (min_le_left _ _))
  have hd4 : (d : ℝ) < 1/4 := lt_of_lt_of_le hd (min_le_right _ _)
  have hψ := remark_psi_toReal d (by linarith)
  have hb := remarkBias_range d
  have hb' : remarkBias d ≤ (1/2^10)/4 := by unfold remarkBias; nlinarith
  have hcb : c*remarkBias d ≤ max c 0*((1/2^10)/4) :=
    (mul_le_mul_of_nonneg_right (le_max_left c 0) hb.1).trans
      (mul_le_mul_of_nonneg_left hb' (le_max_right c 0))
  have hM : a ≤ max ((rarePsi (remarkLaw d) (1/8) d).toReal - c*remarkBias d) 0 :=
    le_max_of_le_left (by rw [ha_def]; linarith)
  have hsq : a^2 ≤ (max ((rarePsi (remarkLaw d) (1/8) d).toReal - c*remarkBias d) 0)^2 :=
    pow_le_pow_left₀ ha.le hM 2
  have hsq' : ((d : ℝ)*(K+1))^2 < a^2 := pow_lt_pow_left₀ hda (by positivity) two_ne_zero
  have hpos : 0 ≤ (d : ℝ)^2*(K^2+K+1) := by positivity
  have hKd : K*(d : ℝ)^2 < a^2 := by nlinarith
  rw [lt_div_iff₀ (by positivity)]
  nlinarith

end ThresholdHC.BiasSubtraction
