import ThresholdHC.LawAdaptation.Moments
import ThresholdHC.LawAdaptation.Parity
import ThresholdHC.LawAdaptation.Pilot
import ThresholdHC.ObservableSimulation.OriginalExperiment

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
namespace ThresholdHC.LawAdaptation
open ThresholdHC.Tier6 ThresholdHC.ObservableSimulation ThresholdHC.CriticalEntropy

/-- Even-prefix parity is a function of observed flips alone. -/
def prefixParity (k : ℕ) (tape : ℕ → Bool) : ℝ :=
  parity (ThresholdHC.Tier2.tapePrefix (2*k) tape)

theorem measurable_prefixParity (k : ℕ) : Measurable (prefixParity k) :=
  (measurable_of_countable parity).comp (ThresholdHC.Tier2.measurable_prefix (2*k))

theorem abs_prefixParity (k : ℕ) (tape : ℕ → Bool) : |prefixParity k tape| = 1 :=
  parity_abs _

theorem bernoulli_prefixParity_mean (p : unitInterval) (k : ℕ) :
    ∫ tape, prefixParity k tape ∂ThresholdHC.Tier2.tapeMeasure p = (2*(p:ℝ)-1)^(2*k) := by
  simp only [prefixParity]
  rw [ThresholdHC.Tier2.integral_prefix]
  exact parity_mean (p:ℝ) (2*k)

private theorem parameter_tape_integral (κ : Measure unitInterval) [IsProbabilityMeasure κ]
    (F : (ℕ → Bool) → ℝ) (hF : Measurable F) {M : ℝ} (hb : ∀ t, |F t| ≤ M) :
    (∫ t, F t ∂parameterTapeLaw κ) =
      ∫ p, (∫ t, F t ∂ThresholdHC.Tier2.tapeMeasure p) ∂κ := by
  have hi := ThresholdHC.Tier5.integrable_of_abs_bound (κ.prod uniformTapeMeasure)
    (fun z => F (uniformCoinTape z.1 z.2)) (hF.comp measurable_uniformCoinTape) M
    (fun _ => hb _)
  rw [parameterTapeLaw, integral_map measurable_uniformCoinTape.aemeasurable
    hF.aestronglyMeasurable, integral_prod _ hi]
  apply integral_congr_ae
  apply ae_of_all
  intro p
  change (∫ u, F (uniformCoinTape p u) ∂uniformTapeMeasure) =
    ∫ t, F t ∂ThresholdHC.Tier2.tapeMeasure p
  have hm : Measurable (uniformCoinTape p) :=
    measurable_uniformCoinTape.comp (measurable_const.prodMk measurable_id)
  rw [← uniformCoinTape_map p]
  exact (integral_map hm.aemeasurable hF.aestronglyMeasurable).symm

/-- The actual population tape has the same even-parity mean for every sign law,
including signs depending measurably on the gap. -/
theorem original_prefixParity_mean (μ : Measure Gap) [IsProbabilityMeasure μ]
    (q : SignLaw) (k : ℕ) :
    ∫ tape, prefixParity k tape ∂originalPopulationTapeLaw μ q = evenMoment μ k := by
  let κ := populationParameterLaw μ (gapParameter false) (gapParameter true) (signUnit q)
  let : IsProbabilityMeasure κ := populationParameterLaw_probability μ
    (gapParameter false) (gapParameter true) (signUnit q)
    (measurable_gapParameter false) (measurable_gapParameter true) (measurable_signUnit q)
  change (∫ t, prefixParity k t ∂parameterTapeLaw κ) = _
  rw [parameter_tape_integral κ _ (measurable_prefixParity k)
    (fun t => (abs_prefixParity k t).le)]
  simp_rw [bernoulli_prefixParity_mean]
  have hb (p : unitInterval) : |(2*(p:ℝ)-1)^(2*k)| ≤ 1 := by
    rw [abs_pow]
    apply pow_le_one₀ (abs_nonneg _)
    rw [abs_le]
    rcases p.property with ⟨hp0,hp1⟩
    constructor <;> linarith
  rw [show κ = populationParameterLaw μ (gapParameter false) (gapParameter true)
      (signUnit q) from rfl,
    populationParameterLaw_integral μ _ _ _ (measurable_gapParameter false)
      (measurable_gapParameter true) (measurable_signUnit q) (fun p => (2*(p:ℝ)-1)^(2*k))
      (((measurable_const.mul measurable_subtype_coe).sub_const 1).pow_const (2*k)) 1 hb]
  apply integral_congr_ae
  apply ae_of_all
  intro d
  have hp : 2*(gapParameter true d:ℝ)-1 = 2*(d:ℝ) := by simp [gapParameter]; ring
  have hn : 2*(gapParameter false d:ℝ)-1 = -(2*(d:ℝ)) := by simp [gapParameter]; ring
  dsimp only
  rw [hp,hn,Even.neg_pow (even_two_mul k)]
  ring

/-- Independent persistent population coins, retaining their original labels. -/
def pilotTableLaw (μ : Measure Gap) (q : SignLaw) : Measure (ℕ → ℕ → Bool) :=
  Measure.infinitePi (fun _ : ℕ => originalPopulationTapeLaw μ q)

instance pilotTableLaw_probability (μ : Measure Gap) [IsProbabilityMeasure μ] (q : SignLaw) :
    IsProbabilityMeasure (pilotTableLaw μ q) := by
  unfold pilotTableLaw
  infer_instance

def pilotAverage (n k : ℕ) (table : ℕ → ℕ → Bool) : ℝ :=
  (∑ t : Fin n, prefixParity k (table t.val))/(n:ℝ)

/-- The concrete parity pilot satisfies the audited error bound on the original
population-tape law. Coordinates share coins; independence is only across coins. -/
theorem original_pilot_error {ι : Type*} [Nonempty ι]
    (laws : ι → Measure Gap) [∀ i, IsProbabilityMeasure (laws i)]
    (truth : ι) (q : SignLaw) {m n : ℕ} (hn : 0 < n) {η : ℝ} (hη : 0 < η)
    (hdist : ∀ i j, i ≠ j → ∃ k : Fin m,
      η ≤ |evenMoment (laws i) (k.val+1)-evenMoment (laws j) (k.val+1)|) :
    (pilotTableLaw (laws truth) q)
      {t | identify (fun i (k : Fin m) => evenMoment (laws i) (k.val+1))
        (fun k => pilotAverage n (k.val+1) t) (η/4) ≠ truth} ≤
      ENNReal.ofReal (2*(m:ℝ)*Real.exp (-(n:ℝ)*η^2/32)) := by
  let X (k : Fin m) (j : Fin n) (t : ℕ → ℕ → Bool) := prefixParity (k.val+1) (t j.val)
  apply pilot_error (pilotTableLaw (laws truth) q) hn
    (fun i (k : Fin m) => evenMoment (laws i) (k.val+1)) truth X hη hdist
  · intro k j
    exact ((measurable_prefixParity (k.val+1)).comp (measurable_pi_apply j.val)).aemeasurable
  · intro k j
    apply ae_of_all
    intro t
    have h := (abs_le.mp (abs_prefixParity (k.val+1) (t j.val)).le)
    exact h
  · intro k
    exact (iIndepFun_infinitePi (P := fun _ : ℕ => originalPopulationTapeLaw (laws truth) q)
      (fun _ => measurable_prefixParity (k.val+1))).precomp Fin.val_injective
  · intro k j
    change (∫ t, prefixParity (k.val+1) (t j.val)
      ∂Measure.infinitePi (fun _ : ℕ => originalPopulationTapeLaw (laws truth) q)) = _
    rw [← integral_map (measurable_pi_apply j.val).aemeasurable
      (measurable_prefixParity (k.val+1)).aestronglyMeasurable, Measure.infinitePi_map_eval]
    exact original_prefixParity_mean (laws truth) q (k.val+1)

end ThresholdHC.LawAdaptation

