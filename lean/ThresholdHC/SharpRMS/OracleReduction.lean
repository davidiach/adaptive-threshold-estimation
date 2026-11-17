import ThresholdHC.SharpRMS.OracleLaw
import ThresholdHC.SharpRMS.Reduction

/-! A uniformly budgeted oracle protocol can be run in the ordinary single-gap experiment. -/
noncomputable section
namespace ThresholdHC.SharpRMS
open MeasureTheory Tier3 Tier5 Tier6 CriticalEntropy ContinuousObserved ObservableSimulation OracleLower
open scoped ENNReal

def oracleResponse {R : Type} [MeasurableSpace R] (A : OracleEstimator R) (g : Gap) (r : R × NoiseArray) :=
  localResponse (A.policy r.1) (fun i => coinDecoder (A.gap r.1 i) g 0 0 (r.2 i))

private theorem response_measurable {R : Type} [MeasurableSpace R] (A : OracleEstimator R) (g : Gap)
    (xs : List Bool) (b : Bool) : Measurable (fun r : R × NoiseArray => oracleResponse A g r xs b) :=
  measurable_localResponse (fun r : R × NoiseArray => A.policy r.1)
    (fun ys o => measurable_fst (A.policy_measurable ys o)) _
    (fun i ys y => (measurable_coinDecoder g 0 0 ys y).comp
      (((A.gap_measurable i).comp measurable_fst).prodMk ((measurable_pi_apply i).comp measurable_snd))) xs b

def oracleObservation {R : Type} [MeasurableSpace R] (A : OracleEstimator R) (g : Gap)
    (z : (R × NoiseArray) × ProcessTape) := (z.1.1,decodeTape (oracleResponse A g z.1) z.2)

private theorem observation_measurable {R : Type} [MeasurableSpace R] (A : OracleEstimator R) (g : Gap) :
    Measurable (oracleObservation A g) :=
  (measurable_fst.comp measurable_fst).prodMk (measurable_decodeTape _ (response_measurable A g))

def oracleSource {R : Type} [MeasurableSpace R] (μ : Measure Gap) (g : Gap) (A : OracleEstimator R) :
    AdaptiveEstimator (R × NoiseArray) where
  randomLaw := A.randomLaw.prod (Measure.infinitePi (fun _ : ℕ => uniformTapeMeasure))
  probability := inferInstance
  policy := fun r xs => A.policy r.1 (decode (oracleResponse A g r) xs)
  policy_measurable := by
    intro xs o
    have ma : Measurable (fun z : R × List Bool => A.policy z.1 z.2) :=
      measurable_from_prod_countable_left (fun ys => measurable_to_countable' (A.policy_measurable ys))
    exact (ma.comp (measurable_fst.prodMk (measurable_decode _ (response_measurable A g) xs))) (measurableSet_singleton o)
  output := fun z => (A.output (oracleObservation A g z)-(1-modulus μ g.val)/2)/modulus μ g.val
  output_measurable := ((A.output_measurable.comp (observation_measurable A g)).sub measurable_const).div_const _

theorem oracle_source_observations {R : Type} [MeasurableSpace R] (μ : Measure Gap) (g : Gap)
    (A : OracleEstimator R) (q : SignLaw) (F : R × ProcessTape → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ z, F (oracleObservation A g (z.1.1,z.2)) ∂experimentLaw (Measure.dirac g) (oracleSource μ g A) q) =
      ∫⁻ z, F z ∂oracleLaw A (sourceTarget g q) := by
  let S := oracleSource μ g A
  let N := Measure.infinitePi (fun _ : ℕ => uniformTapeMeasure)
  let U := Measure.infinitePi (fun _ : ℕ => originalPopulationTapeLaw (Measure.dirac g) q)
  have assoc := measurePreserving_prodAssoc A.randomLaw N U
  let G := fun z : R × (NoiseArray × RawArray) => F (z.1,oracleVirtualPath A g z)
  have mG : Measurable G := hF.comp (measurable_fst.prodMk (measurable_oracleVirtualPath A g))
  rw [original_observable_lintegral (Measure.dirac g) S q (fun z => F (oracleObservation A g z)) (hF.comp (observation_measurable A g)),
      ←oracle_virtual_law A g q,lintegral_map hF (measurable_fst.prodMk (measurable_oracleVirtualPath A g))]
  apply Eq.trans _ (assoc.lintegral_comp mG)
  apply lintegral_congr
  intro z
  apply congrArg F
  change (z.1.1,_) = (z.1.1,_)
  congr 1
  exact causal_population_path (A.policy z.1.1) (fun i => coinDecoder (A.gap z.1.1 i) g 0 0 (z.1.2 i)) z.2

theorem oracle_expected_work {R : Type} [MeasurableSpace R] (μ : Measure Gap) (g : Gap)
    (A : OracleEstimator R) (q : SignLaw) :
    expectedWork (Measure.dirac g) (oracleSource μ g A) q = oracleWork A (sourceTarget g q) := by
  let F := fun z : R × ProcessTape => totalProcessWork z.2
  have m : Measurable F := measurable_totalProcessWork Prod.snd
    (fun n b => measurableSet_eq_fun ((measurable_pi_apply n).comp measurable_snd) measurable_const)
  simpa only [expectedWork,oracleWork,F,oracleObservation,decodeTape_work] using oracle_source_observations μ g A q F m

theorem oracle_source_rms {R : Type} [MeasurableSpace R] (μ : Measure Gap) [IsProbabilityMeasure μ]
    (g : Gap) (A : OracleEstimator R) (q : SignLaw) :
    ENNReal.ofReal (modulus μ g.val) * rootMeanRisk (experimentLaw (Measure.dirac g) (oracleSource μ g A) q)
      (populationOutput (oracleSource μ g A)) (signMean (Measure.dirac g) q.val) =
    rootMeanRisk (oracleLaw A (sourceTarget g q)) A.output (signMean μ (sourceTarget g q).val) := by
  let ω := modulus μ g.val
  have hp : 0 < ω := modulus_pos μ g.property.1
  let S := oracleSource μ g A
  let m := signMean μ (sourceTarget g q).val
  let loss := fun z : R × ProcessTape => ENNReal.ofReal ((A.output z-m)^2)
  have ml : Measurable loss := ENNReal.measurable_ofReal.comp ((A.output_measurable.sub measurable_const).pow_const 2)
  have eq := oracle_source_observations μ g A q loss ml
  have mean : signMean (Measure.dirac g) q.val=q.val g := by simp [signMean]
  have aff (x : ℝ) : ω*((x-(1-ω)/2)/ω-q.val g) = x-m := by
    dsimp only [m]
    rw [source_target_mean]
    change ω*((x-(1-ω)/2)/ω-q.val g) = x-(1+(2*q.val g-1)*ω)/2
    field_simp [hp.ne']
    ring
  have sq : ENNReal.ofReal (ω^2)*squaredRisk (experimentLaw (Measure.dirac g) S q) (populationOutput S)
      (signMean (Measure.dirac g) q.val) = squaredRisk (oracleLaw A (sourceTarget g q)) A.output m := by
    unfold squaredRisk
    rw [←lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    apply Eq.trans _ eq
    apply lintegral_congr
    intro z
    rw [←ENNReal.ofReal_mul (sq_nonneg _),←mul_pow,mean]
    change ENNReal.ofReal ((ω*((A.output (oracleObservation A g (z.1.1,z.2))-(1-ω)/2)/ω-q.val g))^2) = _
    rw [aff]
  have result := congrArg (fun x : ℝ≥0∞ => x^(1/2:ℝ)) sq
  rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num),ofReal_square_rpow_half ω hp.le] at result
  exact result

theorem oracle_gap_reduction {R : Type} [MeasurableSpace R] (μ : Measure Gap) [IsProbabilityMeasure μ]
    (g : Gap) (A : OracleEstimator R) (B : ℝ) (hb : OracleBudget A B) :
    ENNReal.ofReal (modulus μ g.val)*minimaxRisk (Measure.dirac g) B ≤ oracleRisk μ A := by
  let S := oracleSource μ g A
  have budget : UniformBudget (Measure.dirac g) S B := fun q =>
    (oracle_expected_work μ g A q).le.trans (hb (sourceTarget g q))
  have low : minimaxRisk (Measure.dirac g) B ≤ maximalRMSRisk (Measure.dirac g) S :=
    sInf_le ⟨R × NoiseArray,inferInstance,S,budget,rfl⟩
  apply (mul_le_mul_right low _).trans
  unfold maximalRMSRisk oracleRisk
  rw [ENNReal.mul_iSup]
  apply iSup_le
  intro q
  rw [oracle_source_rms μ g A q]
  exact le_iSup (fun p : SignLaw => rootMeanRisk (oracleLaw A p) A.output (signMean μ p.val)) (sourceTarget g q)

end ThresholdHC.SharpRMS
