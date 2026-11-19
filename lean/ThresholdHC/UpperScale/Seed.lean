import ThresholdHC.BlindUpper.BatchRealization

/-! The calibrated batch at a scale that need not be a power of two.

The batch machine of `BlindUpper` at level `L` runs pilot and production calls
of the padded classifier with cap `2^L`. A call with cost `C` is marked when its
uniform seed mark `u` satisfies `u < C/2^L`, so the calibration has scale
`2^L`, and the batch uses `4*2^L - E C` flips on average. Running the same
machine on a seed whose marks are multiplied by `t ≥ 1` marks a call when
`t*u < C/2^L`, that is, when `u < C/(t*2^L)`: the machine then realizes the
calibration with scale `t*2^L` (`scaledMark`), with the same calls and the same
output rule. `scaledEstimator L t` is that machine with the scaled seed.

Its expected work is the calibrated work at scale `t*2^L`, at most `4*t*2^L`
(`scaled_uniformBudget`), and its squared risk is the calibrated mean-square
error at that scale (`scaled_squaredRisk_eq`). Both follow from the identities
of `BlindUpper.ActualBatch` for the scaled seed, the identity
`callMark_scale`, and the law of the seed. -/
noncomputable section
namespace ThresholdHC.UpperScale
open MeasureTheory ThresholdHC.CriticalEntropy ThresholdHC.Tier3 ThresholdHC.ObservableSimulation
open ThresholdHC.Tier6 ThresholdHC.BlindUpper
open scoped ENNReal

/-- The ratio of the calibration scale to `2^L`; it is at least one. -/
def scaleRatio (t : ℝ) : ℝ := max t 1

theorem one_le_scaleRatio (t : ℝ) : 1 ≤ scaleRatio t := le_max_right _ _

theorem scaleRatio_pos (t : ℝ) : 0 < scaleRatio t := lt_of_lt_of_le one_pos (one_le_scaleRatio t)

theorem scaleRatio_of_one_le {t : ℝ} (h : 1 ≤ t) : scaleRatio t = t := max_eq_left h

/-- The calibration scale `t*2^L`. -/
def calScale (L : ℕ) (t : ℝ) : ℝ := scaleRatio t * (2 : ℝ) ^ L

theorem calScale_pos (L : ℕ) (t : ℝ) : 0 < calScale L t :=
  mul_pos (scaleRatio_pos t) (by positivity)

theorem paddedRealCost_scale_bounds (L : ℕ) (t : ℝ) (z : ℕ × (ℕ → Bool)) :
    0 ≤ paddedRealCost L z ∧ paddedRealCost L z ≤ calScale L t :=
  ⟨(paddedRealCost_bounds L z).1, (paddedRealCost_bounds L z).2.trans
    (le_mul_of_one_le_left (by positivity) (one_le_scaleRatio t))⟩

/-- A call is marked with probability its padded cost over the calibration scale. -/
def scaledMark (L : ℕ) (t : ℝ) : (ℕ × (ℕ → Bool)) → unitInterval :=
  costParameter (calScale L t) (calScale_pos L t) (paddedRealCost L) (paddedRealCost_scale_bounds L t)

theorem measurable_scaledMark (L : ℕ) (t : ℝ) : Measurable (scaledMark L t) :=
  measurable_costParameter _ _ _ _ (measurable_paddedRealCost L)

/-- The mark of `BlindUpper` on a scaled seed mark is the mark at the calibration scale. -/
theorem callMark_scale (L : ℕ) (t : ℝ) (x : ℕ × (ℕ → Bool)) (u : ℝ) :
    callMark (paddedMark L) (x, scaleRatio t * u) = callMark (scaledMark L t) (x, u) := by
  have hs := scaleRatio_pos t
  have h2 : (0 : ℝ) < (2 : ℝ) ^ L := by positivity
  have key : scaleRatio t * u < paddedRealCost L x / (2 : ℝ) ^ L ↔
      u < paddedRealCost L x / calScale L t := by
    unfold calScale
    rw [lt_div_iff₀ h2, lt_div_iff₀ (mul_pos hs h2)]
    constructor <;> intro h <;> linarith
  have hp : ((paddedMark L x : unitInterval) : ℝ) = paddedRealCost L x / (2 : ℝ) ^ L := rfl
  have hq : ((scaledMark L t x : unitInterval) : ℝ) = paddedRealCost L x / calScale L t := rfl
  simp only [callMark, uniformCoinFlip]
  split_ifs with h1 h2 h2 <;> first
    | rfl
    | (exfalso; rw [hp] at h1; rw [hq] at h2; tauto)

/-- Multiply the marks of a marked sequence by the ratio. -/
def scaleMarks {X : Type} (t : ℝ) (z : ℕ → X × ℝ) : ℕ → X × ℝ :=
  fun i => ((z i).1, scaleRatio t * (z i).2)

/-- Multiply the marks of both pilot sequences of a calibration state. -/
def scaleState {X : Type} (t : ℝ) (z : CalibrationState X) : CalibrationState X :=
  ((scaleMarks t z.1.1, scaleMarks t z.1.2), z.2)

theorem markedTape_scale (L : ℕ) (t : ℝ) (z : ℕ → (ℕ × (ℕ → Bool)) × ℝ) :
    markedTape (paddedMark L) (scaleMarks t z) = markedTape (scaledMark L t) z := by
  funext i
  exact callMark_scale L t (z i).1 (z i).2

theorem pilotFailures_scale (L : ℕ) (t : ℝ) (z : ℕ → (ℕ × (ℕ → Bool)) × ℝ) :
    pilotFailures (paddedMark L) (scaleMarks t z) = pilotFailures (scaledMark L t) z := by
  unfold pilotFailures
  rw [markedTape_scale]

theorem firstPilotWork_scale (L : ℕ) (t : ℝ) (C : (ℕ × (ℕ → Bool)) → ℝ≥0∞)
    (z : ℕ → (ℕ × (ℕ → Bool)) × ℝ) :
    firstPilotWork (paddedMark L) C (scaleMarks t z) = firstPilotWork (scaledMark L t) C z := by
  unfold firstPilotWork failureWeight
  congr 1
  funext i
  congr 1
  apply Finset.prod_congr rfl
  intro j _
  change (if callMark (paddedMark L) ((z j).1, scaleRatio t * (z j).2) then 0 else 1) = _
  rw [callMark_scale]

theorem calibrationOutput_scale (L : ℕ) (t : ℝ) (Z : (ℕ × (ℕ → Bool)) → ℝ)
    (z : CalibrationState (ℕ × (ℕ → Bool))) :
    calibrationOutput (paddedMark L) Z (scaleState t z) = calibrationOutput (scaledMark L t) Z z := by
  unfold calibrationOutput scaleState twoPilotFailures
  simp only [pilotFailures_scale]

theorem calibrationWork_scale (L : ℕ) (t : ℝ) (C : (ℕ × (ℕ → Bool)) → ℝ)
    (z : CalibrationState (ℕ × (ℕ → Bool))) :
    calibrationWork (paddedMark L) C (scaleState t z) = calibrationWork (scaledMark L t) C z := by
  unfold calibrationWork scaleState twoPilotWork twoPilotFailures
  simp only [pilotFailures_scale, firstPilotWork_scale]

/-- Multiply the uniform marks of a seed by the ratio. -/
def scaleSeed (t : ℝ) (r : BatchSeed) : BatchSeed := fun j => ((r j).1, scaleRatio t * (r j).2)

theorem measurable_scaleSeed (t : ℝ) : Measurable (scaleSeed t) := by
  apply Measurable.of_eval
  intro j
  exact (measurable_pi_apply j).fst.prodMk (measurable_const.mul (measurable_pi_apply j).snd)

theorem batchInput_scale (t : ℝ) (r : BatchSeed) (s : ℕ → ℕ → Bool) :
    batchInput (scaleSeed t r, s) = scaleState t (batchInput (r, s)) := rfl

/-- The batch machine of `BlindUpper` at level `L`, run on the scaled seed. -/
def scaledEstimator (L : ℕ) (t : ℝ) : AdaptiveEstimator BatchSeed where
  randomLaw := batchSeedLaw
  probability := batchSeedLaw_probability
  policy := fun r xs => batchPolicy L (scaleSeed t r) xs
  policy_measurable := fun xs _ =>
    measurableSet_eq_fun ((measurable_batchPolicy L xs).comp (measurable_scaleSeed t)) measurable_const
  output := fun z => batchOutput L (scaleSeed t z.1, z.2)
  output_measurable :=
    (measurable_batchOutput L).comp (((measurable_scaleSeed t).comp measurable_fst).prodMk measurable_snd)

/-- The calibrated output and work at the calibration scale `t*2^L`. -/
def scaledBatchOutput (L : ℕ) (t : ℝ) : CalibrationState (ℕ × (ℕ → Bool)) → ℝ :=
  calibrationOutput (scaledMark L t) (cutoffValue L)

def scaledBatchWork (L : ℕ) (t : ℝ) : CalibrationState (ℕ × (ℕ → Bool)) → ℝ≥0∞ :=
  calibrationWork (scaledMark L t) (paddedRealCost L)

theorem measurable_scaledBatchOutput (L : ℕ) (t : ℝ) : Measurable (scaledBatchOutput L t) :=
  measurable_calibrationOutput _ (measurable_scaledMark L t) _ (measurable_cutoffValue L)

theorem measurable_scaledBatchWork (L : ℕ) (t : ℝ) : Measurable (scaledBatchWork L t) :=
  measurable_calibrationWork _ (measurable_scaledMark L t) _ (measurable_paddedRealCost L)

theorem phaseMark_scale (L : ℕ) (t : ℝ) (r : BatchSeed) (s : ℕ → ℕ → Bool) (phase : ℕ) :
    phaseMark L (scaleSeed t r) s phase =
      fun i => callMark (scaledMark L t) (seededMarkedCalls (r, s) (Nat.pair phase i)) := by
  funext i
  exact callMark_scale L t _ _

theorem scaledMark_mean_pos (L : ℕ) (t : ℝ) (μ : Measure Gap) [IsProbabilityMeasure μ] (q : SignLaw) :
    0 < (meanParameter (callMeasure μ q) (scaledMark L t) (measurable_scaledMark L t) : ℝ) := by
  unfold scaledMark
  rw [mean_costParameter _ _ _ _ _ (measurable_paddedRealCost L)]
  exact div_pos (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) (paddedCutoff_work_lower L μ q))
    (calScale_pos L t)

theorem scaled_pilots_terminate (L : ℕ) (t : ℝ) (μ : Measure Gap) [IsProbabilityMeasure μ]
    (q : SignLaw) :
    ∀ᵐ z ∂originalSimulationLaw μ (scaledEstimator L t) q,
      firstSuccess (phaseMark L (scaleSeed t z.1) z.2 0) ≠ ⊤ ∧
        firstSuccess (phaseMark L (scaleSeed t z.1) z.2 1) ≠ ⊤ := by
  let ν := callMeasure μ q
  let π := markedSequenceLaw ν
  have hp : meanParameter ν (scaledMark L t) (measurable_scaledMark L t) ≠ 0 := by
    intro h
    have ht := scaledMark_mean_pos L t μ q
    change 0 < (meanParameter ν (scaledMark L t) (measurable_scaledMark L t) : ℝ) at ht
    simp [h] at ht
  have ht := pilot_terminates ν (scaledMark L t) (measurable_scaledMark L t) hp
  have h₀ : ∀ᵐ z ∂π.prod π, firstSuccess (markedTape (scaledMark L t) z.1) ≠ ⊤ :=
    Measure.quasiMeasurePreserving_fst.ae ht
  have h₁ : ∀ᵐ z ∂π.prod π, firstSuccess (markedTape (scaledMark L t) z.2) ≠ ⊤ :=
    Measure.quasiMeasurePreserving_snd.ae ht
  have hcal : ∀ᵐ z ∂calibrationLaw ν,
      firstSuccess (markedTape (scaledMark L t) z.1.1) ≠ ⊤ ∧
      firstSuccess (markedTape (scaledMark L t) z.1.2) ≠ ⊤ :=
    Measure.quasiMeasurePreserving_fst.ae (h₀.and h₁)
  have hpres := (batchInput_preserving μ q).quasiMeasurePreserving.ae hcal
  change ∀ᵐ z ∂(batchSeedLaw.prod (Measure.infinitePi (fun _ : ℕ => originalPopulationTapeLaw μ q))), _
  filter_upwards [hpres] with z hz
  rw [phaseMark_scale, phaseMark_scale]
  exact hz

/-- Actual work and output of the scaled machine under the population law. -/
theorem scaled_population_identities (L : ℕ) (t : ℝ) (μ : Measure Gap) [IsProbabilityMeasure μ]
    (q : SignLaw) :
    ∀ᵐ z ∂originalSimulationLaw μ (scaledEstimator L t) q,
      totalProcessWork (populationPath (batchPolicy L (scaleSeed t z.1)) z.2) =
          scaledBatchWork L t (batchInput z) ∧
        batchOutput L (scaleSeed t z.1, populationPath (batchPolicy L (scaleSeed t z.1)) z.2) =
          scaledBatchOutput L t (batchInput z) := by
  filter_upwards [scaled_pilots_terminate L t μ q] with z hz
  have h₀ := (ENat.natCast_toNat hz.1).symm
  have h₁ := (ENat.natCast_toNat hz.2).symm
  have hw := batch_population_work L (scaleSeed t z.1) z.2 _ _ h₀ h₁
  have ho := batch_population_output L (scaleSeed t z.1) z.2 _ _ h₀ h₁
  rw [batchInput_scale] at hw ho
  refine ⟨hw.trans ?_, ho.trans ?_⟩
  · exact calibrationWork_scale L t (paddedRealCost L) (batchInput z)
  · exact calibrationOutput_scale L t (cutoffValue L) (batchInput z)

theorem scaled_expectedWork_eq (L : ℕ) (t : ℝ) (μ : Measure Gap) [IsProbabilityMeasure μ]
    (q : SignLaw) :
    expectedWork μ (scaledEstimator L t) q =
      ∫⁻ z, scaledBatchWork L t z ∂calibrationLaw (callMeasure μ q) := by
  rw [original_expectedWork_simulation]
  calc
    _ = ∫⁻ z, scaledBatchWork L t (batchInput z) ∂originalSimulationLaw μ (scaledEstimator L t) q := by
      apply lintegral_congr_ae
      filter_upwards [scaled_population_identities L t μ q] with z hz
      exact hz.1
    _ = _ := (batchInput_preserving μ q).lintegral_comp (measurable_scaledBatchWork L t)

theorem scaled_squaredRisk_eq (L : ℕ) (t : ℝ) (μ : Measure Gap) [IsProbabilityMeasure μ]
    (q : SignLaw) (a : ℝ) :
    squaredRisk (experimentLaw μ (scaledEstimator L t) q) (populationOutput (scaledEstimator L t)) a =
      ∫⁻ z, ENNReal.ofReal ((scaledBatchOutput L t z - a) ^ 2) ∂calibrationLaw (callMeasure μ q) := by
  rw [original_squaredRisk_simulation]
  calc
    _ = ∫⁻ z, ENNReal.ofReal ((scaledBatchOutput L t (batchInput z) - a) ^ 2)
        ∂originalSimulationLaw μ (scaledEstimator L t) q := by
      apply lintegral_congr_ae
      filter_upwards [scaled_population_identities L t μ q] with z hz
      change ENNReal.ofReal ((batchOutput L (scaleSeed t z.1,
        populationPath (batchPolicy L (scaleSeed t z.1)) z.2) - a) ^ 2) = _
      rw [hz.2]
    _ = _ := (batchInput_preserving μ q).lintegral_comp
      (((measurable_scaledBatchOutput L t).sub measurable_const).pow_const 2).ennreal_ofReal

/-- The scaled machine keeps the budget `4*t*2^L`. -/
theorem scaled_uniformBudget (L : ℕ) (t : ℝ) (μ : Measure Gap) [IsProbabilityMeasure μ] :
    UniformBudget μ (scaledEstimator L t) (4 * calScale L t) := by
  intro q
  rw [scaled_expectedWork_eq]
  exact calibration_cost_budget (callMeasure μ q) (calScale L t) (calScale_pos L t) (paddedRealCost L)
    (paddedRealCost_scale_bounds L t) (measurable_paddedRealCost L)
    (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) (paddedCutoff_work_lower L μ q))

end ThresholdHC.UpperScale
