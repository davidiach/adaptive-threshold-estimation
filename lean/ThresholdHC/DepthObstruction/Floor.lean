import ThresholdHC.DepthObstruction.CappedTranscript

/-! The RMS floor from equal observable laws, and its cap-diameter consequence.
The squared risk of the population output is an integral against the joint law
of seed and transcript. When the two sign laws give the same such law, the
pointwise identity `(Z-a)^2+(Z-b)^2 = (2Z-a-b)^2/2+(a-b)^2/2` bounds the larger
squared risk below by `(a-b)^2/4`, with infinite risk retained. -/

noncomputable section
namespace ThresholdHC.DepthObstruction
open MeasureTheory
open scoped ENNReal
open ThresholdHC.Tier3 (ProcessTape)
open ThresholdHC.Tier6 (Gap SignLaw signMean AdaptiveEstimator experimentLaw rootMeanRisk
  populationOutput squaredRisk PopulationSeed)
open ThresholdHC.RareAboveTwo (rareRisk RarePrior)
open ThresholdHC.CapIdentification (OddMomentMatch capDiameter capDiameter_attained
  capDiameter_bounds)

/-- The squared risk of the population output against the observable law. -/
theorem squaredRisk_observable {R : Type} [MeasurableSpace R]
    (μ : Measure Gap) [IsProbabilityMeasure μ] (A : AdaptiveEstimator R) (q : SignLaw)
    (θ : ℝ) :
    squaredRisk (experimentLaw μ A q) (populationOutput A) θ =
      ∫⁻ w, ENNReal.ofReal ((A.output w - θ)^2)
        ∂(experimentLaw μ A q).map (fun z => (z.1.1, z.2)) := by
  have hπ : Measurable (fun z : PopulationSeed R × ProcessTape => (z.1.1, z.2)) :=
    (measurable_fst.comp measurable_fst).prodMk measurable_snd
  have hF : Measurable (fun w : R × ProcessTape => ENNReal.ofReal ((A.output w - θ)^2)) :=
    ((A.output_measurable.sub measurable_const).pow_const 2).ennreal_ofReal
  rw [lintegral_map hF hπ]
  rfl

theorem sq_pair_floor (z a b : ℝ) : (a-b)^2/2 ≤ (z-a)^2 + (z-b)^2 := by
  nlinarith [sq_nonneg (2*z-a-b)]

/-- Two squared errors of one statistic against one probability law. -/
theorem squared_pair_floor {Ω : Type} [MeasurableSpace Ω] (M : Measure Ω)
    [IsProbabilityMeasure M] (f : Ω → ℝ) (hf : Measurable f) (a b : ℝ) :
    ENNReal.ofReal ((a-b)^2/4) ≤
      max (∫⁻ w, ENNReal.ofReal ((f w - a)^2) ∂M) (∫⁻ w, ENNReal.ofReal ((f w - b)^2) ∂M) := by
  have hfa : Measurable (fun w => ENNReal.ofReal ((f w - a)^2)) :=
    ((hf.sub measurable_const).pow_const 2).ennreal_ofReal
  have hsum : ENNReal.ofReal ((a-b)^2/2) ≤
      (∫⁻ w, ENNReal.ofReal ((f w - a)^2) ∂M) + ∫⁻ w, ENNReal.ofReal ((f w - b)^2) ∂M := by
    rw [← lintegral_add_left hfa]
    calc ENNReal.ofReal ((a-b)^2/2) = ∫⁻ _w, ENNReal.ofReal ((a-b)^2/2) ∂M := by
          rw [lintegral_const, measure_univ, mul_one]
      _ ≤ _ := lintegral_mono (fun w => by
          rw [← ENNReal.ofReal_add (sq_nonneg _) (sq_nonneg _)]
          exact ENNReal.ofReal_le_ofReal (sq_pair_floor (f w) a b))
  have h2 : ENNReal.ofReal ((a-b)^2/2) = 2 * ENNReal.ofReal ((a-b)^2/4) := by
    rw [show (a-b)^2/2 = 2 * ((a-b)^2/4) by ring, ENNReal.ofReal_mul (by norm_num),
      ENNReal.ofReal_ofNat]
  have hle : (∫⁻ w, ENNReal.ofReal ((f w - a)^2) ∂M) + ∫⁻ w, ENNReal.ofReal ((f w - b)^2) ∂M ≤
      2 * max (∫⁻ w, ENNReal.ofReal ((f w - a)^2) ∂M)
        (∫⁻ w, ENNReal.ofReal ((f w - b)^2) ∂M) := by
    rw [two_mul]
    exact add_le_add (le_max_left _ _) (le_max_right _ _)
  rw [h2] at hsum
  exact (ENNReal.mul_le_mul_iff_right two_ne_zero ENNReal.ofNat_ne_top).mp (hsum.trans hle)

/-- `thm:cap`, final display: equal observable laws give RMS at least half the
target separation under one of the two sign laws. -/
theorem equalLawFloor : EqualLawFloorStatement := by
  intro R _ μ _ A qH qL hlaw
  have hsq : ENNReal.ofReal ((signMean μ qH.val - signMean μ qL.val)^2/4) ≤
      max (squaredRisk (experimentLaw μ A qH) (populationOutput A) (signMean μ qH.val))
        (squaredRisk (experimentLaw μ A qL) (populationOutput A) (signMean μ qL.val)) := by
    rw [squaredRisk_observable, squaredRisk_observable, hlaw]
    exact squared_pair_floor _ A.output A.output_measurable _ _
  have hh := ENNReal.rpow_le_rpow hsq (by norm_num : (0 : ℝ) ≤ 1/2)
  rw [ENNReal.max_rpow (by norm_num : (0 : ℝ) ≤ 1/2)] at hh
  have heq : ENNReal.ofReal ((signMean μ qH.val - signMean μ qL.val)^2/4) ^ (1/2 : ℝ) =
      ENNReal.ofReal (|signMean μ qH.val - signMean μ qL.val| / 2) := by
    rw [show (signMean μ qH.val - signMean μ qL.val)^2/4 =
        (|signMean μ qH.val - signMean μ qL.val| / 2)^2 by rw [div_pow, sq_abs]; norm_num,
      ENNReal.ofReal_pow (by positivity)]
    simpa only [Nat.cast_ofNat, one_div] using
      ENNReal.pow_rpow_inv_natCast (n := 2) (by norm_num)
        (ENNReal.ofReal (|signMean μ qH.val - signMean μ qL.val| / 2))
  rw [heq] at hh
  exact hh

/-- Formal-only extension: half the attained cap-`N` diameter floors the rare-prior
RMS risk of every per-coin-capped population procedure, for every gap law. -/
theorem populationCapFloor : PopulationCapFloorStatement := by
  intro R _ μ _ ρ N A hρ hcap
  obtain ⟨qH, qL, hH, hL, hm, he, -⟩ := capDiameter_attained μ hρ N
  have hfloor := equalLawFloor R μ A qH qL (cappedTranscript R μ qH qL N A hm hcap)
  have hnn := (capDiameter_bounds μ hρ N).1
  rw [he] at hnn ⊢
  rw [abs_of_nonneg hnn] at hfloor
  refine hfloor.trans (max_le ?_ ?_)
  · unfold rareRisk
    exact le_iSup₂ (f := fun (q : SignLaw) (_ : RarePrior μ ρ q) =>
      rootMeanRisk (experimentLaw μ A q) (populationOutput A) (signMean μ q.val)) qH hH
  · unfold rareRisk
    exact le_iSup₂ (f := fun (q : SignLaw) (_ : RarePrior μ ρ q) =>
      rootMeanRisk (experimentLaw μ A q) (populationOutput A) (signMean μ q.val)) qL hL

end ThresholdHC.DepthObstruction
