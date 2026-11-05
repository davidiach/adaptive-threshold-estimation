import ThresholdHC.TypedConfidence.SeededTransfer
import ThresholdHC.TypedConfidence.PathValidity

noncomputable section
open MeasureTheory InformationTheory Set
open scoped ENNReal
namespace ThresholdHC.TypedConfidence
open ThresholdHC ThresholdHC.Proofs ThresholdHC.Tier3 ThresholdHC.Tier4 ThresholdHC.CriticalEntropy
open ThresholdHC.ObservableSimulation ThresholdHC.ConfidenceTransfer

local instance : MeasurableSpace (Option Bool) := ⊤
local instance : MeasurableSpace (Option ℕ) := ⊤
local instance : MeasurableSpace (Option (Fin 1)) := ⊤

theorem parameter_valid_ae {R : Type} [MeasurableSpace R]
    (ν : Measure R) (κ : ℕ → Measure unitInterval) [∀ i, IsProbabilityMeasure (κ i)]
    (pol : R → List Bool → Option ℕ) (hp : ∀ xs, Measurable (fun r => pol r xs)) :
    ∀ᵐ z ∂parameterExperimentLaw ν κ pol, ∀ n,
      (z.2 n).isSome = (pol z.1 (processHistory z.2 n)).isSome := by
  apply ae_all_iff.2
  intro n
  have hm := measurable_fst.prodMk (measurable_seeded_populationPath pol hp)
  have hpm : Measurable (fun z : R × ProcessTape => pol z.1 (processHistory z.2 n)) :=
    measurable_prefix_function Prod.fst Prod.snd measurable_fst
      (fun k b => measurableSet_eq_fun ((measurable_pi_apply k).comp measurable_snd)
        (measurable_const : Measurable (fun _ : R × ProcessTape => b))) n
      (fun u w => pol u (fullHist w)) (fun w => hp (fullHist w))
  have he : MeasurableSet {z : R × ProcessTape |
      (z.2 n).isSome = (pol z.1 (processHistory z.2 n)).isSome} :=
    measurableSet_eq_fun
      ((measurable_of_countable (@Option.isSome Bool)).comp ((measurable_pi_apply n).comp measurable_snd))
      ((measurable_of_countable (@Option.isSome ℕ)).comp hpm)
  exact (ae_map_iff hm.aemeasurable he).mpr
    (ae_of_all _ (fun z => populationPath_valid (pol z.1) z.2 n))

theorem parameter_stopped_cover {R : Type} [MeasurableSpace R]
    (ν : Measure R) (κ : ℕ → Measure unitInterval) [∀ i, IsProbabilityMeasure (κ i)]
    (pol : R → List Bool → Option ℕ) (hp : ∀ xs, Measurable (fun r => pol r xs))
    (hw : (∫⁻ z, totalProcessWork z.2 ∂parameterExperimentLaw ν κ pol) < ∞) :
    ∀ᵐ z ∂parameterExperimentLaw ν κ pol, z ∈ ⋃ n, stoppedFullSet (Tier5.stoppingFlagPolicy pol) n := by
  have hfinite := ae_lt_top (measurable_totalProcessWork (Prod.snd : R × ProcessTape → ProcessTape)
    (fun n b => measurableSet_eq_fun ((measurable_pi_apply n).comp measurable_snd)
      (measurable_const : Measurable (fun _ : R × ProcessTape => b)))) hw.ne
  filter_upwards [parameter_valid_ae ν κ pol hp,hfinite] with z hvalid hwork
  have hstop : ∃ n, pol z.1 (processHistory z.2 n) = none := by
    by_contra hn
    push Not at hn
    have hsome (n : ℕ) : (z.2 n).isSome = true := by
      rw [hvalid n]
      exact Option.isSome_iff_ne_none.mpr (hn n)
    have hcount (n : ℕ) : workOf (processPrefix n z.2) = n := by
      simp [workOf,processPrefix,hsome]
    obtain ⟨n,hnlarge⟩ := exists_nat_gt (totalProcessWork z.2).toReal
    have hle : ENNReal.ofReal (n : ℝ) ≤ totalProcessWork z.2 := by
      rw [← hcount n]
      exact le_iSup (fun k => ENNReal.ofReal (workOf (processPrefix k z.2))) n
    have h := ENNReal.toReal_mono hwork.ne hle
    exact (not_le.mpr hnlarge) (by simpa using h)
  obtain ⟨n,hn⟩ := hstop
  exact mem_iUnion.mpr ⟨n,n,le_rfl,by simp [Tier5.stoppingFlagPolicy,hn]⟩

/-- Finite expected work at both endpoints exhausts the full observable entropy
by the physical finite prefixes of the same population. -/
theorem stopped_parameter_kl_eq_iSup {R : Type} [MeasurableSpace R]
    (ν : Measure R) [IsProbabilityMeasure ν]
    (κ τ : ℕ → Measure unitInterval)
    [∀ i, IsProbabilityMeasure (κ i)] [∀ i, IsProbabilityMeasure (τ i)]
    (pol : R → List Bool → Option ℕ) (hp : ∀ xs, Measurable (fun r => pol r xs))
    (hw : (∫⁻ z, totalProcessWork z.2 ∂parameterExperimentLaw ν κ pol) < ∞)
    (hw' : (∫⁻ z, totalProcessWork z.2 ∂parameterExperimentLaw ν τ pol) < ∞) :
    klDiv (parameterExperimentLaw ν κ pol) (parameterExperimentLaw ν τ pol) =
      ⨆ n, klDiv
        ((parameterExperimentLaw ν κ pol).map (fun z => (z.1,processPrefix n z.2)))
        ((parameterExperimentLaw ν τ pol).map (fun z => (z.1,processPrefix n z.2))) := by
  let f (n : ℕ) (z : R × ProcessTape) := (z.1,processPrefix n z.2)
  let flag := Tier5.stoppingFlagPolicy pol
  have hflag := Tier5.measurable_stoppingFlagPolicy pol
    (fun xs a => measurableSet_eq_fun (hp xs) measurable_const)
  have heq (n) : f n ⁻¹' stoppedPrefixSet flag n = stoppedFullSet flag n :=
    Set.ext (fun z => (stoppedFullSet_prefix flag n z).symm)
  let : IsProbabilityMeasure (parameterExperimentLaw ν κ pol) := parameterExperiment_probability ν κ pol hp
  let : IsProbabilityMeasure (parameterExperimentLaw ν τ pol) := parameterExperiment_probability ν τ pol hp
  have cover (υ : ℕ → Measure unitInterval) [∀ i, IsProbabilityMeasure (υ i)]
      (hb : (∫⁻ z, totalProcessWork z.2 ∂parameterExperimentLaw ν υ pol) < ∞) :
      ∀ᵐ z ∂parameterExperimentLaw ν υ pol, z ∈ ⋃ n, f n ⁻¹' stoppedPrefixSet flag n := by
    simp_rw [heq]
    exact parameter_stopped_cover ν υ pol hp hb
  have recn (υ : ℕ → Measure unitInterval) [∀ i, IsProbabilityMeasure (υ i)] (n : ℕ) :
      ∀ᵐ z ∂(parameterExperimentLaw ν υ pol).restrict (f n ⁻¹' stoppedPrefixSet flag n),
        padJoint n (f n z) = z := by
    rw [heq]
    apply (ae_restrict_iff' (measurableSet_stoppedFull flag hflag n)).mpr
    filter_upwards [parameter_valid_ae ν υ pol hp] with z hz hstop
    exact stopped_valid_reconstruction flag z (by
      simpa only [flag,Tier5.stoppingFlagPolicy,Option.isSome_map] using hz) n hstop
  have hm : Monotone (fun n => f n ⁻¹' stoppedPrefixSet flag n) := by
    simp_rw [heq]
    exact stoppedFullSet_mono flag
  exact klDiv_eq_iSup_map_of_reconstruction (parameterExperimentLaw ν κ pol)
    (parameterExperimentLaw ν τ pol) f padJoint (stoppedPrefixSet flag) measurable_jointPrefix
    measurable_padJoint (measurableSet_stoppedPrefix flag hflag) hm (cover κ hw) (cover τ hw')
    (recn κ) (recn τ)

/-- Full stopped information transfer for countably many heterogeneous labels
and arbitrary measurable private randomization. -/
theorem stopped_parameter_reference_kl {R : Type} [MeasurableSpace R]
    (ν : Measure R) [IsProbabilityMeasure ν]
    (κ τ : ℕ → Measure unitInterval)
    [∀ i, IsProbabilityMeasure (κ i)] [∀ i, IsProbabilityMeasure (τ i)]
    (pol : R → List Bool → Option ℕ) (hp : ∀ xs, Measurable (fun r => pol r xs))
    (K B : ℝ) (hK : 0 ≤ K) (hB : 0 ≤ B) (hlocal : ∀ i, ParameterReferenceBound (κ i) (τ i) K)
    (hw : (∫⁻ z, totalProcessWork z.2
      ∂parameterExperimentLaw ν (fun i => quarterMix (κ i) (τ i)) pol) ≤ ENNReal.ofReal B)
    (hw' : (∫⁻ z, totalProcessWork z.2
      ∂parameterExperimentLaw ν (fun i => quarterMix (τ i) (κ i)) pol) < ∞) :
    klDiv (parameterExperimentLaw ν (fun i => quarterMix (κ i) (τ i)) pol)
      (parameterExperimentLaw ν (fun i => quarterMix (τ i) (κ i)) pol) ≤
      ENNReal.ofReal ((8/3)*K*B) := by
  have hfin := hw.trans_lt ENNReal.ofReal_lt_top
  rw [stopped_parameter_kl_eq_iSup ν _ _ pol hp hfin hw']
  refine iSup_le fun n => (seeded_parameter_reference_kl ν κ τ pol hp n K hK hlocal).trans ?_
  apply ENNReal.ofReal_le_ofReal
  have hb := prefix_work_le_total _ (Prod.snd : R × ProcessTape → ProcessTape)
    (fun n b => measurableSet_eq_fun ((measurable_pi_apply n).comp measurable_snd)
      (measurable_const : Measurable (fun _ : R × ProcessTape => b))) hfin n
  have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top hw
  rw [ENNReal.toReal_ofReal hB] at h
  exact mul_le_mul_of_nonneg_left (hb.trans h) (mul_nonneg (by norm_num) hK)

end ThresholdHC.TypedConfidence
