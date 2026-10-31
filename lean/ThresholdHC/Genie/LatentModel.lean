import ThresholdHC.Genie.Model
import ThresholdHC.ObservableSimulation.OriginalExperiment

/-! The actual latent magnitude/sign law, its identifiable Bernoulli
parameter, and the signed endpoint score. No posterior or information
identity is assumed by these definitions. -/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace ThresholdHC.Genie
open ThresholdHC.Tier6 ThresholdHC.StoppingProgram ThresholdHC.CriticalEntropy
open ThresholdHC.ObservableSimulation

abbrev LatentState := Gap × Bool

def latentParameter (z : LatentState) : ℝ := (gapParameter z.2 z.1 : ℝ)

theorem measurable_latentParameter : Measurable latentParameter := by
  have he : latentParameter = fun z : LatentState =>
      if z.2 = true then 1/2+(z.1:ℝ) else 1/2-(z.1:ℝ) := by
    funext z
    cases h : z.2 <;> simp [latentParameter,gapParameter,h] <;> ring
  rw [he]
  exact Measurable.ite (measurableSet_eq_fun measurable_snd measurable_const)
    (measurable_const.add (measurable_subtype_coe.comp measurable_fst))
    (measurable_const.sub (measurable_subtype_coe.comp measurable_fst))

theorem latentParameter_injective : Function.Injective latentParameter := by
  rintro ⟨d,s⟩ ⟨e,t⟩ h
  have hd := d.property
  have he := e.property
  cases s <;> cases t <;> simp only [latentParameter,gapParameter,Bool.false_eq_true,ite_false,ite_true] at h
  · have hde : d = e := Subtype.ext (by linarith)
    subst e
    rfl
  · exfalso; linarith
  · exfalso; linarith
  · have hde : d = e := Subtype.ext (by linarith)
    subst e
    rfl

theorem latentParameter_embedding : MeasurableEmbedding latentParameter := by
  letI : StandardBorelSpace Gap :=
    (measurableSet_Ioc : MeasurableSet (Set.Ioc (0:ℝ) (1/2))).standardBorel
  exact measurable_latentParameter.measurableEmbedding latentParameter_injective

def latentSelector (q : SignLaw) (z : Gap × ℝ) : LatentState :=
  (z.1,uniformCoinFlip (signUnit q z.1) z.2)

theorem measurable_latentSelector (q : SignLaw) : Measurable (latentSelector q) :=
  measurable_fst.prodMk (measurable_uniformCoinFlip.comp
    (((measurable_signUnit q).comp measurable_fst).prodMk measurable_snd))

def latentReference (μ : Measure Gap) (q : SignLaw) : Measure LatentState :=
  (μ.prod uniformUnitMeasure).map (latentSelector q)

instance latentReference_probability (μ : Measure Gap) [IsProbabilityMeasure μ] (q : SignLaw) :
    IsProbabilityMeasure (latentReference μ q) :=
  (Measure.isProbabilityMeasure_map_iff (measurable_latentSelector q).aemeasurable).mpr inferInstance

theorem latentReference_lintegral (μ : Measure Gap) [IsFiniteMeasure μ] (q : SignLaw)
    (F : LatentState → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ z, F z ∂latentReference μ q) = ∫⁻ d,
      ENNReal.ofReal (q.val d)*F (d,true)+ENNReal.ofReal (1-q.val d)*F (d,false) ∂μ := by
  have hcomp : Measurable (fun z : Gap × ℝ => F (latentSelector q z)) :=
    hF.comp (measurable_latentSelector q)
  rw [latentReference,lintegral_map hF (measurable_latentSelector q),lintegral_prod _ hcomp.aemeasurable]
  apply lintegral_congr
  intro d
  have hFd : Measurable (fun b : Bool => F (d,b)) := measurable_of_countable _
  have hm : Measurable (uniformCoinFlip (signUnit q d)) :=
    measurable_uniformCoinFlip.comp (measurable_const.prodMk measurable_id)
  change (∫⁻ u, F (d,uniformCoinFlip (signUnit q d) u) ∂uniformUnitMeasure) = _
  rw [←lintegral_map hFd hm,uniformCoinFlip_map]
  simp [bernoulliMeasure_def,lintegral_add_measure,lintegral_smul_measure,
    lintegral_dirac' _ hFd,ENNReal.smul_def,smul_eq_mul,ENNReal.coe_nnreal_eq,signUnit]

def latentScore (Q : FourPriors) (z : LatentState) : ℝ :=
  if z.2 = true then (Q.high.val z.1-Q.low.val z.1)/Q.variance.val z.1
  else -(Q.high.val z.1-Q.low.val z.1)/(1-Q.variance.val z.1)

theorem measurable_latentScore (Q : FourPriors) : Measurable (latentScore Q) := by
  have hd : Measurable (fun z : LatentState => Q.high.val z.1-Q.low.val z.1) :=
    (Q.high.property.1.sub Q.low.property.1).comp measurable_fst
  have hv : Measurable (fun z : LatentState => Q.variance.val z.1) := Q.variance.property.1.comp measurable_fst
  exact Measurable.ite (measurableSet_eq_fun measurable_snd measurable_const)
    (hd.div hv) (hd.neg.div (measurable_const.sub hv))

def parameterScore (Q : FourPriors) : ℝ → ℝ :=
  Function.extend latentParameter (latentScore Q) (fun _ => 0)

theorem measurable_parameterScore (Q : FourPriors) : Measurable (parameterScore Q) :=
  latentParameter_embedding.measurable_extend (measurable_latentScore Q) measurable_const

theorem parameterScore_latent (Q : FourPriors) (z : LatentState) :
    parameterScore Q (latentParameter z) = latentScore Q z :=
  latentParameter_injective.extend_apply _ _ z

end ThresholdHC.Genie
