import ThresholdHC.CriticalEntropy.CriticalTermination
import ThresholdHC.CriticalEntropy.EventualAffinity

noncomputable section

namespace ThresholdHC.CriticalEntropy
open MeasureTheory ProbabilityTheory Set Filter ThresholdHC.Tier3 ThresholdHC.Tier4
open scoped ENNReal Topology
set_option maxHeartbeats 2000000

def criticalObservationLaw {R I : Type} [MeasurableSpace R] [MeasurableSpace I]
    (A : Tier6.AdaptiveEstimator R) (q : ℝ → unitInterval) (hq : Measurable q)
    (f : R × ProcessTape → I) : Measure I :=
  (criticalExperimentLaw A q hq).map (fun z => f (z.1.1,z.2))

instance criticalPrefixLaw_probability {R : Type} [MeasurableSpace R]
    (A : Tier6.AdaptiveEstimator R) (q : ℝ → unitInterval) (hq : Measurable q) (n : ℕ) :
    IsProbabilityMeasure (criticalPrefixLaw A q hq n) := by
  unfold criticalPrefixLaw
  infer_instance

/-- Pass a uniform prefix information bound to any finite observable decision.
Finite expected work is required at both endpoints, while the charged bound may
come from a third (midpoint) law. -/
theorem critical_terminal_affinity_bound {R I : Type} [MeasurableSpace R]
    [Fintype I] [MeasurableSpace I] [MeasurableSingletonClass I]
    (A : Tier6.AdaptiveEstimator R) (q r : ℝ → unitInterval)
    (hq : Measurable q) (hr : Measurable r)
    (hworkq : criticalExpectedWork A q hq < ∞)
    (hworkr : criticalExpectedWork A r hr < ∞)
    (f : R × ProcessTape → I) (hf : Measurable f)
    (k b : ℝ) (hk : 0 ≤ k)
    (hprefix : ∀ n, (1-(hellingerAffinity (criticalPrefixLaw A q hq n)
      (criticalPrefixLaw A r hr n)).toReal)*k ≤ b) :
    (1-(hellingerAffinity (criticalObservationLaw A q hq f)
      (criticalObservationLaw A r hr f)).toReal)*k ≤ b := by
  let P := criticalExperimentLaw A q hq
  let Q := criticalExperimentLaw A r hr
  let g : ((R × (ℕ → ℝ)) × ProcessTape) → I := fun z => f (z.1.1,z.2)
  let F : ℕ → ((R × (ℕ → ℝ)) × ProcessTape) → I :=
    fun n z => f (z.1.1,padPrefix n (processPrefix n z.2))
  have hproj (n : ℕ) : Measurable
      (fun z : (R × (ℕ → ℝ)) × ProcessTape => (z.1.1,processPrefix n z.2)) :=
    (measurable_fst.comp measurable_fst).prodMk
      (Measurable.of_eval (fun i : Fin n => (measurable_pi_apply i.val).comp measurable_snd))
  have hF (n) : Measurable (F n) := (hf.comp (measurable_padJoint n)).comp (hproj n)
  have hg : Measurable g := hf.comp ((measurable_fst.comp measurable_fst).prodMk measurable_snd)
  have hp : ∀ᵐ z ∂P, ∀ᶠ n in atTop, F n z = g z := by
    filter_upwards [critical_eventual_tape_reconstruction A q hq hworkq] with z hz
    exact hz.mono (fun n hn => by simp only [F,g,hn])
  have hq' : ∀ᵐ z ∂Q, ∀ᶠ n in atTop, F n z = g z := by
    filter_upwards [critical_eventual_tape_reconstruction A r hr hworkr] with z hz
    exact hz.mono (fun n hn => by simp only [F,g,hn])
  have hbound (n : ℕ) :
      (1-(hellingerAffinity (P.map (F n)) (Q.map (F n))).toReal)*k ≤ b := by
    let u : R × Prefix n → I := f ∘ padJoint n
    have hu : Measurable u := hf.comp (measurable_padJoint n)
    have hdp := hellingerAffinity_map_finite (criticalPrefixLaw A q hq n)
      (criticalPrefixLaw A r hr n) u hu
    have hm (s : ℝ → unitInterval) (hs : Measurable s) :
        (criticalPrefixLaw A s hs n).map u =
          (criticalExperimentLaw A s hs).map (F n) := by
      rw [criticalPrefixLaw,Measure.map_map hu (hproj n)]
      rfl
    rw [hm q hq,hm r hr] at hdp
    let : IsProbabilityMeasure (P.map (F n)) := inferInstance
    let : IsProbabilityMeasure (Q.map (F n)) := inferInstance
    have hfinite : hellingerAffinity (P.map (F n)) (Q.map (F n)) ≠ ∞ :=
      ne_of_lt ((hellingerAffinity_probability_le_one _ _).trans_lt (by simp))
    have hdr := ENNReal.toReal_mono hfinite hdp
    exact (mul_le_mul_of_nonneg_right (sub_le_sub_left hdr 1) hk).trans (hprefix n)
  have hlim := hellingerAffinity_tendsto_eventual_maps P Q F g hF hg hp hq'
  exact le_of_tendsto ((tendsto_const_nhds.sub hlim).mul tendsto_const_nhds)
    (Eventually.of_forall hbound)

end ThresholdHC.CriticalEntropy
