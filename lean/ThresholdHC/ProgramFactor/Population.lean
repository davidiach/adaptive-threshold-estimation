import ThresholdHC.ProgramFactor.Absorption
import ThresholdHC.StoppingProgram.PrefixRisk

/-! The local-to-population transfer and the observable prefix risk bound,
restated for an arbitrary local constant. These follow
finite_population_information, creation_population_information,
observable_prefix_information(_budget) and observable_prefix_risk of the
StoppingProgram group line by line. Only the local stopped-Hellinger bound is
taken as a hypothesis, in place of the midpoint lemma
ordered_stopped_hellinger_work. The weighted endpoints then supply it. -/

noncomputable section
namespace ThresholdHC.ProgramFactor
open MeasureTheory
open scoped ENNReal
open ThresholdHC.CriticalEntropy ThresholdHC.ObservableSimulation ThresholdHC.StoppingProgram
open ThresholdHC.Tier3 ThresholdHC.Tier6 ThresholdHC.RareAboveTwo

theorem finite_population_information_of_local {m N : ℕ}
    (μ : Measure Gap) [IsProbabilityMeasure μ] (q r : SignLaw) (c : ℝ)
    (hloc : ∀ {R E : Type} [MeasurableSpace R] [MeasurableSpace E]
      (ν : Measure R) [IsProbabilityMeasure ν] (A : StoppedProcedure R E),
      (∀ z, A.stop z ≤ N) → stoppedHellinger μ ν q r A N ≤
        c*(populationExpectedWork μ ν (gapParameter false) (gapParameter true)
          (signUnit (midpointPrior q r)) A).toReal)
    (pol : List Bool → Option (Fin m)) :
    1-realFiniteAffinity
      (finitePopulationWeight (n := N) μ pol (fun d : Gap => (d : ℝ)) (fun _ => q.val))
      (finitePopulationWeight μ pol (fun d : Gap => (d : ℝ)) (fun _ => r.val)) ≤
      c*(finitePopulationExpectedWork μ (gapParameter false) (gapParameter true)
          (signUnit (midpointPrior q r)) pol N).toReal := by
  classical
  let s := midpointPrior q r
  let ν := Measure.pi (fun _ : Fin m => originalPopulationTapeLaw μ s)
  let W (i : Fin m) := populationExpectedWork μ ν (gapParameter false) (gapParameter true)
    (signUnit s) (localSimulationProcedure i N pol)
  have hlocal (i : Fin m) :
      1-realFiniteAffinity
        (finitePopulationWeight (n := N) μ pol (fun d : Gap => (d : ℝ))
          (fun j d => if j=i then q.val d else s.val d))
        (finitePopulationWeight μ pol (fun d : Gap => (d : ℝ))
          (fun j d => if j=i then r.val d else s.val d)) ≤ c*(W i).toReal := by
    have hA := localSimulation_affinity_le μ (gapParameter false) (gapParameter true)
      (signUnit q) (signUnit r) (signUnit s)
      (measurable_gapParameter false) (measurable_gapParameter true)
      (measurable_signUnit q) (measurable_signUnit r) (measurable_signUnit s)
      (fun d : Gap => (d : ℝ)) measurable_subtype_coe
      (fun d => ⟨d.property.1.le,d.property.2⟩)
      (ae_of_all _ (fun d => by simp [gapParameter,sub_eq_add_neg]))
      (ae_of_all _ (fun d => by simp [gapParameter])) pol i (n := N)
    have hh := hloc ν (localSimulationProcedure i N pol)
      (localSimulationProcedure_capped i N pol)
    exact (sub_le_sub_left hA 1).trans hh
  have hhyb := finite_population_hybrid_decomposition μ pol (fun d : Gap => (d : ℝ))
    q.val r.val measurable_subtype_coe q.property.1 r.property.1
    (fun d => ⟨d.property.1.le,d.property.2⟩) q.property.2 r.property.2 (n := N)
  have he (u : Gap → ℝ) (i : Fin m) :
      (fun j => if j=i then u else fun d => (q.val d+r.val d)/2) =
        (fun j d => if j=i then u d else s.val d) := by
    funext j d
    by_cases hj : j=i
    · simp [hj]
    · simp only [hj,ite_false]
      dsimp only [s,StoppingProgram.midpointPrior,mixPrior]
      ring
  simp_rw [he] at hhyb
  calc
    _ ≤ ∑ i : Fin m, (1-realFiniteAffinity
        (finitePopulationWeight (n := N) μ pol (fun d : Gap => (d : ℝ))
          (fun j d => if j=i then q.val d else s.val d))
        (finitePopulationWeight μ pol (fun d : Gap => (d : ℝ))
          (fun j d => if j=i then r.val d else s.val d))) := hhyb
    _ ≤ ∑ i : Fin m, c*(W i).toReal := Finset.sum_le_sum (fun i _ => hlocal i)
    _ = _ := by
      rw [← Finset.mul_sum]
      congr 1
      exact population_localSimulation_total_work_real μ (gapParameter false) (gapParameter true)
        (signUnit s) (measurable_gapParameter false) (measurable_gapParameter true)
        (measurable_signUnit s) pol

theorem creation_population_information_of_local (μ : Measure Gap) [IsProbabilityMeasure μ]
    (q r : SignLaw) (N : ℕ) (c : ℝ)
    (hloc : ∀ {R E : Type} [MeasurableSpace R] [MeasurableSpace E]
      (ν : Measure R) [IsProbabilityMeasure ν] (A : StoppedProcedure R E),
      (∀ z, A.stop z ≤ N) → stoppedHellinger μ ν q r A N ≤
        c*(populationExpectedWork μ ν (gapParameter false) (gapParameter true)
          (signUnit (midpointPrior q r)) A).toReal)
    (pol : List Bool → Option ℕ) :
    1-realFiniteAffinity
      (creationPopulationWeight (n := N) μ pol (fun d : Gap => (d : ℝ)) q.val)
      (creationPopulationWeight μ pol (fun d : Gap => (d : ℝ)) r.val) ≤
      c*∑ w : Fin N → Option Bool,
          creationPopulationWeight μ pol (fun d : Gap => (d : ℝ))
            (midpointPrior q r).val w*ThresholdHC.workOf w := by
  let cpol := ThresholdHC.Tier5.capPolicy (ThresholdHC.Tier5.coinCap N pol) pol
  have h := finite_population_information_of_local (N := N) μ q r c hloc cpol
  rw [finitePopulation_work_real μ _ _ _ (measurable_gapParameter false)
    (measurable_gapParameter true) (measurable_signUnit (midpointPrior q r))
    (fun d : Gap => (d : ℝ)) measurable_subtype_coe
    (fun d => ⟨d.property.1.le,d.property.2⟩)
    (ae_of_all _ (fun d => by simp [gapParameter,sub_eq_add_neg]))
    (ae_of_all _ (fun d => by simp [gapParameter])) cpol] at h
  have he (u : SignLaw) :
      creationPopulationWeight (n := N) μ pol (fun d : Gap => (d : ℝ)) u.val =
        finitePopulationWeight μ cpol (fun d : Gap => (d : ℝ)) (fun _ => u.val) := by
    funext w
    exact creationPopulationWeight_eq_finite μ pol _ u.val measurable_subtype_coe u.property.1 w
  rw [he q,he r,he (midpointPrior q r)]
  exact h

theorem observable_prefix_information_of_local {R : Type} [MeasurableSpace R]
    (μ : Measure Gap) [IsProbabilityMeasure μ] (A : AdaptiveEstimator R)
    (q r : SignLaw) (N : ℕ) (c : ℝ)
    (hloc : ∀ {R E : Type} [MeasurableSpace R] [MeasurableSpace E]
      (ν : Measure R) [IsProbabilityMeasure ν] (A : StoppedProcedure R E),
      (∀ z, A.stop z ≤ N) → stoppedHellinger μ ν q r A N ≤
        c*(populationExpectedWork μ ν (gapParameter false) (gapParameter true)
          (signUnit (midpointPrior q r)) A).toReal) :
    1-(hellingerAffinity (observablePrefixLaw μ A q N)
      (observablePrefixLaw μ A r N)).toReal ≤
      c*∫ z, ThresholdHC.workOf (processPrefix N z.2) ∂experimentLaw μ A (midpointPrior q r) := by
  have h := observable_population_hellinger_bound A.randomLaw μ
    (experimentLaw μ A q) (experimentLaw μ A r) (experimentLaw μ A (midpointPrior q r))
    Prod.fst Prod.snd A.policy (fun d : Gap => (d : ℝ)) q.val r.val (midpointPrior q r).val
    measurable_fst observable_tape_measurable A.policy_measurable measurable_subtype_coe
    q.property.1 r.property.1 (midpointPrior q r).property.1
    (fun d => ⟨d.property.1.le,d.property.2⟩) q.property.2 r.property.2 (midpointPrior q r).property.2
    (population_realization R μ A q).2 (population_realization R μ A r).2
    (population_realization R μ A (midpointPrior q r)).2 N 1 c
    (fun u => by simpa only [mul_one] using
      creation_population_information_of_local μ q r N c hloc (A.policy u))
  simpa only [mul_one,observablePrefixLaw] using h

theorem observable_prefix_information_budget_of_local {R : Type} [MeasurableSpace R]
    (μ : Measure Gap) [IsProbabilityMeasure μ] (A : AdaptiveEstimator R)
    (q r : SignLaw) (N : ℕ) (B : ℝ) (hB : 0 ≤ B) (c : ℝ) (hc : 0 ≤ c)
    (hloc : ∀ {R E : Type} [MeasurableSpace R] [MeasurableSpace E]
      (ν : Measure R) [IsProbabilityMeasure ν] (A : StoppedProcedure R E),
      (∀ z, A.stop z ≤ N) → stoppedHellinger μ ν q r A N ≤
        c*(populationExpectedWork μ ν (gapParameter false) (gapParameter true)
          (signUnit (midpointPrior q r)) A).toReal)
    (hw : expectedWork μ A (midpointPrior q r) ≤ ENNReal.ofReal B) :
    1-(hellingerAffinity (observablePrefixLaw μ A q N)
      (observablePrefixLaw μ A r N)).toReal ≤ c*B := by
  have hfin : expectedWork μ A (midpointPrior q r) < ⊤ := hw.trans_lt (by simp)
  have hpre := prefix_work_le_total (experimentLaw μ A (midpointPrior q r))
    Prod.snd observable_tape_measurable hfin N
  have hwork : (expectedWork μ A (midpointPrior q r)).toReal ≤ B := by
    have h := ENNReal.toReal_mono (by simp : ENNReal.ofReal B ≠ ⊤) hw
    simpa only [ENNReal.toReal_ofReal hB] using h
  exact (observable_prefix_information_of_local μ A q r N c hloc).trans
    (mul_le_mul_of_nonneg_left (hpre.trans hwork) hc)

theorem observable_prefix_risk_of_local {R : Type} [MeasurableSpace R]
    (μ : Measure Gap) [IsProbabilityMeasure μ] (A : AdaptiveEstimator R)
    (q r : SignLaw) (N : ℕ) (B : ℝ) (hB : 0 ≤ B) (c : ℝ) (hc : 0 ≤ c)
    (hloc : ∀ {R E : Type} [MeasurableSpace R] [MeasurableSpace E]
      (ν : Measure R) [IsProbabilityMeasure ν] (A : StoppedProcedure R E),
      (∀ z, A.stop z ≤ N) → stoppedHellinger μ ν q r A N ≤
        c*(populationExpectedWork μ ν (gapParameter false) (gapParameter true)
          (signUnit (midpointPrior q r)) A).toReal)
    (hw : expectedWork μ A (midpointPrior q r) ≤ ENNReal.ofReal B)
    (hab : signMean μ q.val ≤ signMean μ r.val)
    (f : R × (Fin N → Option Bool) → ℝ) (hf : Measurable f) :
    ENNReal.ofReal ((signMean μ r.val-signMean μ q.val)/2*(1-c*B)) ≤
        max (rootMeanRisk (observablePrefixLaw μ A q N) f (signMean μ q.val))
          (rootMeanRisk (observablePrefixLaw μ A r N) f (signMean μ r.val)) := by
  have hi := observable_prefix_information_budget_of_local μ A q r N B hB c hc hloc hw
  have hr := affinity_rms_risk (observablePrefixLaw μ A q N) (observablePrefixLaw μ A r N)
    f hf (signMean μ q.val) (signMean μ r.val) hab
  apply le_trans (ENNReal.ofReal_le_ofReal ?_) hr
  have hgap : 0 ≤ (signMean μ r.val-signMean μ q.val)/2 := by
    have := sub_nonneg.mpr hab
    positivity
  have hinfo : 1-c*B ≤
      (hellingerAffinity (observablePrefixLaw μ A q N) (observablePrefixLaw μ A r N)).toReal := by
    linarith [hi]
  nlinarith [mul_le_mul_of_nonneg_left hinfo hgap]

/-- For the weighted endpoints, the larger of the two prefix RMS risks is at
least `aΔ/2 · (1 - a²KB/(2(1-a)²))` when the new midpoint has expected work at
most `B`, where `K` is the ordinary information/work ratio. -/
theorem weighted_prefix_risk {R : Type} [MeasurableSpace R]
    (μ : Measure Gap) [IsProbabilityMeasure μ] (A : AdaptiveEstimator R)
    (Q : FourPriors) (a : ℝ) (ha : 0 ≤ a ∧ a ≤ 1) (ha1 : a < 1)
    (N : ℕ) (hN : 0 < N) (hK : informationRatio μ N Q ≠ ⊤) (B : ℝ) (hB : 0 ≤ B)
    (hw : expectedWork μ A (midpointPrior (weightedLow Q a ha) (weightedHigh Q a ha)) ≤
      ENNReal.ofReal B)
    (hab : signMean μ Q.low.val ≤ signMean μ Q.high.val)
    (f : R × (Fin N → Option Bool) → ℝ) (hf : Measurable f) :
    ENNReal.ofReal (a*(signMean μ Q.high.val-signMean μ Q.low.val)/2*
      (1-a^2/(2*(1-a)^2)*(informationRatio μ N Q).toReal*B)) ≤
        max (rootMeanRisk (observablePrefixLaw μ A (weightedLow Q a ha) N) f
            (signMean μ (weightedLow Q a ha).val))
          (rootMeanRisk (observablePrefixLaw μ A (weightedHigh Q a ha) N) f
            (signMean μ (weightedHigh Q a ha).val)) := by
  have hc : 0 ≤ a^2/(2*(1-a)^2)*(informationRatio μ N Q).toReal :=
    mul_nonneg (by positivity) ENNReal.toReal_nonneg
  have hg := weighted_gap μ Q a ha
  have hab' : signMean μ (weightedLow Q a ha).val ≤ signMean μ (weightedHigh Q a ha).val := by
    apply sub_nonneg.mp
    rw [hg]
    exact mul_nonneg ha.1 (sub_nonneg.mpr hab)
  have h := observable_prefix_risk_of_local μ A (weightedLow Q a ha) (weightedHigh Q a ha) N B hB
    _ hc (fun ν _ A hcap => weighted_stopped_hellinger_work μ ν Q a ha ha1 A N hN hK hcap)
    hw hab' f hf
  rw [hg] at h
  exact h

end ThresholdHC.ProgramFactor
