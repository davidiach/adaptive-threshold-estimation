import ThresholdHC.ContinuousObserved.PrefixLaw

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace ThresholdHC.ContinuousObserved
open ThresholdHC ThresholdHC.Tier3 ThresholdHC.Tier4 ThresholdHC.Tier6 ThresholdHC.ObservedState
open ThresholdHC.CriticalEntropy ThresholdHC.ObservableSimulation

/-- The finite-prefix law of ordinary fresh observations at the selected
states. The private seed is retained jointly with the observations. -/
def RealizesQueryPrefixes {N : ℕ} {R : Type} [MeasurableSpace R]
    (D : QueryDesign N) (A : StateEstimator R) (s : Fin N → Bool)
    (P : Measure (R × ProcessTape)) : Prop :=
  ∀ (n : ℕ) (F : R × Prefix n → ℝ≥0∞), Measurable F →
    (∫⁻ z, F (z.1,processPrefix n z.2) ∂P) =
      ∫⁻ r, prefixExpectation D s (A.continues r) (A.query r) n (fun w => F (r,w)) ∂A.randomLaw

theorem decoded_population_prefix {N : ℕ} {R : Type} [MeasurableSpace R]
    (D : QueryDesign N) (A : StateEstimator R) (r : R) (v : ℕ → ℝ)
    (raw : Fin N → ℕ → Bool) (n : ℕ) :
    processPrefix n (decodeTape (perturb D A (r,v)) (populationPath ((reduction D A).policy (r,v)) raw)) =
      noisyWord D (A.continues r) (A.query r) n v raw := by
  rw [← decodePrefix_processPrefix,populationPath_prefix,noisyWord_decode]
  rfl

theorem queryLaw_realizes {N : ℕ} {R : Type} [MeasurableSpace R]
    (D : QueryDesign N) (A : StateEstimator R) (s : Fin N → Bool) :
    RealizesQueryPrefixes D A s (queryLaw D A s) := by
  intro n F hF
  let G (z : (R × (ℕ → ℝ)) × (Fin N → ℕ → Bool)) :=
    F (z.1.1,noisyWord D (A.continues z.1.1) (A.query z.1.1) n z.1.2 z.2)
  have hprefix : Measurable (fun z : R × ProcessTape => F (z.1,processPrefix n z.2)) :=
    hF.comp (measurable_jointPrefix n)
  have he : (fun z : (R × (ℕ → ℝ)) × (Fin N → ℕ → Bool) =>
      F (z.1.1,processPrefix n
        (decodeTape (perturb D A z.1) (populationPath ((reduction D A).policy z.1) z.2)))) = G := by
    funext z
    rw [decoded_population_prefix]
  have hG : Measurable G := by
    rw [← he]
    exact hprefix.comp ((measurable_decoded D A).comp (measurable_observation (reduction D A)))
  rw [queryLaw,lintegral_map hprefix (measurable_decoded D A),modelLaw]
  have hdecoded : Measurable (fun z : (R × (ℕ → ℝ)) × ProcessTape =>
      F ((decoded D A z).1,processPrefix n (decoded D A z).2)) :=
    hprefix.comp (measurable_decoded D A)
  rw [lintegral_map hdecoded (measurable_observation (reduction D A))]
  simp only [decoded]
  rw [he]
  change (∫⁻ z, G z ∂(A.randomLaw.prod uniformTapeMeasure).prod
    (Measure.pi (fun i => Tier2.tapeMeasure (gapParameter (s i) (D.cap i))))) = _
  rw [lintegral_prod _ hG.aemeasurable]
  rw [lintegral_prod _ hG.lintegral_prod_right'.aemeasurable]
  apply lintegral_congr
  intro r
  have hm : Measurable (fun z : (ℕ → ℝ) × (Fin N → ℕ → Bool) =>
      F (r,noisyWord D (A.continues r) (A.query r) n z.1 z.2)) :=
    (hF.comp (measurable_const.prodMk measurable_id)).comp
      (measurable_noisyWord D (A.continues r) (A.query r) n)
  rw [← lintegral_prod _ hm.aemeasurable]
  exact noisyWord_prefix_law D s (A.continues r) (A.query r) n (fun w => F (r,w))

theorem query_prefix_unique {N : ℕ} {R : Type} [MeasurableSpace R]
    (D : QueryDesign N) (A : StateEstimator R) (s : Fin N → Bool)
    (P Q : Measure (R × ProcessTape)) [IsFiniteMeasure P] [IsFiniteMeasure Q]
    (hP : RealizesQueryPrefixes D A s P) (hQ : RealizesQueryPrefixes D A s Q) : P = Q := by
  apply joint_tape_law_ext P Q
  intro n
  apply Measure.ext
  intro E hE
  let F : R × Prefix n → ℝ≥0∞ := E.indicator (fun _ => 1)
  have hF : Measurable F := measurable_const.indicator hE
  have hp := hP n F hF
  have hq := hQ n F hF
  rw [← lintegral_map hF (measurable_jointPrefix n)] at hp hq
  simpa only [F,lintegral_indicator_fun_one hE] using hp.trans hq.symm

end ThresholdHC.ContinuousObserved
