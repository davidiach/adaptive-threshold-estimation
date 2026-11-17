import ThresholdHC.SharpRMS.SingleTape
import ThresholdHC.SharpRMS.ArrayLaw
import ThresholdHC.OracleLower.Realization

/-! Conditional on an oracle seed, the magnitudes can be an arbitrary array. -/
noncomputable section
namespace ThresholdHC.SharpRMS
open MeasureTheory Tier3 Tier5 Tier6 CriticalEntropy ObservableSimulation Proofs
open scoped ENNReal

theorem fixed_single_tape (d g : Gap) (q : SignLaw) :
    (uniformTapeMeasure.prod (originalPopulationTapeLaw (Measure.dirac g) q)).map
      (fun z => virtualTape d g 0 0 z.1 z.2) = originalPopulationTapeLaw (Measure.dirac d) (sourceTarget g q) := by
  let T := originalPopulationTapeLaw (Measure.dirac g) q
  have pin : MeasurePreserving (Prod.mk d) uniformTapeMeasure ((Measure.dirac d).prod uniformTapeMeasure) :=
    ⟨measurable_prodMk_left, (Measure.dirac_prod _).symm⟩
  have whole := pin.prod (MeasurePreserving.id T)
  have eq := single_tape_law (Measure.dirac d) g q
  rw [←whole.map_eq,Measure.map_map (measurable_virtualTape_joint g 0 0) whole.measurable] at eq
  exact eq

theorem fixed_array_tapes (d : ℕ → Gap) (g : Gap) (q : SignLaw) :
    ((Measure.infinitePi (fun _ : ℕ => uniformTapeMeasure)).prod
      (Measure.infinitePi (fun _ : ℕ => originalPopulationTapeLaw (Measure.dirac g) q))).map
      (fun z i => virtualTape (d i) g 0 0 (z.1 i) (z.2 i)) =
    Measure.infinitePi (fun i => originalPopulationTapeLaw (Measure.dirac (d i)) (sourceTarget g q)) := by
  let T := originalPopulationTapeLaw (Measure.dirac g) q
  let f (i : ℕ) (x : (ℕ → ℝ) × (ℕ → Bool)) := virtualTape (d i) g 0 0 x.1 x.2
  have mf (i) : Measurable (f i) := (measurable_virtualTape_joint g 0 0).comp
    ((measurable_const.prodMk measurable_fst).prodMk measurable_snd)
  have h := zip_population uniformTapeMeasure T
  have m : Measurable (fun x : ℕ → (ℕ → ℝ) × (ℕ → Bool) => fun i => f i (x i)) :=
    Measurable.of_eval (fun i => (mf i).comp (measurable_pi_apply i))
  have eq := Measure.infinitePi_map_pi (fun _ : ℕ => uniformTapeMeasure.prod T) mf
  rw [←h.map_eq,Measure.map_map m h.measurable] at eq
  change ((Measure.infinitePi (fun _ : ℕ => uniformTapeMeasure)).prod (Measure.infinitePi (fun _ : ℕ => T))).map
    (fun z i => f i (z.1 i,z.2 i)) = Measure.infinitePi (fun i => (uniformTapeMeasure.prod T).map (f i)) at eq
  apply eq.trans
  congr 1
  funext i
  exact fixed_single_tape (d i) g q

private theorem fixed_finite_words {m : ℕ} (d : Fin m → Gap) (q : SignLaw)
    (pol : List Bool → Option (Fin m)) (n : ℕ) :
    (Measure.pi (fun i => originalPopulationTapeLaw (Measure.dirac (d i)) q)).map
      (fun x => (populationSimulation pol n x).2) =
      finiteWeightMeasure (transcriptLaw (n:=n) pol (fun i => (d i).val) (fun i => q.val (d i))) := by
  let κ (i : Fin m) := populationParameterLaw (Measure.dirac (d i)) (gapParameter false) (gapParameter true) (signUnit q)
  let (i : Fin m) : IsProbabilityMeasure (κ i) := populationParameterLaw_probability _ _ _ _
    (measurable_gapParameter false) (measurable_gapParameter true) (measurable_signUnit q)
  rw [show (fun i => originalPopulationTapeLaw (Measure.dirac (d i)) q) = (fun i => parameterTapeLaw (κ i)) by rfl,
      parameterTapeLaw_population_word_law]
  congr 1
  funext w
  rw [parameter_pathProb_factor,transcriptLaw_factor]
  congr 1
  apply Finset.prod_congr rfl
  intro i _
  have mf : Measurable (fun p : unitInterval => coinLike pol w i p.val) :=
    (continuous_coinLike pol w i).measurable.comp measurable_subtype_coe
  rw [populationParameterLaw_integral _ _ _ _ (measurable_gapParameter false) (measurable_gapParameter true)
    (measurable_signUnit q) _ mf 1 (fun p => by
      rw [abs_of_nonneg (coinLike_nonneg pol w i p.property.1 p.property.2)]
      exact coinLike_le_one pol w i p p.property.1 p.property.2),integral_dirac]
  simp [gapParameter,signUnit,sub_eq_add_neg]

theorem fixed_oracle_words (d : ℕ → Gap) (q : SignLaw) (pol : List Bool → Option ℕ) (n : ℕ) :
    (Measure.infinitePi (fun i => originalPopulationTapeLaw (Measure.dirac (d i)) q)).map
      (fun x => (populationSimulation pol n x).2) =
    finiteWeightMeasure (creationLaw (n:=n) pol (fun i => (d i).val) (fun i => q.val (d i))) := by
  let m := coinCap n pol
  let τ (i : ℕ) := originalPopulationTapeLaw (Measure.dirac (d i)) q
  let res (x : ℕ → ℕ → Bool) : Fin m → ℕ → Bool := fun i => x i.val
  have mr : Measurable res := Measurable.of_eval (fun i => measurable_pi_apply i.val)
  have hm : (Measure.infinitePi τ).map res = Measure.pi (fun i : Fin m => τ i.val) := by
    rw [Measure.map_infinitePi_infinitePi_of_inj Fin.val_injective,Measure.infinitePi_eq_pi]
  calc
    _ = ((Measure.infinitePi τ).map res).map (fun s => (populationSimulation (capPolicy m pol) n s).2) := by
      rw [Measure.map_map (measurable_populationSimulation_word n _) mr]
      congr 1
      funext x
      exact populationSimulation_cap n pol x
    _ = _ := by rw [hm]; exact fixed_finite_words (fun i => d i.val) q (capPolicy m pol) n

end ThresholdHC.SharpRMS
