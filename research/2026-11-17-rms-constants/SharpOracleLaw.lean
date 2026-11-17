import SharpOracleTapes
import SharpPopulationTransfer

/-! Equality of the entire oracle observation law, conditional on its private seed. -/
noncomputable section
namespace ThresholdHC.SharpRMS
open MeasureTheory Tier3 Tier4 Tier5 Tier6 CriticalEntropy ContinuousObserved ObservableSimulation OracleLower
open scoped ENNReal

abbrev NoiseArray := ℕ → ℕ → ℝ
abbrev RawArray := ℕ → ℕ → Bool

def oracleArrayLaw (g : Gap) (q : SignLaw) : Measure (NoiseArray × RawArray) :=
  (Measure.infinitePi (fun _ : ℕ => uniformTapeMeasure)).prod
    (Measure.infinitePi (fun _ : ℕ => originalPopulationTapeLaw (Measure.dirac g) q))

instance (g : Gap) (q : SignLaw) : IsProbabilityMeasure (oracleArrayLaw g q) := by
  unfold oracleArrayLaw
  infer_instance

def oracleVirtual {R : Type} [MeasurableSpace R] (A : OracleEstimator R) (g : Gap)
    (z : R × (NoiseArray × RawArray)) (i : ℕ) := virtualTape (A.gap z.1 i) g 0 0 (z.2.1 i) (z.2.2 i)

theorem measurable_oracleVirtual {R : Type} [MeasurableSpace R] (A : OracleEstimator R) (g : Gap) :
    Measurable (oracleVirtual A g) := by
  apply Measurable.of_eval
  intro i
  change Measurable ((fun z : (Gap × (ℕ → ℝ)) × (ℕ → Bool) => virtualTape z.1.1 g 0 0 z.1.2 z.2) ∘
    (fun z : R × (NoiseArray × RawArray) => ((A.gap z.1 i,z.2.1 i),z.2.2 i)))
  exact (measurable_virtualTape_joint g 0 0).comp (((A.gap_measurable i).comp measurable_fst |>.prodMk
    ((measurable_pi_apply i).comp (measurable_fst.comp measurable_snd))).prodMk
    ((measurable_pi_apply i).comp (measurable_snd.comp measurable_snd)))

def oracleVirtualPath {R : Type} [MeasurableSpace R] (A : OracleEstimator R) (g : Gap)
    (z : R × (NoiseArray × RawArray)) := populationPath (A.policy z.1) (oracleVirtual A g z)

theorem measurable_oracleVirtualPath {R : Type} [MeasurableSpace R] (A : OracleEstimator R) (g : Gap) :
    Measurable (oracleVirtualPath A g) :=
  (measurable_seeded_populationPath A.policy (fun ys => measurable_to_countable' (A.policy_measurable ys))).comp
    (measurable_fst.prodMk (measurable_oracleVirtual A g))

theorem oracle_virtual_law {R : Type} [MeasurableSpace R] (A : OracleEstimator R) (g : Gap) (q : SignLaw) :
    (A.randomLaw.prod (oracleArrayLaw g q)).map (fun z => (z.1,oracleVirtualPath A g z)) =
    oracleLaw A (sourceTarget g q) := by
  let T := oracleArrayLaw g q
  let P := A.randomLaw.prod T
  let q' := sourceTarget g q
  have mv := measurable_oracleVirtualPath A g
  have hreal : RealizesCreationPrefixes A.randomLaw P Prod.fst (oracleVirtualPath A g)
    A.policy (fun r i => (A.gap r i).val) (fun r i => q'.val (A.gap r i)) := by
    intro n f mf bound
    obtain ⟨C,hC⟩ := bound
    have mpre : Measurable (fun z => processPrefix n (oracleVirtualPath A g z)) :=
      Measurable.of_eval (fun j => (measurable_pi_apply j.val).comp mv)
    have mtest : Measurable (Function.uncurry f) := measurable_from_prod_countable_left mf
    have hi := integrable_of_abs_bound P _ (mtest.comp (measurable_fst.prodMk mpre)) C
      (fun z => hC z.1 (processPrefix n (oracleVirtualPath A g z)))
    rw [integral_prod (fun z : R × (NoiseArray × RawArray) => f z.1 (processPrefix n (oracleVirtualPath A g z))) hi]
    apply integral_congr_ae
    apply ae_of_all
    intro r
    let path (v : NoiseArray × RawArray) := processPrefix n (oracleVirtualPath A g (r,v))
    have mp : Measurable path := mpre.comp (measurable_const.prodMk measurable_id)
    have vmeas : Measurable (fun v : NoiseArray × RawArray => oracleVirtual A g (r,v)) :=
      (measurable_oracleVirtual A g).comp (measurable_const.prodMk measurable_id)
    have map : T.map path = finiteWeightMeasure (creationLaw (n:=n) (A.policy r)
        (fun i => (A.gap r i).val) (fun i => q'.val (A.gap r i))) := by
      have ep : path = (fun x => (populationSimulation (A.policy r) n x).2) ∘
          (fun v => oracleVirtual A g (r,v)) := by funext v; exact populationPath_prefix _ _ _
      rw [ep,←Measure.map_map (measurable_populationSimulation_word n _) vmeas]
      change ((oracleArrayLaw g q).map (fun z i => virtualTape (A.gap r i) g 0 0 (z.1 i) (z.2 i))).map _ = _
      rw [oracleArrayLaw,fixed_array_tapes]
      exact fixed_oracle_words (A.gap r) q' (A.policy r) n
    have hfr : Measurable (f r) := measurable_of_finite _
    have hn := (creationLaw_total n (A.policy r) (fun i => (A.gap r i).val) (fun i => q'.val (A.gap r i))
      (fun i => ⟨(A.gap r i).property.1.le,(A.gap r i).property.2⟩) (fun i => q'.property.2 _)).1
    change (∫ v, f r (path v) ∂T) = _
    rw [←integral_map mp.aemeasurable hfr.aestronglyMeasurable,map,integral_fintype]
    · simp only [finiteWeightMeasure_singleton,Measure.real,ENNReal.toReal_ofReal (hn _),smul_eq_mul]
    · rw [←map]
      exact integrable_of_abs_bound _ _ hfr C (hC r)
  have eq := realizes_creation_joint_law_unique A.randomLaw P (oracleLaw A q')
    Prod.fst (oracleVirtualPath A g) Prod.fst Prod.snd A.policy
    (fun r i => (A.gap r i).val) (fun r i => q'.val (A.gap r i))
    measurable_fst mv measurable_fst measurable_snd hreal (oracle_realization R A q').2
  change P.map (fun x => (x.1,oracleVirtualPath A g x)) = (oracleLaw A q').map id at eq
  simpa only [Measure.map_id] using eq

end ThresholdHC.SharpRMS
