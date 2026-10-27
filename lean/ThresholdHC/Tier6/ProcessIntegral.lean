import ThresholdHC.Tier6.ProcessModel
import Mathlib.Probability.Kernel.Composition.IntegralCompProd

noncomputable section
open MeasureTheory ProbabilityTheory Preorder
open scoped ENNReal
namespace ThresholdHC.Tier6
open ThresholdHC.Tier3 ThresholdHC.Tier5

theorem creationStepKernel_integral {Seed : Type} [MeasurableSpace Seed]
    (pol : Seed → List Bool → Option ℕ) (d q : Seed → ℕ → ℝ)
    (hp : MeasurableCreationPolicy pol) (hdm : MeasurableEnvironment d)
    (hqm : MeasurableEnvironment q)
    (hd : ∀ u i, 0 ≤ d u i ∧ d u i ≤ 1/2)
    (hq : ∀ u i, 0 ≤ q u i ∧ q u i ≤ 1) (n : ℕ)
    (x : (i : Finset.Iic n) → ProcessCoord Seed i) (f : Option Bool → ℝ) :
    (∫ o, f o ∂creationStepKernel pol d q hp hdm hqm n x) =
      ∑ o : Option Bool, creationTransition (pol (coordSeed x)) (d (coordSeed x))
        (q (coordSeed x)) (coordPrefix x) o * f o := by
  classical
  letI := creationNextKernel_markov pol d q hp hdm hqm hd hq n
  change (∫ o, f o ∂creationNextKernel pol d q hp hdm hqm n (coordSeed x, coordPrefix x)) = _
  rw [integral_fintype (Integrable.of_finite)]
  apply Finset.sum_congr rfl
  intro o ho
  simp only [smul_eq_mul]
  congr 1
  simp only [measureReal_def, creationStepKernel, Kernel.comap_apply, creationNextKernel,
    Kernel.coe_mk, Measure.finsetSum_apply,
    Measure.smul_apply, smul_eq_mul, Measure.dirac_apply' _ (measurableSet_singleton o)]
  simp only [Set.indicator_apply, Set.mem_singleton_iff, Pi.one_apply,
    ite_mul, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  exact ENNReal.toReal_ofReal (creationTransition_nonneg _ _ _ (hd _) (hq _) _ _)

theorem trajMeasure_map_zero {X : ℕ → Type} [∀ n, MeasurableSpace (X n)]
    (μ : Measure (X 0))
    (κ : (n : ℕ) → Kernel ((i : Finset.Iic n) → X i) (X (n+1)))
    [∀ n, IsMarkovKernel (κ n)] :
    (Kernel.trajMeasure μ κ).map (fun x => x 0) = μ := by
  have hzero : (Kernel.trajMeasure μ κ).map (frestrictLe 0) =
      μ.map (MeasurableEquiv.piUnique _).symm := by
    rw [Kernel.trajMeasure, Measure.map_comp _ _ (measurable_frestrictLe 0),
      Kernel.traj_map_frestrictLe, Kernel.partialTraj_self]
    simp
  have hcomp : (fun x : (n : ℕ) → X n => x 0) =
      (fun y : (i : Finset.Iic 0) → X i => y ⟨0, by simp⟩) ∘ frestrictLe 0 := rfl
  rw [hcomp, ← Measure.map_map (measurable_pi_apply _) (measurable_frestrictLe 0), hzero,
    Measure.map_map (measurable_pi_apply _) (MeasurableEquiv.measurable _)]
  convert Measure.map_id using 2
  funext u
  rfl

def creationTrajectoryLaw {Seed : Type} [MeasurableSpace Seed]
    (μ : Measure Seed) (pol : Seed → List Bool → Option ℕ) (d q : Seed → ℕ → ℝ)
    (hp : MeasurableCreationPolicy pol) (hdm : MeasurableEnvironment d)
    (hqm : MeasurableEnvironment q)
    (hd : ∀ u i, 0 ≤ d u i ∧ d u i ≤ 1/2)
    (hq : ∀ u i, 0 ≤ q u i ∧ q u i ≤ 1) : Measure ((n : ℕ) → ProcessCoord Seed n) := by
  letI : ∀ n, IsMarkovKernel (creationStepKernel pol d q hp hdm hqm n) :=
    fun n => creationStepKernel_markov pol d q hp hdm hqm hd hq n
  exact Kernel.trajMeasure (X := ProcessCoord Seed) μ (creationStepKernel pol d q hp hdm hqm)

instance creationTrajectoryLaw_probability {Seed : Type} [MeasurableSpace Seed]
    (μ : Measure Seed) [IsProbabilityMeasure μ]
    (pol : Seed → List Bool → Option ℕ) (d q : Seed → ℕ → ℝ)
    (hp : MeasurableCreationPolicy pol) (hdm : MeasurableEnvironment d)
    (hqm : MeasurableEnvironment q)
    (hd : ∀ u i, 0 ≤ d u i ∧ d u i ≤ 1/2)
    (hq : ∀ u i, 0 ≤ q u i ∧ q u i ≤ 1) :
    IsProbabilityMeasure (creationTrajectoryLaw μ pol d q hp hdm hqm hd hq) := by
  letI : ∀ n, IsMarkovKernel (creationStepKernel pol d q hp hdm hqm n) :=
    fun n => creationStepKernel_markov pol d q hp hdm hqm hd hq n
  letI : @IsProbabilityMeasure (ProcessCoord Seed 0) (processCoordSpace Seed 0) μ :=
    inferInstanceAs (IsProbabilityMeasure μ)
  unfold creationTrajectoryLaw
  exact Kernel.instIsProbabilityMeasureForallTrajMeasure
    (X := ProcessCoord Seed) (κ := creationStepKernel pol d q hp hdm hqm) (μ₀ := μ)

theorem coordPrefix_snoc {Seed : Type} (n : ℕ) (x : (n : ℕ) → ProcessCoord Seed n) :
    processPrefix (n+1) (coordTranscript x).2 =
      Fin.snoc (α := fun _ : Fin (n+1) => Option Bool)
        (coordPrefix (frestrictLe n x)) (x (n+1)) := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · exact (Fin.snoc_last (α := fun _ : Fin (n+1) => Option Bool)
      (x (n+1)) (coordPrefix (frestrictLe n x))).symm
  · exact (Fin.snoc_castSucc (α := fun _ : Fin (n+1) => Option Bool)
      (x (n+1)) (coordPrefix (frestrictLe n x)) j).symm

theorem creationTrajectoryLaw_integral_step {Seed : Type} [MeasurableSpace Seed]
    (μ : Measure Seed) [IsProbabilityMeasure μ]
    (pol : Seed → List Bool → Option ℕ) (d q : Seed → ℕ → ℝ)
    (hp : MeasurableCreationPolicy pol) (hdm : MeasurableEnvironment d)
    (hqm : MeasurableEnvironment q)
    (hd : ∀ u i, 0 ≤ d u i ∧ d u i ≤ 1/2)
    (hq : ∀ u i, 0 ≤ q u i ∧ q u i ≤ 1) (n : ℕ)
    (f : Seed → Prefix (n+1) → ℝ) (hf : ∀ w, Measurable (fun u => f u w))
    (C : ℝ) (hb : ∀ u w, |f u w| ≤ C) :
    (∫ x, f (x 0) (processPrefix (n+1) (coordTranscript x).2)
      ∂creationTrajectoryLaw μ pol d q hp hdm hqm hd hq) =
    ∫ x, ∑ o : Option Bool,
      creationTransition (pol (x 0)) (d (x 0)) (q (x 0))
        (processPrefix n (coordTranscript x).2) o *
      f (x 0) (Fin.snoc (processPrefix n (coordTranscript x).2) o)
      ∂creationTrajectoryLaw μ pol d q hp hdm hqm hd hq := by
  letI : ∀ k, IsMarkovKernel (creationStepKernel pol d q hp hdm hqm k) :=
    fun k => creationStepKernel_markov pol d q hp hdm hqm hd hq k
  letI : @IsProbabilityMeasure (ProcessCoord Seed 0) (processCoordSpace Seed 0) μ :=
    inferInstanceAs (IsProbabilityMeasure μ)
  let R := creationTrajectoryLaw μ pol d q hp hdm hqm hd hq
  let κ : (k : ℕ) → Kernel ((i : Finset.Iic k) → ProcessCoord Seed i) (Option Bool) :=
    fun k => creationStepKernel pol d q hp hdm hqm k
  letI : ∀ k, IsMarkovKernel (κ k) := fun k =>
    creationStepKernel_markov pol d q hp hdm hqm hd hq k
  letI : IsProbabilityMeasure R := creationTrajectoryLaw_probability μ pol d q hp hdm hqm hd hq
  let g : ((i : Finset.Iic n) → ProcessCoord Seed i) × Option Bool → ℝ :=
    fun z => f (coordSeed z.1) (Fin.snoc (coordPrefix z.1) z.2)
  have hfm : Measurable (fun z : Seed × Prefix (n+1) => f z.1 z.2) :=
    measurable_from_prod_countable_left hf
  have hsnoc : Measurable (fun z : ((i : Finset.Iic n) → ProcessCoord Seed i) × Option Bool =>
      (Fin.snoc (coordPrefix z.1) z.2 : Prefix (n+1))) :=
    (measurable_of_countable (fun z : Prefix n × Option Bool =>
      (Fin.snoc z.1 z.2 : Prefix (n+1)))).comp
      (((measurable_coordPrefix n).comp measurable_fst).prodMk measurable_snd)
  have hgm : Measurable g := hfm.comp
    (((measurable_coordSeed n).comp measurable_fst).prodMk hsnoc)
  have hgint : Integrable g ((R.map (frestrictLe n)) ⊗ₘ κ n) :=
    integrable_of_abs_bound _ g hgm C (fun z => hb _ _)
  have hstep : (R.map (frestrictLe n)) ⊗ₘ κ n =
      R.map (fun x => (frestrictLe n x, x (n+1))) :=
    Kernel.map_frestrictLe_trajMeasure_compProd_eq_map_trajMeasure
      (X := ProcessCoord Seed) (μ₀ := μ) (κ := creationStepKernel pol d q hp hdm hqm) (a := n)
  have hsum : Measurable (fun x : (i : Finset.Iic n) → ProcessCoord Seed i =>
      ∑ o : Option Bool, creationTransition (pol (coordSeed x)) (d (coordSeed x))
        (q (coordSeed x)) (coordPrefix x) o * f (coordSeed x) (Fin.snoc (coordPrefix x) o)) := by
    apply Finset.measurable_sum
    intro o ho
    have hcm : Measurable (fun z : Seed × Prefix n =>
        creationTransition (pol z.1) (d z.1) (q z.1) z.2 o) :=
      measurable_from_prod_countable_left
        (fun w => measurable_creationTransition pol hp d q hdm hqm w o)
    exact (hcm.comp ((measurable_coordSeed n).prodMk (measurable_coordPrefix n))).mul
      (hgm.comp (measurable_id.prodMk measurable_const))
  calc
    _ = ∫ z, g z ∂R.map (fun x => (frestrictLe n x, x (n+1))) := by
      rw [integral_map ((measurable_frestrictLe n).prodMk (measurable_pi_apply (n+1))).aemeasurable
        hgm.aestronglyMeasurable]
      apply integral_congr_ae
      filter_upwards [] with x
      simp only [g, coordPrefix_snoc]
      rfl
    _ = ∫ z, g z ∂((R.map (frestrictLe n)) ⊗ₘ κ n) := by
      exact congrArg (fun M : Measure (((i : Finset.Iic n) → ProcessCoord Seed i) × Option Bool) =>
        ∫ z, g z ∂M) hstep.symm
    _ = ∫ x, ∫ o, g (x,o) ∂κ n x ∂R.map (frestrictLe n) :=
      Measure.integral_compProd hgint
    _ = ∫ x, ∑ o : Option Bool, creationTransition (pol (coordSeed x)) (d (coordSeed x))
        (q (coordSeed x)) (coordPrefix x) o * f (coordSeed x) (Fin.snoc (coordPrefix x) o)
        ∂R.map (frestrictLe n) := by
      apply integral_congr_ae
      filter_upwards [] with x
      exact creationStepKernel_integral pol d q hp hdm hqm hd hq n x (fun o => g (x,o))
    _ = _ := by
      rw [integral_map (measurable_frestrictLe n).aemeasurable hsum.aestronglyMeasurable]
      rfl

end ThresholdHC.Tier6
