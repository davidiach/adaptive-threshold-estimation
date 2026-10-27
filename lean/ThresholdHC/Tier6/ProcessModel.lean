import ThresholdHC.Tier6.ProcessWeights

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace ThresholdHC.Tier6
open ThresholdHC.Tier3 ThresholdHC.Tier5

/-- Coordinate zero stores the common seed; subsequent coordinates are observations. -/
def ProcessCoord (Seed : Type) : ℕ → Type
  | 0 => Seed
  | _ + 1 => Option Bool

instance processCoordSpace (Seed : Type) [MeasurableSpace Seed] (n : ℕ) :
    MeasurableSpace (ProcessCoord Seed n) := by
  cases n with
  | zero => exact inferInstanceAs (MeasurableSpace Seed)
  | succ n => exact inferInstanceAs (MeasurableSpace (Option Bool))

def coordSeed {Seed : Type} {n : ℕ} (x : (i : Finset.Iic n) → ProcessCoord Seed i) : Seed :=
  x ⟨0, Finset.mem_Iic.mpr (Nat.zero_le n)⟩

def coordPrefix {Seed : Type} {n : ℕ} (x : (i : Finset.Iic n) → ProcessCoord Seed i) : Prefix n :=
  fun i => x ⟨i.val+1, Finset.mem_Iic.mpr i.isLt⟩

theorem measurable_coordSeed {Seed : Type} [MeasurableSpace Seed] (n : ℕ) :
    Measurable (coordSeed (Seed := Seed) (n := n)) := measurable_pi_apply _

theorem measurable_coordPrefix {Seed : Type} [MeasurableSpace Seed] (n : ℕ) :
    Measurable (coordPrefix (Seed := Seed) (n := n)) := by
  apply Measurable.of_eval
  intro i
  exact measurable_pi_apply _

def creationStepKernel {Seed : Type} [MeasurableSpace Seed]
    (pol : Seed → List Bool → Option ℕ) (d q : Seed → ℕ → ℝ)
    (hp : MeasurableCreationPolicy pol) (hdm : MeasurableEnvironment d)
    (hqm : MeasurableEnvironment q) (n : ℕ) :
    Kernel ((i : Finset.Iic n) → ProcessCoord Seed i) (ProcessCoord Seed (n+1)) :=
  (creationNextKernel pol d q hp hdm hqm n).comap
    (fun x => (coordSeed (Seed := Seed) (n := n) x, coordPrefix (Seed := Seed) (n := n) x))
    ((measurable_coordSeed (Seed := Seed) n).prodMk (measurable_coordPrefix (Seed := Seed) n))

theorem creationStepKernel_markov {Seed : Type} [MeasurableSpace Seed]
    (pol : Seed → List Bool → Option ℕ) (d q : Seed → ℕ → ℝ)
    (hp : MeasurableCreationPolicy pol) (hdm : MeasurableEnvironment d)
    (hqm : MeasurableEnvironment q)
    (hd : ∀ u i, 0 ≤ d u i ∧ d u i ≤ 1/2)
    (hq : ∀ u i, 0 ≤ q u i ∧ q u i ≤ 1) (n : ℕ) :
    IsMarkovKernel (creationStepKernel pol d q hp hdm hqm n) := by
  letI := creationNextKernel_markov pol d q hp hdm hqm hd hq n
  exact Kernel.IsMarkovKernel.comap (creationNextKernel pol d q hp hdm hqm n)
    ((measurable_coordSeed (Seed := Seed) n).prodMk (measurable_coordPrefix (Seed := Seed) n))

def coordTranscript {Seed : Type} (x : (n : ℕ) → ProcessCoord Seed n) : Seed × ProcessTape :=
  (x 0, fun n => x (n+1))

theorem measurable_coordTranscript {Seed : Type} [MeasurableSpace Seed] :
    Measurable (coordTranscript (Seed := Seed)) := by
  apply Measurable.prodMk (measurable_pi_apply 0)
  exact Measurable.of_eval (fun n => measurable_pi_apply (n+1))

/-- Canonical infinite adaptive experiment, built by Ionescu--Tulcea. -/
def creationProcessLaw {Seed : Type} [MeasurableSpace Seed]
    (μ : Measure Seed) (pol : Seed → List Bool → Option ℕ) (d q : Seed → ℕ → ℝ)
    (hp : MeasurableCreationPolicy pol) (hdm : MeasurableEnvironment d)
    (hqm : MeasurableEnvironment q)
    (hd : ∀ u i, 0 ≤ d u i ∧ d u i ≤ 1/2)
    (hq : ∀ u i, 0 ≤ q u i ∧ q u i ≤ 1) : Measure (Seed × ProcessTape) := by
  letI : ∀ n, IsMarkovKernel (creationStepKernel pol d q hp hdm hqm n) :=
    fun n => creationStepKernel_markov pol d q hp hdm hqm hd hq n
  exact (Kernel.trajMeasure (X := ProcessCoord Seed) μ
    (creationStepKernel pol d q hp hdm hqm)).map (coordTranscript (Seed := Seed))

instance creationProcessLaw_probability {Seed : Type} [MeasurableSpace Seed]
    (μ : Measure Seed) [IsProbabilityMeasure μ]
    (pol : Seed → List Bool → Option ℕ) (d q : Seed → ℕ → ℝ)
    (hp : MeasurableCreationPolicy pol) (hdm : MeasurableEnvironment d)
    (hqm : MeasurableEnvironment q)
    (hd : ∀ u i, 0 ≤ d u i ∧ d u i ≤ 1/2)
    (hq : ∀ u i, 0 ≤ q u i ∧ q u i ≤ 1) :
    IsProbabilityMeasure (creationProcessLaw μ pol d q hp hdm hqm hd hq) := by
  letI : ∀ n, IsMarkovKernel (creationStepKernel pol d q hp hdm hqm n) :=
    fun n => creationStepKernel_markov pol d q hp hdm hqm hd hq n
  letI : @IsProbabilityMeasure (ProcessCoord Seed 0) (processCoordSpace Seed 0) μ :=
    inferInstanceAs (IsProbabilityMeasure μ)
  unfold creationProcessLaw
  apply (Measure.isProbabilityMeasure_map_iff
    (measurable_coordTranscript (Seed := Seed)).aemeasurable).2
  exact Kernel.instIsProbabilityMeasureForallTrajMeasure
    (X := ProcessCoord Seed) (κ := creationStepKernel pol d q hp hdm hqm) (μ₀ := μ)

end ThresholdHC.Tier6
