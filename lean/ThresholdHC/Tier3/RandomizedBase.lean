import ThresholdHC.Tier3.RandomizedModel
import ThresholdHC.Proofs.Tier2.Information

noncomputable section
namespace ThresholdHC.Tier3
open MeasureTheory Real
open ThresholdHC.Proofs

local instance (m : ℕ) : MeasurableSpace (Option (Fin m)) := ⊤

abbrev PolicyCode (m n : ℕ) := Prefix n → Fin n → Option (Fin m)

def policyCode {U : Type} {m n : ℕ} (pol : U → List Bool → Option (Fin m))
    (u : U) : PolicyCode m n := fun ω t => pol u (histBefore ω t)

def codeLaw {m n : ℕ} (c : PolicyCode m n) (d q : Fin m → ℝ) (ω : Prefix n) : ℝ :=
  ∑ s : Fin m → Bool, (∏ i, if s i then q i else 1-q i) *
    ∏ t : Fin n,
      match c ω t, ω t with
      | none, none => 1
      | some i, some true => 1/2 + (if s i then d i else -d i)
      | some i, some false => 1-(1/2 + (if s i then d i else -d i))
      | _, _ => 0

theorem transcriptLaw_eq_codeLaw {U : Type} {m n : ℕ}
    (pol : U → List Bool → Option (Fin m)) (d q : Fin m → ℝ) (u : U) (ω : Prefix n) :
    transcriptLaw (pol u) d q ω = codeLaw (policyCode pol u) d q ω := rfl

theorem measurable_policyCode {U : Type} [MeasurableSpace U] {m n : ℕ}
    (pol : U → List Bool → Option (Fin m)) (hp : MeasurablePolicy pol) :
    Measurable (policyCode (n:=n) pol) := by
  apply Measurable.of_eval
  intro ω
  apply Measurable.of_eval
  intro t
  exact measurable_to_countable' (fun action => hp (histBefore ω t) action)

theorem integrable_finite_comp {U B : Type} [MeasurableSpace U] [MeasurableSpace B]
    [Finite B] [MeasurableSingletonClass B] (μ : Measure U) [IsFiniteMeasure μ]
    (g : U → B) (hg : Measurable g) (f : B → ℝ) :
    Integrable (fun u => f (g u)) μ := by
  have hi : Integrable f (μ.map g) := Integrable.of_finite
  exact (integrable_map_measure (measurable_of_countable f).aestronglyMeasurable
    hg.aemeasurable).mp hi

theorem integrable_policy_function {U : Type} [MeasurableSpace U] {m n : ℕ}
    (μ : Measure U) [IsFiniteMeasure μ] (pol : U → List Bool → Option (Fin m))
    (hp : MeasurablePolicy pol) (F : PolicyCode m n → ℝ) :
    Integrable (fun u => F (policyCode pol u)) μ :=
  integrable_finite_comp μ _ (measurable_policyCode pol hp) F

theorem integrable_transcriptLaw {U : Type} [MeasurableSpace U] {m n : ℕ}
    (μ : Measure U) [IsFiniteMeasure μ] (pol : U → List Bool → Option (Fin m))
    (hp : MeasurablePolicy pol) (d q : Fin m → ℝ) (ω : Prefix n) :
    Integrable (fun u => transcriptLaw (pol u) d q ω) μ := by
  exact integrable_policy_function μ pol hp (fun c => codeLaw c d q ω)

theorem integrable_conditional_kl {U : Type} [MeasurableSpace U] {m n : ℕ}
    (μ : Measure U) [IsFiniteMeasure μ] (pol : U → List Bool → Option (Fin m))
    (hp : MeasurablePolicy pol) (d q r : Fin m → ℝ) :
    Integrable (fun u => klFT (transcriptLaw (n:=n) (pol u) d q)
      (transcriptLaw (n:=n) (pol u) d r)) μ :=
  integrable_policy_function μ pol hp (fun c => klFT (codeLaw c d q) (codeLaw c d r))

theorem integrable_conditional_work {U : Type} [MeasurableSpace U] {m n : ℕ}
    (μ : Measure U) [IsFiniteMeasure μ] (pol : U → List Bool → Option (Fin m))
    (hp : MeasurablePolicy pol) (d q : Fin m → ℝ) :
    Integrable (fun u => ∑ ω : Prefix n, transcriptLaw (pol u) d q ω * workOf ω) μ :=
  integrable_policy_function μ pol hp (fun c => ∑ ω, codeLaw c d q ω * workOf ω)

theorem randomized_law_total : RandomizedTotalStatement := by
  intro U _ μ _ m n pol d q hp hd hq
  constructor
  · intro ω
    exact integral_nonneg (fun u => (transcript_law_total m n (pol u) d q hd hq).1 ω)
  · unfold randomizedLaw
    rw [← integral_finsetSum _ (fun ω _ => integrable_transcriptLaw μ pol hp d q ω)]
    simp_rw [(transcript_law_total m n _ d q hd hq).2]
    simp

theorem randomized_information_bound : RandomizedInformationStatement := by
  intro U _ μ _ m n pol d η h hp hh hd hη hdη
  have hi := integral_mono (integrable_conditional_kl (n:=n) μ pol hp d _ _)
    ((integrable_conditional_work (n:=n) μ pol hp d _).const_mul ((128/225)*h^2))
    (fun u => stopped_transcript_kl m n (pol u) d η h hh hd hη hdη)
  simpa only [integral_const_mul, conditionalInformation, randomizedWork] using hi

end ThresholdHC.Tier3
