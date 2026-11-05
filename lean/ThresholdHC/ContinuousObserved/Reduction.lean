import ThresholdHC.ContinuousObserved.Tape
import ThresholdHC.ContinuousObserved.Noise

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace ThresholdHC.ContinuousObserved
open ThresholdHC ThresholdHC.Tier3 ThresholdHC.Tier6 ThresholdHC.ObservedState
open ThresholdHC.CriticalEntropy

local instance (N : ℕ) : MeasurableSpace (Option (Fin N)) := ⊤

/-- A known gap map with a larger fixed magnitude for each persistent sign cell. -/
structure QueryDesign (N : ℕ) where
  cap : Fin N → Gap
  gap : unitInterval → Gap
  cell : unitInterval → Fin N
  gap_measurable : Measurable gap
  cell_measurable : Measurable cell
  bound : ∀ u, (gap u : ℝ) ≤ cap (cell u)

def perturb {N : ℕ} {R : Type} [MeasurableSpace R] (D : QueryDesign N) (A : StateEstimator R)
    (z : R × (ℕ → ℝ)) (xs : List Bool) (b : Bool) : Bool :=
  Bool.xor b (uniformCoinFlip
    (noiseRate (D.cap (D.cell (A.query z.1 xs))) (D.gap (A.query z.1 xs)) (D.bound _))
    (z.2 xs.length))

theorem measurable_perturb {N : ℕ} {R : Type} [MeasurableSpace R]
    (D : QueryDesign N) (A : StateEstimator R) (xs : List Bool) (b : Bool) :
    Measurable (fun z : R × (ℕ → ℝ) => perturb D A z xs b) := by
  have hu : Measurable (fun z : R × (ℕ → ℝ) => A.query z.1 xs) :=
    (A.query_measurable xs).comp measurable_fst
  have hn := measurable_noiseRate (fun u => D.cap (D.cell u)) D.gap
    ((measurable_of_countable D.cap).comp D.cell_measurable) D.gap_measurable D.bound
  exact (measurable_of_countable (fun c : Bool => Bool.xor b c)).comp
    (measurable_uniformCoinFlip.comp ((hn.comp hu).prodMk
      ((measurable_pi_apply xs.length).comp measurable_snd)))

def decoded {N : ℕ} {R : Type} [MeasurableSpace R] (D : QueryDesign N) (A : StateEstimator R)
    (z : (R × (ℕ → ℝ)) × ProcessTape) : R × ProcessTape :=
  (z.1.1,decodeTape (perturb D A z.1) z.2)

theorem measurable_decoded {N : ℕ} {R : Type} [MeasurableSpace R]
    (D : QueryDesign N) (A : StateEstimator R) : Measurable (decoded D A) :=
  measurable_fst.fst.prodMk (measurable_decodeTape (perturb D A) (measurable_perturb D A))

/-- Simulate an arbitrary selected-state policy using one larger-gap
observation per query and an independent uniform tape in the private seed. -/
def reduction {N : ℕ} {R : Type} [MeasurableSpace R] (D : QueryDesign N) (A : StateEstimator R) :
    Estimator N (R × (ℕ → ℝ)) where
  randomLaw := A.randomLaw.prod uniformTapeMeasure
  probability := inferInstance
  policy := fun z xs =>
    let ys := decode (perturb D A z) xs
    if A.continues z.1 ys then some (D.cell (A.query z.1 ys)) else none
  policy_measurable := by
    intro xs a
    have hy := measurable_decode (perturb D A) (measurable_perturb D A) xs
    have hq : Measurable (fun z : R × List Bool => A.query z.1 z.2) :=
      measurable_from_prod_countable_left A.query_measurable
    have ht : Measurable (fun z : R × List Bool => A.continues z.1 z.2) :=
      measurable_from_prod_countable_left A.continues_measurable
    have hp : Measurable (fun z : R × (ℕ → ℝ) =>
        if A.continues z.1 (decode (perturb D A z) xs)
          then some (D.cell (A.query z.1 (decode (perturb D A z) xs))) else none) :=
      Measurable.ite (measurableSet_eq_fun (ht.comp (measurable_fst.prodMk hy)) measurable_const)
        ((measurable_of_countable (fun i : Fin N => some i)).comp
          (D.cell_measurable.comp (hq.comp (measurable_fst.prodMk hy)))) measurable_const
    exact measurableSet_eq_fun hp measurable_const
  output := fun z => A.output (decoded D A z)
  output_measurable := A.output_measurable.comp (measurable_decoded D A)

def queryLaw {N : ℕ} {R : Type} [MeasurableSpace R] (D : QueryDesign N) (A : StateEstimator R)
    (s : Fin N → Bool) : Measure (R × ProcessTape) :=
  (modelLaw (reduction D A) D.cap s).map (decoded D A)

instance queryLaw_probability {N : ℕ} {R : Type} [MeasurableSpace R]
    (D : QueryDesign N) (A : StateEstimator R) (s : Fin N → Bool) :
    IsProbabilityMeasure (queryLaw D A s) :=
  (Measure.isProbabilityMeasure_map_iff (measurable_decoded D A).aemeasurable).mpr inferInstance

theorem reduction_work {N : ℕ} {R : Type} [MeasurableSpace R]
    (D : QueryDesign N) (A : StateEstimator R) (s : Fin N → Bool) :
    (∫⁻ z, totalProcessWork z.2 ∂queryLaw D A s) =
      ThresholdHC.ObservedState.expectedWork (reduction D A) D.cap s := by
  have hm := measurable_totalProcessWork (Prod.snd : R × ProcessTape → ProcessTape)
    (fun n b => measurableSet_eq_fun ((measurable_pi_apply n).comp measurable_snd) measurable_const)
  rw [queryLaw,lintegral_map hm (measurable_decoded D A)]
  apply lintegral_congr
  intro z
  exact decodeTape_work _ _

theorem reduction_error {N : ℕ} {R : Type} [MeasurableSpace R]
    (D : QueryDesign N) (A : StateEstimator R) (s : Fin N → Bool) (r θ : ℝ) :
    queryLaw D A s {z | r < |A.output z - θ|} =
      modelLaw (reduction D A) D.cap s {z | r < |(reduction D A).output z - θ|} := by
  rw [queryLaw,Measure.map_apply (measurable_decoded D A)
    (measurableSet_lt measurable_const ((A.output_measurable.sub_const θ).abs))]
  rfl

end ThresholdHC.ContinuousObserved
