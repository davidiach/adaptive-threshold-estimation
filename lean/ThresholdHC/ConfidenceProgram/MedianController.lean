import ThresholdHC.ConfidenceProgram.Blocks
import ThresholdHC.HardBudget.Inputs
import ThresholdHC.HardBudget.StageMoments
import ThresholdHC.Confidence.Median

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace ThresholdHC.ConfidenceProgram
open ThresholdHC.Tier3 ThresholdHC.Tier6 ThresholdHC.ObservableSimulation
open ThresholdHC.BlindUpper ThresholdHC.HardBudget ThresholdHC.Confidence

variable {R : Type} [MeasurableSpace R]

def medianReader (A : AdaptiveEstimator R) (r : ℕ → R) (i : ℕ) : Reader :=
  fun h => (A.policy (r i) h).getD 0

private theorem measurable_blockReader (A : AdaptiveEstimator R) (N k start : ℕ) (w : List Bool) :
    Measurable (fun r => blockReader N (medianReader A r) k start w) := by
  induction k generalizing start w with
  | zero => exact measurable_const
  | succ k ih =>
    by_cases h : w.length < N
    · simp only [blockReader,thenRead,ite_eq_left h,Function.comp_apply,medianReader]
      exact (measurable_of_countable (fun a : Option ℕ => Nat.pair start (a.getD 0))).comp
        ((measurable_to_countable' (A.policy_measurable w)).comp (measurable_pi_apply start))
    · simpa only [blockReader,thenRead,ite_eq_right_iff.mpr (fun h' => (h h').elim)] using ih (start+1) (w.drop N)

def cappedMedian (A : AdaptiveEstimator R) (m N : ℕ) (M : ℝ) : AdaptiveEstimator (ℕ → R) where
  randomLaw := Measure.infinitePi (fun _ : ℕ => A.randomLaw)
  probability := inferInstance
  policy r := stopAt ((2*m+1)*N) (blockReader N (medianReader A r) (2*m+1) 0)
  policy_measurable := by
    intro w a
    by_cases h : w.length < (2*m+1)*N
    · simp only [stopAt,ite_eq_left h]
      exact measurableSet_eq_fun ((measurable_of_countable some).comp
        (measurable_blockReader A N (2*m+1) 0 w)) measurable_const
    · simp [stopAt,h]
  output z := median m (fun i => (stageOutput A M (z.1 i.val)
    (blockAt N i.val (processHistory z.2 ((2*m+1)*N)))).getD (M/2))
  output_measurable := by
    apply measurable_median
    intro i
    have hm : Measurable (fun z : (ℕ → R) × List Bool =>
        (stageOutput A M (z.1 i.val) (blockAt N i.val z.2)).getD (M/2)) :=
      measurable_from_prod_countable_left (fun w => measurable_stage_getD A M (blockAt N i.val w)
        (fun u : ℕ → R => u i.val) (measurable_pi_apply _) (fun _ => M/2) measurable_const)
    exact hm.comp (measurable_fst.prodMk ((measurable_processHistory_fixed _).comp measurable_snd))

theorem cappedMedian_cap (A : AdaptiveEstimator R) (m N : ℕ) (M : ℝ) :
    PathwiseCap (cappedMedian A m N M) ((2*m+1)*N) := stopAt_pathwise_cap _ _ _ (fun _ => rfl)

def localValue (M : ℝ) (v : Outcome) : ℝ := if v.1 then M/2 else v.2

theorem measurable_localValue (M : ℝ) : Measurable (localValue M) :=
  Measurable.ite (measurableSet_eq_fun measurable_fst measurable_const) measurable_const measurable_snd

theorem stageResult_value (A : AdaptiveEstimator R) (N : ℕ) (M : ℝ) (r : R) (s : Table) :
    (stageResult A N M r s).getD (M/2) = localValue M (outcome A N M (r,s)) := by
  dsimp only [stageResult,localValue,outcome,observed]
  cases A.policy r (processHistory (populationPath (A.policy r) s) N) <;> rfl

/-- The estimator is blind to the hidden table. On every realization its
output is the median of the clipped, capped local runs in disjoint namespaces. -/
theorem cappedMedian_output (A : AdaptiveEstimator R) (m N : ℕ) (M : ℝ) (r : ℕ → R) (s : Table) :
    (cappedMedian A m N M).output (r,populationPath ((cappedMedian A m N M).policy r) s) =
      median m (fun i => localValue M (outcome A N M (stageInputs (r,s) i.val))) := by
  let p := medianReader A r
  let w := (readBlock ((2*m+1)*N) (blockReader N p (2*m+1) 0) s).1
  have hx := block_path ((2*m+1)*N) (blockReader N p (2*m+1) 0) s
  change populationPath ((cappedMedian A m N M).policy r) s = fun i => w[i]? at hx
  change median m (fun i => (stageOutput A M (r i.val) (blockAt N i.val (processHistory _ _))).getD _) = _
  rw [hx,← show w.length = (2*m+1)*N from readBlock_length _ _ _,processHistory_word]
  congr 1
  funext i
  have hb := observed_block N p s (2*m+1) 0 i.val i.isLt
  simp only [Nat.zero_add] at hb
  change blockAt N i.val w = _ at hb
  rw [hb,show stageOutput A M (r i.val) (readBlock N (p i.val) (s ∘ Nat.pair i.val)).1 =
    stageResult A N M (r i.val) (s ∘ Nat.pair i.val) from stageOutput_correct _ _ _ _ _,stageResult_value]
  rfl

end ThresholdHC.ConfidenceProgram
