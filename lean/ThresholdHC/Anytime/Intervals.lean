import ThresholdHC.HardBudget.Controller

noncomputable section
open MeasureTheory
namespace ThresholdHC.Anytime
open ThresholdHC.Tier3 ThresholdHC.Tier6 ThresholdHC.HardBudget ThresholdHC.BlindUpper ThresholdHC.ObservableSimulation

def intersectBall (I : ℝ × ℝ) (c r : ℝ) : ℝ × ℝ := (max I.1 (c-r),min I.2 (c+r))

variable {R : ℕ → Type} [∀ j, MeasurableSpace (R j)]

def historyInterval (base : ∀ j, AdaptiveEstimator (R j)) (M : ℝ) (radius : ℕ → ℝ) (r : ∀ j, R j) :
    ℕ → List Bool → ℝ × ℝ
  | 0, _ => (0,M)
  | j+1, xs => intersectBall (historyInterval base M radius r j (xs.take (paid j)))
      ((stageOutput (base j) M (r j) (xs.drop (paid j))).getD (M/2)) (radius j)

def tableInterval (base : ∀ j, AdaptiveEstimator (R j)) (M : ℝ) (radius : ℕ → ℝ)
    (r : ∀ j, R j) (s : Table) : ℕ → ℝ × ℝ
  | 0 => (0,M)
  | j+1 => intersectBall (tableInterval base M radius r s j)
      ((stageResult (base j) (stageCap j) M (r j) (s ∘ Nat.pair j)).getD (M/2)) (radius j)

theorem measurable_historyInterval (base : ∀ j, AdaptiveEstimator (R j)) (M : ℝ) (radius : ℕ → ℝ)
    (k : ℕ) (xs : List Bool) : Measurable (fun r => historyInterval base M radius r k xs) := by
  induction k generalizing xs with
  | zero => exact measurable_const
  | succ j ih =>
    have hp := ih (xs.take (paid j))
    have hc := measurable_stage_getD (base j) M (xs.drop (paid j))
      (fun r : ∀ i, R i => r j) (measurable_pi_apply j) (fun _ => M/2) measurable_const
    exact (hp.fst.max (hc.sub_const (radius j))).prodMk (hp.snd.min (hc.add_const (radius j)))

/-- Both endpoints use exactly the same purchase policy and private seed.
Only their scalar, stopped-history output maps differ. -/
def endpointEstimator (base : ∀ j, AdaptiveEstimator (R j)) (M : ℝ) (radius : ℕ → ℝ) (k : ℕ) (upper : Bool) :
    AdaptiveEstimator (∀ j, R j) :=
  { estimator base M k with
    output := fun z => let I := historyInterval base M radius z.1 k (processHistory z.2 (paid k)); if upper then I.2 else I.1
    output_measurable := by
      have hm : Measurable (fun z : (∀ j, R j) × List Bool => historyInterval base M radius z.1 k z.2) :=
        measurable_from_prod_countable_left (measurable_historyInterval base M radius k)
      have ht := hm.comp (measurable_fst.prodMk ((measurable_processHistory_fixed (paid k)).comp measurable_snd))
      cases upper
      · exact ht.fst
      · exact ht.snd }

theorem endpoint_cap (base : ∀ j, AdaptiveEstimator (R j)) (M : ℝ) (radius : ℕ → ℝ) (k : ℕ) (upper : Bool) :
    PathwiseCap (endpointEstimator base M radius k upper) (paid k) := estimator_cap base M k

theorem interval_readBlock (base : ∀ j, AdaptiveEstimator (R j)) (M : ℝ) (radius : ℕ → ℝ)
    (r : ∀ j, R j) (s : Table) (k : ℕ) :
    historyInterval base M radius r k (readBlock (paid k) (planReader base r k) s).1 =
      tableInterval base M radius r s k := by
  induction k with
  | zero => rfl
  | succ j ih =>
    let p := planReader base r j
    let v := readBlock (paid j) p s
    let q := fun h => ((base j).policy (r j) h).getD 0
    let stage := readBlock (stageCap j) (Nat.pair j ∘ q) v.2
    have hword : (readBlock (paid (j+1)) (planReader base r (j+1)) s).1 = v.1++stage.1 :=
      congrArg Prod.fst (readBlock_append (paid j) (stageCap j) p (Nat.pair j ∘ q) s)
    have hlen : v.1.length = paid j := readBlock_length _ _ _
    have hcut := readBlock_relabel (stageCap j) (Nat.pair j) (fun _ _ h => (Nat.pair_eq_pair.mp h).2) q v.2
    have he : v.2 ∘ Nat.pair j = s ∘ Nat.pair j := funext (next_stage_fresh base r j s)
    rw [he] at hcut
    change stage.1 = _ at hcut
    rw [historyInterval,hword,← hlen,List.take_left,List.drop_left,hcut]
    rw [show historyInterval base M radius r j v.1 = tableInterval base M radius r s j from ih,
      stageOutput_correct (base j) M (stageCap j) (r j) (s ∘ Nat.pair j)]
    rfl

theorem endpoint_output (base : ∀ j, AdaptiveEstimator (R j)) (M : ℝ) (radius : ℕ → ℝ)
    (k : ℕ) (upper : Bool) (r : ∀ j, R j) (s : Table) :
    (endpointEstimator base M radius k upper).output
      (r,populationPath ((endpointEstimator base M radius k upper).policy r) s) =
      if upper then (tableInterval base M radius r s k).2 else (tableInterval base M radius r s k).1 := by
  let w := (readBlock (paid k) (planReader base r k) s).1
  have hp := block_path (paid k) (planReader base r k) s
  change populationPath ((endpointEstimator base M radius k upper).policy r) s = fun i => w[i]? at hp
  change (if upper then (historyInterval base M radius r k (processHistory _ (paid k))).2
    else (historyInterval base M radius r k (processHistory _ (paid k))).1) = _
  rw [hp,← show w.length = paid k from readBlock_length _ _ _,processHistory_word,
    interval_readBlock base M radius r s k]

end ThresholdHC.Anytime
