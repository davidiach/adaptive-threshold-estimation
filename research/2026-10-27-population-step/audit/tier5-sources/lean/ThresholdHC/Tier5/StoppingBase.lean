import ThresholdHC.Tier5.Model
import ThresholdHC.Tier5.CreationBase
import ThresholdHC.Tier3.StoppingBase
import ThresholdHC.Tier4.StoppedReconstruction

noncomputable section
open MeasureTheory Filter
open scoped ENNReal
namespace ThresholdHC.Tier5
open ThresholdHC.Tier3 ThresholdHC.Tier4

local instance stoppingOptionFinSpace : MeasurableSpace (Option (Fin 1)) := ⊤

theorem measurable_creation_policy {Seed : Type} [MeasurableSpace Seed]
    (pol : Seed → List Bool → Option ℕ) (hp : MeasurableCreationPolicy pol) (xs : List Bool) :
    Measurable (fun u => pol u xs) := measurable_to_countable' (hp xs)

theorem capPolicy_isSome_at {n : ℕ} (pol : List Bool → Option ℕ)
    (w : Prefix n) (t : Fin n) :
    (capPolicy (coinCap n pol) pol (histBefore w t)).isSome =
      (pol (histBefore w t)).isSome := by
  cases he : pol (histBefore w t) with
  | none => simp [capPolicy, he]
  | some i => simp [capPolicy, he, selected_lt_coinCap pol w t i he]

theorem creationLaw_zero_of_invalid {n : ℕ} (pol : List Bool → Option ℕ)
    (d q : ℕ → ℝ) (w : Prefix n) (t : Fin n)
    (h : (w t).isSome ≠ (pol (histBefore w t)).isSome) : creationLaw pol d q w = 0 := by
  unfold creationLaw
  apply transcriptLaw_zero_of_invalid _ _ _ w t
  rwa [capPolicy_isSome_at]

theorem realized_creation_valid_step {Seed Ω : Type} [MeasurableSpace Seed] [MeasurableSpace Ω]
    (μ : Measure Seed) (ν : Measure Ω) [IsProbabilityMeasure ν]
    (seed : Ω → Seed) (tape : Ω → ProcessTape) (pol : Seed → List Bool → Option ℕ)
    (d q : Seed → ℕ → ℝ) (hs : Measurable seed)
    (htape : ∀ n b, MeasurableSet {ω | tape ω n = b}) (hp : MeasurableCreationPolicy pol)
    (hr : RealizesCreationPrefixes μ ν seed tape pol d q) (n : ℕ) :
    ∀ᵐ ω ∂ν, (tape ω n).isSome = (pol (seed ω) (processHistory (tape ω) n)).isSome := by
  classical
  let f : Seed → (Fin (n+1) → Option Bool) → ℝ := fun u w =>
    if (w (Fin.last n)).isSome = (pol u (histBefore w (Fin.last n))).isSome then 0 else 1
  have hf : ∀ w, Measurable (fun u => f u w) := by
    intro w
    have hm := (measurable_of_countable _ : Measurable (@Option.isSome ℕ)).comp
      (measurable_creation_policy pol hp (histBefore w (Fin.last n)))
    exact measurable_const.ite (measurableSet_eq_fun measurable_const hm) measurable_const
  have hbound : ∃ C : ℝ, ∀ u w, |f u w| ≤ C := by
    refine ⟨1, ?_⟩
    intro u w
    dsimp [f]
    split_ifs <;> norm_num
  have hz : ∀ u, (∑ w, creationLaw (pol u) (d u) (q u) w * f u w) = 0 := by
    intro u
    apply Finset.sum_eq_zero
    intro w hw
    dsimp [f]
    split_ifs with h
    · simp
    · rw [creationLaw_zero_of_invalid (pol u) (d u) (q u) w (Fin.last n) h, zero_mul]
  have heq := hr (n+1) f hf hbound
  simp_rw [hz] at heq
  simp only [integral_zero] at heq
  let bad : Set Ω := {ω | (tape ω n).isSome ≠ (pol (seed ω) (processHistory (tape ω) n)).isSome}
  have hm : MeasurableSet bad := by
    have ha := (measurable_of_countable _ : Measurable (@Option.isSome Bool)).comp
      (measurable_to_countable' (htape n))
    have hb := (measurable_of_countable _ : Measurable (@Option.isSome ℕ)).comp
      (measurable_prefix_function seed tape hs htape n
        (fun u w => pol u (Proofs.fullHist w))
        (fun w => measurable_creation_policy pol hp (Proofs.fullHist w)))
    exact (measurableSet_eq_fun ha hb).compl
  have heq' : ν.real bad = 0 := by
    have hfun : (fun ω => f (seed ω) (processPrefix (n+1) (tape ω))) =
        bad.indicator (fun _ => (1:ℝ)) := by
      funext ω
      simp only [f, processPrefix, Fin.val_last, histBefore_processPrefix_last,
        Set.indicator, bad, Set.mem_ofPred_eq]
      split_ifs <;> simp_all
    rw [hfun, integral_indicator_const 1 hm] at heq
    simpa using heq
  exact (ae_iff).2 ((measureReal_eq_zero_iff).mp heq')

theorem creation_stops : CreationStopsStatement := by
  intro Seed Ω _ _ μ ν _ _ seed tape pol d q hs htape hp hr hfin
  have hv : ∀ᵐ ω ∂ν, ∀ n, (tape ω n).isSome =
      (pol (seed ω) (processHistory (tape ω) n)).isSome :=
    ae_all_iff.2 (fun n => realized_creation_valid_step μ ν seed tape pol d q hs htape hp hr n)
  have hfinite := ae_lt_top (measurable_totalProcessWork tape htape) hfin.ne
  filter_upwards [hv, hfinite] with ω hvalid hwork
  by_contra hn
  push Not at hn
  have hsome (n : ℕ) : (tape ω n).isSome = true := by
    rw [hvalid n]
    exact Option.isSome_iff_ne_none.mpr (hn n)
  have hcount (n : ℕ) : workOf (processPrefix n (tape ω)) = n := by
    simp [workOf, processPrefix, hsome]
  obtain ⟨n, hnlarge⟩ := exists_nat_gt (totalProcessWork (tape ω)).toReal
  have hle : ENNReal.ofReal (n : ℝ) ≤ totalProcessWork (tape ω) := by
    rw [← hcount n]
    exact le_iSup (fun k => ENNReal.ofReal (workOf (processPrefix k (tape ω)))) n
  have := ENNReal.toReal_mono hwork.ne hle
  simpa using (not_le.mpr hnlarge) (by simpa using this)


end ThresholdHC.Tier5
