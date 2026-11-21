import ThresholdHC.HardCapNecessity.Rate
import ThresholdHC.PaperStatements.OneFlip

/-! Fresh-flip runs at the endpoint gap: the clipped sample mean of `N+1`
fresh flips, and a delayed run that buys `c+1` flips but reads only the first
`N+1`. Both have the same squared risk; the clipped mean has risk at most
`min(1/16, (1/4)/(N+1))` when `0 ≤ theta ≤ 1/4`. -/

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace ThresholdHC.HardCapNecessity
open ThresholdHC.Tier3 ThresholdHC.Tier6 ThresholdHC.ObservableSimulation ThresholdHC.HardBudget
open ThresholdHC.PaperStatements ThresholdHC.SharpRMS.LargeBudget

/-- `N+1` fresh flips and their sample mean. -/
def freshMean (N : ℕ) : AdaptiveEstimator Unit :=
  freshFlips N (fun j => 1/((N:ℝ)+1) * j + 0)

/-- `N+1` fresh flips and their sample mean clipped to `[0, 1/4]`. -/
def freshClip (N : ℕ) : AdaptiveEstimator Unit :=
  freshFlips N (fun j => clipEstimate (1/4) (1/((N:ℝ)+1) * j + 0))

/-- Buy `c+1` fresh flips, but return the clipped mean of the first `N+1`. -/
def delayedClip (N c : ℕ) : AdaptiveEstimator Unit :=
  { freshFlips c (fun _ => 0) with
    output := (freshClip N).output
    output_measurable := (freshClip N).output_measurable }

theorem freshFlips_output (N : ℕ) (out : ℕ → ℝ) (z : Unit × ProcessTape) :
    (freshFlips N out).output z = out (headsNat (processPrefix (N+1) z.2)) := rfl

theorem freshFlips_policy (N : ℕ) (r : Unit) :
    (freshFlips N (fun _ => 0)).policy r = stopAt (N+1) List.length := rfl

/-- A block of `n+m` reads begins with the block of its first `n` reads. -/
theorem readBlock_take (n m : ℕ) (p : Reader) (s : Table) :
    (readBlock (n+m) p s).1.take n = (readBlock n p s).1 := by
  induction n generalizing p s with
  | zero => simp [readBlock]
  | succ n ih =>
    rw [Nat.succ_add]
    simp only [readBlock, List.take_succ_cons, ih]

/-- The first `n` observations of a fresh run do not depend on its length `c ≥ n`. -/
theorem prefix_agree {n c : ℕ} (h : n ≤ c) (s : Table) :
    processPrefix n (populationPath (stopAt c List.length) s) =
      processPrefix n (populationPath (stopAt n List.length) s) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le h
  funext i
  simp only [processPrefix]
  rw [block_path, block_path, ← readBlock_take n m]
  exact (List.getElem?_take_of_lt i.isLt).symm

theorem clip_bounds (x : ℝ) : 0 ≤ clipEstimate (1/4) x ∧ clipEstimate (1/4) x ≤ 1/4 :=
  ⟨le_max_left _ _, max_le (by norm_num) (min_le_left _ _)⟩

/-- An estimator with outputs in `[0, 1/4]` has squared risk at most `1/16`
for every target in `[0, 1/4]`. -/
theorem risk_le_of_range {R : Type} [MeasurableSpace R] (μ : Measure Gap) [IsProbabilityMeasure μ]
    (A : AdaptiveEstimator R) (q : SignLaw) {θ : ℝ} (hθ : 0 ≤ θ ∧ θ ≤ 1/4)
    (hA : ∀ z, 0 ≤ A.output z ∧ A.output z ≤ 1/4) :
    squaredRisk (experimentLaw μ A q) (populationOutput A) θ ≤ ENNReal.ofReal (1/16) := by
  unfold squaredRisk
  calc (∫⁻ z, ENNReal.ofReal ((populationOutput A z - θ)^2) ∂experimentLaw μ A q)
      ≤ ∫⁻ _, ENNReal.ofReal (1/16) ∂experimentLaw μ A q := by
        apply lintegral_mono
        intro z
        apply ENNReal.ofReal_le_ofReal
        have h := hA (z.1.1, z.2)
        change (A.output (z.1.1, z.2) - θ)^2 ≤ 1/16
        nlinarith
    _ = ENNReal.ofReal (1/16) := by rw [lintegral_const, measure_univ, mul_one]

theorem clip_risk_le_mean (μ : Measure Gap) [IsProbabilityMeasure μ] (N : ℕ) (q : SignLaw)
    {θ : ℝ} (hθ : 0 ≤ θ ∧ θ ≤ 1/4) :
    squaredRisk (experimentLaw μ (freshClip N) q) (populationOutput (freshClip N)) θ ≤
      squaredRisk (experimentLaw μ (freshMean N) q) (populationOutput (freshMean N)) θ := by
  unfold squaredRisk
  change (∫⁻ z, loss θ (clipEstimate (1/4) (populationOutput (freshMean N) z))
      ∂experimentLaw μ (freshMean N) q) ≤ ∫⁻ z, loss θ (populationOutput (freshMean N) z)
      ∂experimentLaw μ (freshMean N) q
  exact lintegral_mono (fun z => clip_loss_le _ _ _ hθ)

theorem signMean_half (q : SignLaw) : signMean (Measure.dirac halfGap) q.val = q.val halfGap := by
  simp [signMean]

theorem mean_risk_half (N : ℕ) (q : SignLaw) (hθ : q.val halfGap ≤ 1/4) :
    squaredRisk (experimentLaw (Measure.dirac halfGap) (freshMean N) q)
        (populationOutput (freshMean N)) (q.val halfGap) ≤
      ENNReal.ofReal ((1/4) / ((N:ℝ)+1)) := by
  have h := (fresh_moments N (1/((N:ℝ)+1)) 0 halfGap q (q.val halfGap)).2.2
  unfold freshMean
  rw [h]
  apply ENNReal.ofReal_le_ofReal
  have hg : ((halfGap : Gap) : ℝ) = 1/2 := rfl
  have h0 := (q.property.2 halfGap).1
  set θ := q.val halfGap
  have hb : 1/2 + (2 * θ - 1) * (1/2 : ℝ) = θ := by ring
  rw [hg, hb]
  have hN : (0:ℝ) < (N:ℝ)+1 := by positivity
  have he : (1/((N:ℝ)+1) * (((N:ℝ)+1) * θ) + 0 - θ)^2 +
      (1/((N:ℝ)+1))^2 * ((N:ℝ)+1) * θ * (1 - θ) = θ * (1 - θ) / ((N:ℝ)+1) := by
    field_simp; ring
  rw [he]
  apply div_le_div_of_nonneg_right _ hN.le
  nlinarith

/-- The clipped mean of `N+1` fresh flips at the endpoint gap. -/
theorem clip_risk_half (N : ℕ) (q : SignLaw) (hθ : q.val halfGap ≤ 1/4) :
    squaredRisk (experimentLaw (Measure.dirac halfGap) (freshClip N) q)
        (populationOutput (freshClip N)) (q.val halfGap) ≤
      ENNReal.ofReal (min (1/16) ((1/4) / ((N:ℝ)+1))) := by
  have h0 := (q.property.2 halfGap).1
  rcases min_cases (1/16 : ℝ) ((1/4) / ((N:ℝ)+1)) with ⟨h, _⟩ | ⟨h, _⟩ <;> rw [h]
  · exact risk_le_of_range _ _ _ ⟨h0, hθ⟩ (fun z => clip_bounds _)
  · exact (clip_risk_le_mean _ N q ⟨h0, hθ⟩).trans (mean_risk_half N q hθ)

/-- The delayed run returns the same output as the short run on every table. -/
theorem delayed_output {N c : ℕ} (h : N ≤ c) (s : Table) :
    (delayedClip N c).output ((), populationPath ((delayedClip N c).policy ()) s) =
      (freshClip N).output ((), populationPath ((freshClip N).policy ()) s) := by
  change (freshClip N).output ((), populationPath (stopAt (c+1) List.length) s) =
    (freshClip N).output ((), populationPath (stopAt (N+1) List.length) s)
  unfold freshClip
  rw [freshFlips_output, freshFlips_output]
  dsimp only
  rw [prefix_agree (Nat.succ_le_succ h)]

theorem delayed_risk (μ : Measure Gap) [IsProbabilityMeasure μ] {N c : ℕ} (h : N ≤ c)
    (q : SignLaw) (θ : ℝ) :
    squaredRisk (experimentLaw μ (delayedClip N c) q) (populationOutput (delayedClip N c)) θ =
      squaredRisk (experimentLaw μ (freshClip N) q) (populationOutput (freshClip N)) θ := by
  rw [original_squaredRisk_simulation, original_squaredRisk_simulation]
  refine lintegral_congr (fun z => ?_)
  change ENNReal.ofReal (((delayedClip N c).output ((), populationPath ((delayedClip N c).policy ()) z.2) - θ)^2) =
    ENNReal.ofReal (((freshClip N).output ((), populationPath ((freshClip N).policy ()) z.2) - θ)^2)
  rw [delayed_output h]

theorem delayed_work (μ : Measure Gap) [IsProbabilityMeasure μ] (N c : ℕ) (q : SignLaw) :
    expectedWork μ (delayedClip N c) q ≤ ENNReal.ofReal ((c:ℝ)+1) :=
  fresh_budget μ c (fun _ => 0) q

theorem clip_work (μ : Measure Gap) [IsProbabilityMeasure μ] (N : ℕ) (q : SignLaw) :
    expectedWork μ (freshClip N) q ≤ ENNReal.ofReal ((N:ℝ)+1) :=
  fresh_budget μ N _ q

end ThresholdHC.HardCapNecessity
