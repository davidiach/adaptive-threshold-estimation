import ThresholdHC.ArbitraryLawController.Coverage
import ThresholdHC.ArbitraryLawController.ZeroScale
import ThresholdHC.ArbitraryLawController.Onset
import ThresholdHC.ArbitraryLawAdaptation.LearnedOracle
import ThresholdHC.Anytime.Width

noncomputable section
set_option autoImplicit false
open MeasureTheory Real
open scoped ENNReal
namespace ThresholdHC.ArbitraryLawController
open ThresholdHC.Tier6 ThresholdHC.RareAboveTwo ThresholdHC.HardBudget
open ThresholdHC.ArbitraryLawAdaptation ThresholdHC.RobustContinuation
open ThresholdHC.ObservableSimulation ThresholdHC.KnownLawPlanner

def radiusCoefficient : ℝ := 6 * plannedCoefficient 28000

theorem radiusCoefficient_pos : 0 < radiusCoefficient := by
  have := plannedCoefficient_ge_one
  unfold radiusCoefficient
  linarith

theorem continuation_radius_le {δ : ℝ} (hd : 0 < δ) (hu : δ ≤ 1/4)
    (s : ℕ) (hJ : 1 ≤ depth δ s) (α : Measure ℝ) (ρ : ℝ) :
    medianRadius α ρ (remaining δ s) (4 * pilotGroups δ s (depth δ s)) ≤
      4 * radiusCoefficient * (zeroSelection α ρ ((4 : ℝ) ^ depth δ s)).toReal := by
  let N : ℝ := 4 ^ depth δ s
  have hN : 0 < N := by dsimp [N]; positivity
  have hb := continuation_base_ge hd hu s hJ
  have hm := zeroSelection_antitone α ρ (by positivity : 0 < N / 16) hb
  have hs := zeroSelection_budget_scale α ρ (by positivity : 0 < N / 16)
    (by dsimp [N]; nlinarith [hN] : N / 16 ≤ N)
  have he : Real.sqrt (N / (N / 16)) = 4 := by
    rw [show N / (N / 16) = 16 by field_simp]
    norm_num
  rw [he] at hs
  have ht := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
    (finite_zeroSelection α ρ N)) (hm.trans hs)
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 4)] at ht
  have hr := medianRadius_le α ρ (remaining δ s) (4 * pilotGroups δ s (depth δ s))
  change _ ≤ 4 * radiusCoefficient * (zeroSelection α ρ N).toReal
  change _ ≤ radiusCoefficient * _ at hr
  nlinarith [radiusCoefficient_pos]

theorem paidMedianStage_table_radius (ρ B : ℝ) (m J k : ℕ)
    (r : MedianSeed ρ B m) (t : Table) :
    let S := paidMedianStage ρ B m J k
    Anytime.halfWidth (S.tableInterval r t) =
      medianRadius (S.learnedLaw (readBlock S.pilotCost S.pilot (t ∘ Nat.pair 0)).1) ρ B m := by
  dsimp only
  unfold Anytime.halfWidth
  let S := paidMedianStage ρ B m J k
  let α := S.learnedLaw (readBlock S.pilotCost S.pilot (t ∘ Nat.pair 0)).1
  let w := (readBlock S.continuationCost (S.continuation α r) (t ∘ Nat.pair 1)).1
  have he := medianStage_radius ρ B m α r w
  change ((paidMedianStage ρ B m J k).tableInterval r t).2 -
    ((paidMedianStage ρ B m J k).tableInterval r t).1 = _ at he
  rw [he, max_eq_right (mul_nonneg (by norm_num) (medianRadius_nonneg _ _ _ _))]
  ring

theorem stage_oracle_width (μ : Measure Gap) [IsProbabilityMeasure μ] (q : SignLaw)
    {ρ δ : ℝ} (hρ : 0 < ρ) (hρ4 : ρ ≤ 1/4) (hd : 0 < δ) (hu : δ ≤ 1/4)
    {z : Seed ρ δ × Table} (hz : z ∈ goodEvent μ q ρ δ) {s : ℕ}
    (hJ : 1 ≤ depth δ s) (hon : PilotOnset μ ρ (depth δ s)) :
    Anytime.halfWidth ((stage ρ δ s).tableInterval (z.1 s) (z.2 ∘ Nat.pair s)) ≤
      4 * radiusCoefficient * 16777216 * (EntropyTail.selection μ ρ ((4 : ℝ) ^ depth δ s)).toReal := by
  let S := stage ρ δ s
  let xs := (readBlock S.pilotCost S.pilot ((z.2 ∘ Nat.pair s) ∘ Nat.pair 0)).1
  have hg : pilotGood μ ρ δ s xs := goodEvent_pilot μ q ρ δ hz hJ
  have ho : zeroSelection (S.learnedLaw xs) ρ ((4 : ℝ) ^ depth δ s) ≤
      16777216 * EntropyTail.selection μ ρ ((4 : ℝ) ^ depth δ s) := by
    dsimp [S]
    rw [stage_active hJ]
    apply pilotStage_selection_le μ _ hρ hρ4 hJ hon _ xs
    simpa only [stage_active hJ, paidMedianStage] using hg.2
  have ht := ENNReal.toReal_mono (ENNReal.mul_ne_top (by norm_num)
    (finite_selection μ ρ _)) ho
  rw [ENNReal.toReal_mul] at ht
  norm_num only [ENNReal.toReal_ofNat] at ht
  have he : Anytime.halfWidth (S.tableInterval (z.1 s) (z.2 ∘ Nat.pair s)) =
      medianRadius (S.learnedLaw xs) ρ (remaining δ s) (4 * pilotGroups δ s (depth δ s)) := by
    dsimp [S, xs]
    rw [stage_active hJ]
    exact paidMedianStage_table_radius _ _ _ _ _ _ _
  rw [show (stage ρ δ s) = S from rfl, he]
  have hr := continuation_radius_le hd hu s hJ (S.learnedLaw xs) ρ
  nlinarith [radiusCoefficient_pos]

theorem oracle_effective_scale (μ : Measure Gap) (ρ : ℝ) {δ B : ℝ}
    (hd : 0 < δ) (hu : δ ≤ 1/4) (hB : 0 < B) {s : ℕ}
    (hs : stageCount B = s + 1) (hJ : 1 ≤ depth δ s) :
    (EntropyTail.selection μ ρ ((4 : ℝ) ^ depth δ s)).toReal ≤
      64 * (EntropyTail.selection μ ρ (B / Anytime.inflation B δ)).toReal := by
  let β := B / Anytime.inflation B δ
  have hβ : 0 < β := div_pos hB (Anytime.inflation_pos hB.le hd hu)
  have hn : β / 4096 ≤ (4 : ℝ) ^ depth δ s := by
    have := effective_budget hd hu hB.le hs hJ
    dsimp [β]
    convert this.le using 1; ring
  have hm := Anytime.selection_antitone μ ρ (by positivity : 0 < β / 4096) hn
  have hc := selection_budget_scale μ ρ (by positivity : 0 < β / 4096)
    (by linarith : β / 4096 ≤ β)
  have he : Real.sqrt (β / (β / 4096)) = 64 := by
    rw [show β / (β / 4096) = 4096 by field_simp]
    norm_num
  rw [he] at hc
  have ht := ENNReal.toReal_mono
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (finite_selection μ ρ β)) (hm.trans hc)
  simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 64)] using ht

theorem eventual_oracle_width (μ : Measure Gap) [IsProbabilityMeasure μ]
    {ρ δ : ℝ} (hρ : 0 < ρ) (hρ4 : ρ ≤ 1/4) (hd : 0 < δ) (hu : δ ≤ 1/4) :
    ∃ H : ℕ, 1 ≤ H ∧ ∀ (q : SignLaw) (z : Seed ρ δ × Table),
      z ∈ goodEvent μ q ρ δ → ∀ B : ℕ, H ≤ B →
        Anytime.halfWidth (interval ρ δ B z) ≤
          2 ^ 32 * radiusCoefficient *
            (EntropyTail.selection μ ρ ((B : ℝ) / Anytime.inflation B δ)).toReal := by
  obtain ⟨J₀, hJ₀⟩ := pilotOnset_eventually μ hρ (by linarith : ρ ≤ 1)
  obtain ⟨H, hH, hdepth⟩ := completed_depth_eventually hd hu (max J₀ 1)
  refine ⟨H, hH, fun q z hz B hB => ?_⟩
  obtain ⟨s, hs, hJ⟩ := hdepth B hB
  have hJ1 : 1 ≤ depth δ s := (le_max_right _ _).trans hJ
  have hon := hJ₀ (depth δ s) ((le_max_left _ _).trans hJ)
  have hw := stage_oracle_width μ q hρ hρ4 hd hu hz hJ1 hon
  have hB0 : (0 : ℝ) < B := by exact_mod_cast (show 0 < B by omega)
  have hk := oracle_effective_scale μ ρ hd hu hB0 hs hJ1
  rw [interval, observedInterval_eq, hs]
  apply (tableInterval_width _ _ _ _ s).trans
  have hC := radiusCoefficient_pos
  norm_num
  nlinarith

end ThresholdHC.ArbitraryLawController
