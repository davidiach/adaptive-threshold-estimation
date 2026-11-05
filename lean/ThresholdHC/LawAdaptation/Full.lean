import ThresholdHC.LawAdaptation.Budget
import ThresholdHC.LawAdaptation.Coverage
import ThresholdHC.LawAdaptation.Rate

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace ThresholdHC.LawAdaptation
open ThresholdHC.Tier6 ThresholdHC.HardBudget ThresholdHC.Anytime
open ThresholdHC.EntropyTail ThresholdHC.RareAboveTwo

variable {ι : Type} [Nonempty ι] {R : ι → ℕ → Type}
  [∀ i j, MeasurableSpace (R i j)]

theorem budget_width_on_identification
    (laws : ι → Measure Gap) [∀ i, IsProbabilityMeasure (laws i)]
    (base : ∀ i j, AdaptiveEstimator (R i j)) (truth : ι) (n m : ℕ) (η : ℝ)
    {ρ δ : ℝ} (hr : 0 < ρ) (hu : ρ ≤ 1/4) (hd : 0 < δ) (hd' : δ ≤ 1/4)
    (hH : 0 < pilotCost n m) {B : ℕ} (hB : 2*pilotCost n m ≤ B)
    (z : (∀ i j, R i j) × Table) (hcorrect : chosenTable laws n m η z.2 = truth) :
    halfWidth (budgetInterval laws n m η ρ base (fun i => radius (laws i) ρ (δ/2)) B z) ≤
      3000004*(selection (laws truth) ρ ((B:ℝ)/inflation (B:ℝ) δ)).toReal := by
  have hHB : pilotCost n m ≤ B := by omega
  have hrem : (1:ℝ) ≤ ((B-pilotCost n m:ℕ):ℝ) := by exact_mod_cast (show 1 ≤ B-pilotCost n m by omega)
  rw [budgetInterval_eq,ite_eq_left hHB,postTableInterval,hcorrect]
  have hw := all_budget_width (laws truth) (base truth) hr hu hrem
    (by linarith : 0 < δ/2) (by linarith : δ/2 ≤ 1/4) (z.1 truth) (z.2 ∘ Nat.add n)
  have hs := delayed_selection (laws truth) ρ
    (Nat.cast_nonneg (pilotCost n m))
    (by exact_mod_cast (show 0 < B by omega) : (0:ℝ) < B)
    (by exact_mod_cast hB : 2*(pilotCost n m:ℝ) ≤ (B:ℝ)) hd hd'
  rw [← Nat.cast_sub hHB] at hs
  have ht := ENNReal.toReal_mono
    (ENNReal.mul_ne_top (by norm_num) (finite_selection (laws truth) ρ _)) hs
  rw [ENNReal.toReal_mul] at ht
  norm_num only [ENNReal.toReal_ofNat] at ht
  exact hw.trans (by nlinarith only [ht])

/-- The actual observable family attains coverage and the true law's width on
one event, simultaneously over all physical flip budgets. -/
theorem finite_family_joint
    (laws : ι → Measure Gap) [∀ i, IsProbabilityMeasure (laws i)]
    (base : ∀ i j, AdaptiveEstimator (R i j)) (truth : ι) (q : SignLaw)
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n) {η : ℝ} (hη : 0 < η)
    (hdist : ∀ i j, i ≠ j → ∃ k : Fin m,
      η ≤ |evenMoment (laws i) (k.val+1)-evenMoment (laws j) (k.val+1)|)
    {ρ δ : ℝ} (hr : 0 < ρ) (hu : ρ ≤ 1/4) (hd : 0 < δ) (hd' : δ ≤ 1/4)
    (hsize : Real.log (4*(m:ℝ)/δ) ≤ (n:ℝ)*η^2/32)
    (hq : RarePrior (laws truth) ρ q)
    (hcap : ∀ j, PathwiseCap (base truth j) (stageCap j))
    (hf : ∀ j, ThresholdHC.Confidence.failureProbability (laws truth) (base truth j) q
      (radius (laws truth) ρ (δ/2) j) ≤ ENNReal.ofReal (stageFailure (δ/2) j)) :
    (familyStreamLaw (laws truth) base q) {z | ∃ B : ℕ,
      ¬ ((budgetInterval laws n m η ρ base (fun i => radius (laws i) ρ (δ/2)) B z).1 ≤
          signMean (laws truth) q.val ∧
        signMean (laws truth) q.val ≤
          (budgetInterval laws n m η ρ base (fun i => radius (laws i) ρ (δ/2)) B z).2 ∧
        (2*pilotCost n m ≤ B →
          halfWidth (budgetInterval laws n m η ρ base (fun i => radius (laws i) ρ (δ/2)) B z) ≤
            3000004*(selection (laws truth) ρ ((B:ℝ)/inflation (B:ℝ) δ)).toReal))} ≤
      ENNReal.ofReal δ := by
  let P := familyStreamLaw (laws truth) base q
  let Ep := {z : (∀ i j, R i j) × Table | chosenTable laws n m η z.2 ≠ truth}
  let Eo := {z : (∀ i j, R i j) × Table | ∃ k,
    ¬ ((tableInterval (base truth) ρ (radius (laws truth) ρ (δ/2))
      (z.1 truth) (z.2 ∘ Nat.add n) k).1 ≤ signMean (laws truth) q.val ∧
      signMean (laws truth) q.val ≤
      (tableInterval (base truth) ρ (radius (laws truth) ρ (δ/2))
        (z.1 truth) (z.2 ∘ Nat.add n) k).2)}
  have hp : P Ep ≤ ENNReal.ofReal (δ/2) := by
    apply (family_pilot_error laws base truth q hn hη hdist).trans
    apply ENNReal.ofReal_le_ofReal
    apply pilot_calibration hm (by linarith : 0 < δ/2)
    convert hsize using 1
    congr 1
    ring
  have ho : P Eo ≤ ENNReal.ofReal (δ/2) := by
    have hpres := branchInputs_preserving (laws truth) base q n truth
    have h := Measure.le_map_apply (μ := familyStreamLaw (laws truth) base q)
      hpres.measurable.aemeasurable
      {z : (∀ j, R truth j) × Table | ∃ k,
        ¬ ((tableInterval (base truth) ρ (radius (laws truth) ρ (δ/2)) z.1 z.2 k).1 ≤
          signMean (laws truth) q.val ∧ signMean (laws truth) q.val ≤
          (tableInterval (base truth) ρ (radius (laws truth) ρ (δ/2)) z.1 z.2 k).2)}
    rw [hpres.map_eq] at h
    exact h.trans (all_stage_coverage (laws truth) (base truth) q ρ _
      (by linarith : 0 ≤ δ/2) ⟨(signMean_bounds (laws truth) q).1,hq⟩ hcap hf)
  have hsub : {z | ∃ B : ℕ,
      ¬ ((budgetInterval laws n m η ρ base (fun i => radius (laws i) ρ (δ/2)) B z).1 ≤
          signMean (laws truth) q.val ∧ signMean (laws truth) q.val ≤
          (budgetInterval laws n m η ρ base (fun i => radius (laws i) ρ (δ/2)) B z).2 ∧
        (2*pilotCost n m ≤ B →
          halfWidth (budgetInterval laws n m η ρ base (fun i => radius (laws i) ρ (δ/2)) B z) ≤
            3000004*(selection (laws truth) ρ ((B:ℝ)/inflation (B:ℝ) δ)).toReal))} ⊆ Ep ∪ Eo := by
    rintro z ⟨B,hbad⟩
    by_cases hc : chosenTable laws n m η z.2 = truth
    · apply Or.inr
      by_contra hnone
      apply hbad
      have hcov : (budgetInterval laws n m η ρ base (fun i => radius (laws i) ρ (δ/2)) B z).1 ≤
          signMean (laws truth) q.val ∧ signMean (laws truth) q.val ≤
          (budgetInterval laws n m η ρ base (fun i => radius (laws i) ρ (δ/2)) B z).2 := by
        rw [budgetInterval_eq]
        split_ifs with hB
        · dsimp only [postTableInterval]
          rw [hc]
          exact not_not.mp (fun h => hnone ⟨_,h⟩)
        · exact ⟨(signMean_bounds (laws truth) q).1,hq⟩
      refine ⟨hcov.1,hcov.2,?_⟩
      intro hB
      exact budget_width_on_identification laws base truth n m η hr hu hd hd'
        (by unfold pilotCost; positivity) hB z hc
    · exact Or.inl hc
  calc
    _ ≤ P (Ep ∪ Eo) := measure_mono hsub
    _ ≤ ENNReal.ofReal (δ/2)+ENNReal.ofReal (δ/2) :=
      (measure_union_le _ _).trans (add_le_add hp ho)
    _ = ENNReal.ofReal δ := by
      rw [← ENNReal.ofReal_add (by linarith : 0 ≤ δ/2) (by linarith : 0 ≤ δ/2)]
      congr 1
      ring

/-- Deterministic pilot size, charged once before the selected procedure. -/
def sampleCount (m : ℕ) (η δ : ℝ) : ℕ :=
  ⌈32*Real.log (4*(m:ℝ)/δ)/η^2⌉₊

theorem sampleCount_spec {m : ℕ} (hm : 0 < m) {η δ : ℝ}
    (hη : 0 < η) (hd : 0 < δ) (hd' : δ ≤ 1/4) :
    0 < sampleCount m η δ ∧
      Real.log (4*(m:ℝ)/δ) ≤ (sampleCount m η δ:ℝ)*η^2/32 := by
  have hm' : (1:ℝ) ≤ m := by exact_mod_cast hm
  have hl : 0 < Real.log (4*(m:ℝ)/δ) := Real.log_pos
    ((lt_div_iff₀ hd).mpr (by linarith))
  have hη2 : 0 < η^2 := sq_pos_of_pos hη
  constructor
  · exact Nat.ceil_pos.mpr (by positivity)
  · have h := (div_le_iff₀ hη2).mp (Nat.le_ceil (32*Real.log (4*(m:ℝ)/δ)/η^2))
    change Real.log (4*(m:ℝ)/δ) ≤ (⌈32*Real.log (4*(m:ℝ)/δ)/η^2⌉₊:ℝ)*η^2/32
    linarith

/-- For every supplied finite family of distinct gap laws, construct a single
observable procedure before the true family member or sign law is supplied.
Its cap holds on every path; coverage and oracle width hold jointly at all
integer flip budgets with failure probability at most delta. -/
theorem finite_family_anytime [Fintype ι]
    (laws : ι → Measure Gap) [∀ i, IsProbabilityMeasure (laws i)]
    (hinj : Function.Injective laws) {ρ δ : ℝ}
    (hr : 0 < ρ) (hu : ρ ≤ 1/4) (hd : 0 < δ) (hd' : δ ≤ 1/4) :
    ∃ (m : ℕ) (η : ℝ), 0 < m ∧ 0 < η ∧
      ∃ (R : ι → ℕ → Type) (_ : ∀ i j, MeasurableSpace (R i j))
        (base : ∀ i j, AdaptiveEstimator (R i j)),
        (∀ (B : ℕ) (upper : Bool), PathwiseCap
          (budgetEndpoint laws (sampleCount m η δ) m η ρ base
            (fun i => radius (laws i) ρ (δ/2)) B upper) B) ∧
        (∀ (truth : ι) (q : SignLaw), RarePrior (laws truth) ρ q →
          (familyStreamLaw (laws truth) base q) {z | ∃ B : ℕ,
            ¬ ((budgetInterval laws (sampleCount m η δ) m η ρ base
                (fun i => radius (laws i) ρ (δ/2)) B z).1 ≤ signMean (laws truth) q.val ∧
              signMean (laws truth) q.val ≤
                (budgetInterval laws (sampleCount m η δ) m η ρ base
                  (fun i => radius (laws i) ρ (δ/2)) B z).2 ∧
              (2*pilotCost (sampleCount m η δ) m ≤ B →
                halfWidth (budgetInterval laws (sampleCount m η δ) m η ρ base
                  (fun i => radius (laws i) ρ (δ/2)) B z) ≤
                    3000004*(selection (laws truth) ρ ((B:ℝ)/inflation (B:ℝ) δ)).toReal))} ≤
            ENNReal.ofReal δ) := by
  obtain ⟨m,hm,η,hη,hdist⟩ := finite_moment_separation laws hinj
  have hstages (i : ι) := known_stages (laws i) hr hu
    (by linarith : 0 < δ/2) (by linarith : δ/2 ≤ 1/4)
  choose R mR base hb using hstages
  let (i : ι) (j : ℕ) := mR i j
  refine ⟨m,η,hm,hη,R,mR,base,?_,?_⟩
  · exact budgetEndpoint_cap laws (sampleCount m η δ) m η ρ base
      (fun i => radius (laws i) ρ (δ/2))
  · intro truth q hq
    have hn := sampleCount_spec hm hη hd hd'
    exact finite_family_joint laws base truth q hm hn.1 hη hdist hr hu hd hd'
      hn.2 hq (fun j => (hb truth j).1) (fun j => (hb truth j).2 q hq)

end ThresholdHC.LawAdaptation

