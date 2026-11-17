import ThresholdHC.FiniteLawCertificates.Objective
import ThresholdHC.FiniteLawCertificates.Quantile

/-! Finite rational data connected to the original measure-level definitions. -/
noncomputable section
open MeasureTheory
open scoped BigOperators ENNReal Classical
namespace ThresholdHC.FiniteLawCertificates
open ThresholdHC.Tier6

/-- Residual mass whose inverse-square resolution threshold is affordable. -/
def tailWeights {n : ℕ} (g w s : Fin n → ℚ) (B : ℚ) : Fin n → ℚ :=
  fun i => if 1 ≤ B*(g i)^2 then w i*(1-s i) else 0

def unresolvedWeights {n : ℕ} (g w s : Fin n → ℚ) (B : ℚ) : Fin n → ℚ :=
  fun i => if B*(g i)^2 < 1 then w i*(1-s i) else 0

def resolvedWeights {n : ℕ} (g w s : Fin n → ℚ) (B : ℚ) : Fin n → ℚ :=
  fun i => w i*s i + tailWeights g w s B i

theorem tailWeights_nonneg {n : ℕ} (g w s : Fin n → ℚ) (B : ℚ)
    (hw : ∀ i, 0 ≤ w i) (hs : ∀ i, 0 ≤ s i ∧ s i ≤ 1) (i : Fin n) :
    0 ≤ tailWeights g w s B i := by
  unfold tailWeights
  split_ifs
  · exact mul_nonneg (hw i) (sub_nonneg.mpr (hs i).2)
  · exact le_rfl

theorem tailMeasure_eq {n : ℕ} (g w s : Fin n → ℚ) (B : ℚ)
    (hg : ∀ i, 0 < g i ∧ g i ≤ 1/2) (hw : ∀ i, 0 ≤ w i)
    (hs : ∀ i, 0 ≤ s i ∧ s i ≤ 1) :
    (atomicMeasure (points g hg) w - atomicMeasure (points g hg) (fun i => w i*s i)).restrict
      {x : Gap | 1 ≤ (B:ℝ)*(x:ℝ)^2} = atomicMeasure (points g hg) (tailWeights g w s B) := by
  rw [atomicMeasure_sub _ w _ (fun i => mul_nonneg (hw i) (hs i).1)
    (fun i => by nlinarith [hw i, (hs i).2]), atomicMeasure_restrict]
  congr 1
  funext i
  have hc : (1:ℝ) ≤ (B:ℝ)*(g i:ℝ)^2 ↔ (1:ℚ) ≤ B*(g i)^2 := by exact_mod_cast Iff.rfl
  simp only [tailWeights, points, Set.mem_ofPred_eq, hc]
  split_ifs <;> ring

theorem unresolvedMeasure_eq {n : ℕ} (g w s : Fin n → ℚ) (B : ℚ)
    (hg : ∀ i, 0 < g i ∧ g i ≤ 1/2) (hw : ∀ i, 0 ≤ w i)
    (hs : ∀ i, 0 ≤ s i ∧ s i ≤ 1) :
    (atomicMeasure (points g hg) w - atomicMeasure (points g hg) (fun i => w i*s i)).restrict
      {x : Gap | (B:ℝ)*(x:ℝ)^2 < 1} = atomicMeasure (points g hg) (unresolvedWeights g w s B) := by
  rw [atomicMeasure_sub _ w _ (fun i => mul_nonneg (hw i) (hs i).1)
    (fun i => by nlinarith [hw i, (hs i).2]), atomicMeasure_restrict]
  congr 1
  funext i
  have hc : (B:ℝ)*(g i:ℝ)^2 < 1 ↔ B*(g i)^2 < 1 := by exact_mod_cast Iff.rfl
  simp only [unresolvedWeights, points, Set.mem_ofPred_eq, hc]
  split_ifs <;> ring

theorem resolvedMeasure_eq {n : ℕ} (g w s : Fin n → ℚ) (B : ℚ)
    (hg : ∀ i, 0 < g i ∧ g i ≤ 1/2) (hw : ∀ i, 0 ≤ w i)
    (hs : ∀ i, 0 ≤ s i ∧ s i ≤ 1) :
    atomicMeasure (points g hg) (fun i => w i*s i) +
      (atomicMeasure (points g hg) w - atomicMeasure (points g hg) (fun i => w i*s i)).restrict
        {x : Gap | 1 ≤ (B:ℝ)*(x:ℝ)^2} =
      atomicMeasure (points g hg) (resolvedWeights g w s B) := by
  rw [tailMeasure_eq g w s B hg hw hs]
  exact (atomicMeasure_add _ _ _ (fun i => mul_nonneg (hw i) (hs i).1)
    (tailWeights_nonneg g w s B hw hs)).symm

/-- The real integral in the finite known-law null-prefix contract. -/
def nullPrefixIntegral (μ : Measure Gap) (heads tails : ℕ) : ℝ :=
  ∫ x, (1/2-(x:ℝ))^heads*(1/2+(x:ℝ))^tails ∂μ

def nullPrefixValue {n : ℕ} (g w : Fin n → ℚ) (heads tails : ℕ) : ℚ :=
  ∑ i, w i*(1/2-g i)^heads*(1/2+g i)^tails

theorem nullPrefix_eq {n : ℕ} (g w : Fin n → ℚ)
    (hg : ∀ i, 0 < g i ∧ g i ≤ 1/2) (hw : ∀ i, 0 ≤ w i) (heads tails : ℕ) :
    nullPrefixIntegral (atomicMeasure (points g hg) w) heads tails =
      (nullPrefixValue g w heads tails:ℝ) := by
  rw [nullPrefixIntegral, integral_atomic _ w hw]
  simp only [nullPrefixValue, Rat.cast_sum, Rat.cast_mul, Rat.cast_pow,
    Rat.cast_add, Rat.cast_sub, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat, points]
  apply Finset.sum_congr rfl
  intro i _
  ring

def inverseValue {n : ℕ} (g v : Fin n → ℚ) : ℚ := ∑ i, v i/g i

theorem inverseIntegral_eq {n : ℕ} (g v : Fin n → ℚ)
    (hg : ∀ i, 0 < g i ∧ g i ≤ 1/2) (hv : ∀ i, 0 ≤ v i) :
    (∫ x : Gap, (x:ℝ)⁻¹ ∂atomicMeasure (points g hg) v) = (inverseValue g v:ℝ) := by
  rw [integral_atomic _ v hv]
  simp [inverseValue, points, div_eq_mul_inv]

def errorValue {n : ℕ} (g v : Fin n → ℚ) (M : ℚ) : ℚ :=
  ∑ i, v i*min 1 (1/(M*(g i)^2)^2)

theorem errorIntegral_eq {n : ℕ} (g v : Fin n → ℚ) (M : ℚ)
    (hg : ∀ i, 0 < g i ∧ g i ≤ 1/2) (hv : ∀ i, 0 ≤ v i) :
    (∫ x : Gap, min 1 (1/((M:ℝ)*(x:ℝ)^2)^2) ∂atomicMeasure (points g hg) v) =
      (errorValue g v M:ℝ) := by
  rw [integral_atomic _ v hv]
  simp [errorValue, points]

def tailWorkExpr {n : ℕ} (g v : Fin n → ℚ) (M : ℚ) :
    ThresholdHC.DeterministicCertificates.Expr :=
  ThresholdHC.DeterministicCertificates.sumExpr (List.ofFn fun i => .scale (v i)
    (.minimum (.rational M) (.scale (17/(g i)^2) (.add (.rational 1)
      (.maximum (.rational 0) (.log (.rational (M*(g i)^2))))))))

def tailWorkIntegral (τ : Measure Gap) (M : ℝ) : ℝ :=
  ∫ x : Gap, min M (17/(x:ℝ)^2*(1+max 0 (Real.log (M*(x:ℝ)^2)))) ∂τ

theorem tailWorkExpr_eval {n : ℕ} (g v : Fin n → ℚ) (M : ℚ)
    (hg : ∀ i, 0 < g i ∧ g i ≤ 1/2) (hv : ∀ i, 0 ≤ v i) :
    (tailWorkExpr g v M).eval = tailWorkIntegral (atomicMeasure (points g hg) v) (M:ℝ) := by
  rw [tailWorkIntegral, integral_atomic _ v hv]
  simp [tailWorkExpr, ThresholdHC.DeterministicCertificates.sumExpr_eval,
    List.map_ofFn, List.sum_ofFn, Function.comp_apply,
    ThresholdHC.DeterministicCertificates.Expr.eval, points]

theorem tailWork_accepted_sound {n : ℕ} (g v : Fin n → ℚ) (M : ℚ)
    (hg : ∀ i, 0 < g i ∧ g i ≤ 1/2) (hv : ∀ i, 0 ≤ v i)
    {claimed : ThresholdHC.DeterministicCertificates.Interval}
    {c : ThresholdHC.DeterministicCertificates.Evidence}
    (h : ThresholdHC.DeterministicCertificates.accepted (tailWorkExpr g v M) claimed c = true) :
    ThresholdHC.DeterministicCertificates.Contains claimed
      (tailWorkIntegral (atomicMeasure (points g hg) v) (M:ℝ)) := by
  rw [← tailWorkExpr_eval g v M hg hv]
  exact ThresholdHC.DeterministicCertificates.accepted_sound h

end ThresholdHC.FiniteLawCertificates
