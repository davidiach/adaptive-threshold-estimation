import ThresholdHC.FiniteQuantile.PosteriorEnergy
import ThresholdHC.StoppingProgram.InformationBellman
import ThresholdHC.StoppingProgram.MidpointInformation

noncomputable section
open MeasureTheory Set Real
open scoped ENNReal
namespace ThresholdHC.FiniteQuantile
open ThresholdHC.Tier6 ThresholdHC.StoppingProgram

/-- Finite support suffices even for the divided likelihood at impossible words. -/
theorem integrable_of_finite_gap_support (μ : Measure Gap) [IsFiniteMeasure μ]
    (hs : μ.support.Finite) (f : Gap → ℝ) : Integrable f μ := by
  have h : IntegrableOn f μ.support μ := by
    rw [← Set.biUnion_of_singleton μ.support, integrableOn_finite_biUnion hs]
    exact fun _ _ => integrableOn_singleton
  have hmem : ∀ᵐ g ∂μ, g ∈ μ.support := μ.support_mem_ae
  simpa only [IntegrableOn, Measure.restrict_eq_self_of_ae_mem hmem] using h

/-- Integrating a quadratic upper bound controls the squared contrast of
the mixed transcript, including a word of zero midpoint probability. -/
theorem mixture_quadratic_bound (μ : Measure Gap) [IsFiniteMeasure μ] (hs : μ.support.Finite)
    (D M V : Gap → ℝ) (hM : ∀ g, 0 ≤ M g)
    (hlocal : ∀ g y, 2*y*D g - y^2*M g ≤ V g) :
    (∫ g, D g ∂μ)^2 / (∫ g, M g ∂μ) ≤ ∫ g, V g ∂μ := by
  have hi := integrable_of_finite_gap_support μ hs
  have hint (y : ℝ) : 2*y*(∫ g, D g ∂μ) - y^2*(∫ g, M g ∂μ) ≤ ∫ g, V g ∂μ := by
    calc
      _ = ∫ g, (2*y*D g - y^2*M g) ∂μ := by
        rw [integral_sub (hi _) (hi _), integral_const_mul, integral_const_mul]
      _ ≤ _ := integral_mono (hi _) (hi _) (fun g => hlocal g y)
  rcases (integral_nonneg hM : 0 ≤ ∫ g, M g ∂μ).eq_or_lt with hz | hp
  · simpa [← hz] using hint 0
  · have hh := hint ((∫ g, D g ∂μ)/(∫ g, M g ∂μ))
    convert hh using 1
    field_simp
    ring

/-- The potential pays one price per observed flip. The supremum over
all capped stopping flows is bounded by the same price at every cap. -/
theorem informationRatio_of_potential (μ : Measure Gap) [IsProbabilityMeasure μ]
    (low high : SignLaw) (price : ℝ) (V : ℕ → ℕ → ℝ)
    (hroot : V 0 0 = 0)
    (hstop : ∀ n k, k ≤ n → prefixReward μ (midpointFourPriors low high) n k ≤ V n k)
    (hstep : ∀ n k, k ≤ n → V (n+1) k + V (n+1) (k+1) ≤
      V n k + price * prefixCoefficient μ (midpointPrior low high) n k) (cap : ℕ) :
    informationRatio μ cap (midpointFourPriors low high) ≤ ENNReal.ofReal price := by
  let w := prefixCoefficient μ (midpointPrior low high)
  let r := prefixReward μ (midpointFourPriors low high)
  have htree (d n k : ℕ) (hk : k ≤ n) (a : StopTree d) :
      treeInformation r d n k a ≤ V n k + price * treeWork w d n k a := by
    induction d generalizing n k with
    | zero => simpa [treeInformation, treeWork] using hstop n k hk
    | succ d ih =>
      cases a with
      | none => simpa [treeInformation, treeWork] using hstop n k hk
      | some a =>
        simp only [treeInformation, treeWork]
        have h := hstep n k hk
        change _ ≤ V n k + price * w n k at h
        linarith only [ih (n+1) k (by omega) a.1, ih (n+1) (k+1) (by omega) a.2, h]
  apply (informationRatio_le_bellmanRatio μ cap _ (fun n k _ hk =>
    midpoint_prefixInformation_finite μ low high n k hk)).trans
  apply ENNReal.ofReal_le_ofReal
  unfold bellmanRatio ratioValue
  apply Finset.sup'_le
  intro a _
  have hpos : 0 < rootWork w (cap-1) a :=
    zero_lt_one.trans_le (rootWork_bounds w (prefixCoefficient_nonneg μ _)
      (prefixCoefficient_add μ _) (prefixCoefficient_root μ _) (cap-1) a).1
  change rootInformation r (cap-1) a / rootWork w (cap-1) a ≤ price
  apply (div_le_iff₀ hpos).mpr
  have hh := htree ((cap-1)+1) 0 0 le_rfl (some a)
  simpa only [treeInformation, treeWork, hroot, zero_add, w, prefixCoefficient_root,
    rootInformation, rootWork] using hh

/-- A fractional tail atom has equal-sign midpoint mass w(a+b), and
its residual mass always has the negative sign. Here a and b include
the half-prior factors. -/
theorem fractional_word_bound {a b w : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hw : 0 ≤ w) (hw1 : w ≤ 1) (e y : ℝ) :
    2*y*(4*w*e*(a-b)) - y^2*(w*(a+b)+(1-w)*(2*b)) ≤
      w*(16*e^2)*posteriorEnergy a b := by
  have h : 2*y*(4*e*(a-b)) - y^2*(a+b) ≤ 16*e^2*posteriorEnergy a b := by
    rcases (add_nonneg ha hb).eq_or_lt with hz | hp
    · have ha0 : a = 0 := by linarith
      have hb0 : b = 0 := by linarith
      simp [ha0,hb0,posteriorEnergy]
    · rw [posteriorEnergy, ← mul_div_assoc, le_div_iff₀ hp]
      nlinarith only [sq_nonneg (y*(a+b)-4*e*(a-b))]
  nlinarith only [mul_le_mul_of_nonneg_left h hw,
    mul_nonneg (sq_nonneg y) (mul_nonneg (sub_nonneg.mpr hw1) hb)]

end ThresholdHC.FiniteQuantile
