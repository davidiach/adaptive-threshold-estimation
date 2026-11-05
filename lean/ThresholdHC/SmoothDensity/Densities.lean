import ThresholdHC.SmoothDensity.Bump

noncomputable section
open MeasureTheory
open scoped ContDiff BigOperators
namespace ThresholdHC.SmoothDensity

/-- A centered density, with `a = 2` and `a = -2` giving the testing pair. -/
def centeredDensity (s : ℕ) (t a x : ℝ) : ℝ :=
  baseDensity x + a * (baseDensity x * perturbation s t x)

def density (s : ℕ) (t a p : ℝ) : ℝ := centeredDensity s t a (p - 1 / 2)

theorem centeredDensity_contDiff (s : ℕ) (t a : ℝ) :
    ContDiff ℝ ∞ (centeredDensity s t a) :=
  baseDensity_contDiff.add (contDiff_const.mul
    (baseDensity_contDiff.mul (perturbation_contDiff s t)))

theorem density_contDiff (s : ℕ) (t a : ℝ) : ContDiff ℝ ∞ (density s t a) :=
  (centeredDensity_contDiff s t a).comp (contDiff_id.sub contDiff_const)

theorem centeredDensity_compact (s : ℕ) (t a : ℝ) :
    HasCompactSupport (centeredDensity s t a) :=
  baseDensity_compact.add (HasCompactSupport.mul_left
    (show HasCompactSupport (fun x => baseDensity x * perturbation s t x) from
      baseDensity_compact.mul_right))

theorem centeredDensity_nonneg (s : ℕ) {t a : ℝ}
    (ht : 0 ≤ t) (ht1 : t ≤ 1) (ha : |a| ≤ 2) (x : ℝ) :
    0 ≤ centeredDensity s t a x := by
  have hp := perturbation_abs_le s ht ht1 x
  have hm : |a * perturbation s t x| ≤ 1 / 4 := by
    rw [abs_mul]
    nlinarith [mul_le_mul ha hp (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 2)]
  have hg := baseDensity_nonneg x
  have hc : 0 ≤ 1 + a * perturbation s t x := by
    linarith [neg_le_abs (a * perturbation s t x)]
  unfold centeredDensity
  nlinarith [mul_nonneg hg hc]

theorem density_supported (s : ℕ) (t a p : ℝ) (hp : p ∉ Set.Icc (1 / 4 : ℝ) (3 / 4)) :
    density s t a p = 0 := by
  have hx : 1 / 4 ≤ |p - 1 / 2| := by
    simp only [Set.mem_Icc, not_and_or, not_le] at hp
    rcases hp with hp | hp
    · linarith [neg_le_abs (p - 1 / 2)]
    · linarith [le_abs_self (p - 1 / 2)]
  simp only [density, centeredDensity, baseDensity_zero hx, zero_mul, mul_zero, zero_add]

theorem perturbation_integrable (s : ℕ) (t : ℝ) :
    Integrable (fun x => baseDensity x * perturbation s t x) := by
  have hc := baseDensity_contDiff.continuous.mul (perturbation_contDiff s t).continuous
  exact hc.integrable_of_hasCompactSupport baseDensity_compact.mul_right

theorem centeredDensity_integral (s : ℕ) (t a : ℝ) :
    ∫ x, centeredDensity s t a x = 1 := by
  have hi := perturbation_integrable s t
  have hz : (∫ x, baseDensity x * perturbation s t x) = 0 := by
    have he := integral_neg_eq_self (fun x => baseDensity x * perturbation s t x) (μ := volume)
    simp only [baseDensity_even, perturbation_odd, mul_neg, integral_neg] at he
    linarith
  unfold centeredDensity
  rw [integral_add baseDensity_integrable (hi.const_mul a),
    integral_const_mul, baseDensity_integral, hz]
  ring

theorem density_integral (s : ℕ) (t a : ℝ) : ∫ p, density s t a p = 1 := by
  unfold density
  rw [integral_sub_right_eq_self, centeredDensity_integral]

private def baseBound (k : ℕ) : ℝ := Classical.choose (baseDerivative_bounded k)

private theorem baseBound_pos (k : ℕ) : 0 < baseBound k :=
  (Classical.choose_spec (baseDerivative_bounded k)).1

private theorem baseBound_bound (k : ℕ) (x : ℝ) :
    |iteratedDeriv k baseDensity x| ≤ baseBound k :=
  (Classical.choose_spec (baseDerivative_bounded k)).2 x

private def pairBound (k : ℕ) : ℝ :=
  baseBound k + 2 * ∑ i ∈ Finset.range (k + 1),
    (k.choose i : ℝ) * baseBound i * ((k - i).factorial / 8)

private theorem pairBound_nonneg (k : ℕ) : 0 ≤ pairBound k := by
  unfold pairBound
  apply add_nonneg (baseBound_pos k).le
  apply mul_nonneg (by norm_num)
  exact Finset.sum_nonneg (fun i _ => mul_nonneg
    (mul_nonneg (Nat.cast_nonneg _) (baseBound_pos i).le) (by positivity))

private theorem centeredDensity_derivative_bound {s k : ℕ} (hk : k ≤ s) {t a : ℝ}
    (ht : 0 < t) (ht1 : t ≤ 1) (ha : |a| ≤ 2) (x : ℝ) :
    |iteratedDeriv k (centeredDensity s t a) x| ≤ pairBound k := by
  have hg : ContDiff ℝ k baseDensity := baseDensity_contDiff.of_le (by simp)
  have hp : ContDiff ℝ k (perturbation s t) := (perturbation_contDiff s t).of_le (by simp)
  have hprod : |iteratedDeriv k (fun y => baseDensity y * perturbation s t y) x| ≤
      ∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) * baseBound i * ((k - i).factorial / 8) := by
    rw [iteratedDeriv_fun_mul hg.contDiffAt hp.contDiffAt]
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    apply Finset.sum_le_sum
    intro i hi
    rw [abs_mul, abs_mul, abs_of_nonneg (by positivity : 0 ≤ (k.choose i : ℝ))]
    exact mul_le_mul
      (mul_le_mul_of_nonneg_left (baseBound_bound i x) (by positivity))
      (perturbation_derivative_bound (by omega : k - i ≤ s) ht ht1 x)
      (abs_nonneg _) (mul_nonneg (Nat.cast_nonneg _) (baseBound_pos i).le)
  change |iteratedDeriv k (fun y => baseDensity y +
    a * (baseDensity y * perturbation s t y)) x| ≤ _
  rw [iteratedDeriv_fun_add hg.contDiffAt
    (contDiff_const.mul (hg.mul hp)).contDiffAt, iteratedDeriv_const_mul_field]
  apply (abs_add_le _ _).trans
  rw [abs_mul]
  unfold pairBound
  exact add_le_add (baseBound_bound k x)
    (mul_le_mul ha hprod (abs_nonneg _) (by norm_num))

/-- A single finite derivative bound works for every smoothing scale and both signs. -/
theorem exists_uniform_density_bound (s : ℕ) :
    ∃ M : ℝ, 0 < M ∧ ∀ (t a : ℝ), 0 < t → t ≤ 1 → |a| ≤ 2 →
      ∀ k ≤ s, ∀ p, |iteratedDeriv k (density s t a) p| ≤ M := by
  refine ⟨1 + ∑ k ∈ Finset.range (s + 1), pairBound k, ?_, ?_⟩
  · have := Finset.sum_nonneg (fun k (_ : k ∈ Finset.range (s + 1)) => pairBound_nonneg k)
    linarith
  · intro t a ht ht1 ha k hk p
    have hb := centeredDensity_derivative_bound hk ht ht1 ha (p - 1 / 2)
    have hs := Finset.single_le_sum
      (fun k (_ : k ∈ Finset.range (s + 1)) => pairBound_nonneg k)
      (Finset.mem_range.mpr (show k < s + 1 by omega))
    change |iteratedDeriv k (fun x => centeredDensity s t a (x - 1 / 2)) p| ≤ _
    rw [iteratedDeriv_comp_sub_const]
    linarith

end ThresholdHC.SmoothDensity
