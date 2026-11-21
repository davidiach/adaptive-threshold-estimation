import ThresholdHC.BernoulliTimeUniform.PrefixKL
import ThresholdHC.BernoulliTimeUniform.Testing
import ThresholdHC.BernoulliTimeUniform.Schedule

/-!
The Bernoulli-subfamily time-uniform lower bound.

The interval midpoint is an online estimator. The base constant sign law
`3 rho/4` and the alternatives `3 rho/4 + rho/(4 3^k)` are tested at the
budgets `N_k`; the observable prefix KL of each alternative is at most
`(1-delta) log(k+2)`, so the first-crossing test forces the half-width to be
at least a third of the displacement at infinitely many `N_k`, and the
schedule converts this into the displayed coefficient.
-/

noncomputable section
open MeasureTheory InformationTheory Real Filter
open scoped ENNReal Topology
namespace ThresholdHC.BernoulliTimeUniform
open ThresholdHC.Tier3 ThresholdHC.Tier6 ThresholdHC.RareAboveTwo ThresholdHC.AnytimeLower

theorem constant_prior_prefix_kl : ConstantPriorPrefixKLStatement := constant_prefix_kl

theorem bernoulli_time_uniform_lower : BernoulliTimeUniformLowerStatement := by
  intro R _ μ _ ρ δ hρ hρ4 _ hδ1 A L U hL hU t hc M
  have hθ : 0 < 3*ρ/4 ∧ 3*ρ/4 < 1 := ⟨by positivity, by linarith⟩
  have hθk (k : ℕ) : 0 < 3*ρ/4+meanShift ρ k ∧ 3*ρ/4+meanShift ρ k < 1 :=
    ⟨by linarith [meanShift_pos hρ k], by linarith [meanShift_le hρ k]⟩
  let q := ThresholdHC.StoppingProgram.constantPrior (3*ρ/4) ⟨hθ.1.le, hθ.2.le⟩
  let r (k : ℕ) := ThresholdHC.StoppingProgram.constantPrior (3*ρ/4+meanShift ρ k)
    ⟨(hθk k).1.le, (hθk k).2.le⟩
  have hqm : signMean μ q.val = 3*ρ/4 := ThresholdHC.StoppingProgram.constantPrior_mean μ _ _
  have hrm (k : ℕ) : signMean μ (r k).val = 3*ρ/4+meanShift ρ k :=
    ThresholdHC.StoppingProgram.constantPrior_mean μ _ _
  have hq : RarePrior μ ρ q := by
    change signMean μ q.val ≤ ρ
    rw [hqm]; linarith
  have hr (k : ℕ) : RarePrior μ ρ (r k) := by
    change signMean μ (r k).val ≤ ρ
    rw [hrm k]; linarith [meanShift_le hρ k]
  have hmean (k : ℕ) : signMean μ (r k).val = signMean μ q.val+meanShift ρ k := by
    rw [hrm k, hqm]
  let N := scheduleBudget ρ δ
  let K (k : ℕ) : ℝ := (N k:ℝ)*((3*ρ/4+meanShift ρ k)-3*ρ/4)^2/(3*ρ/4*(1-3*ρ/4))
  have hKe (k : ℕ) : K k = (N k:ℝ)*(meanShift ρ k)^2/baseVar ρ := by
    simp only [K, baseVar]
    ring
  have hK0 (k : ℕ) : 0 ≤ K k := by
    rw [hKe]
    exact div_nonneg (mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _)) (baseVar_pos hρ hρ4).le
  have hKle (k : ℕ) : K k ≤ (1-δ)*log ((k:ℝ)+2) := by
    rw [hKe]
    exact scheduleBudget_information hρ hρ4 hδ1 k
  have hkl (k : ℕ) : klDiv (observablePrefixLaw μ A (r k) (N k))
      (observablePrefixLaw μ A q (N k)) ≤ ENNReal.ofReal (K k) :=
    constant_prefix_kl R μ A (3*ρ/4) (3*ρ/4+meanShift ρ k) hθ (hθk k) (N k)
  have hdiv := not_summable_information hδ1 K hKle
  let H : ∀ n, R × Prefix n → ℝ := fun n x => (L n x+U n x)/2
  have hH : ∀ n, Measurable (H n) := fun n => ((hL n).add (hU n)).div_const 2
  have hacc : OnlineAccuracy μ A H ρ δ t := interval_midpoint_accuracy μ A L U t hc
  have hfreq := observed_third_frequently μ A H hH hδ1 t hacc q hq r hr
    (meanShift ρ) (meanShift_pos hρ) hmean (meanShift_sep hρ)
    N (scheduleBudget_mono hρ hρ4 hδ1) K hK0 hkl hdiv
  obtain ⟨k, hk1, hk2, hk3⟩ := (hfreq.and_eventually (schedule_eventually hρ hρ4 hδ1 M)).exists
  refine ⟨N k, hk2, ?_⟩
  have hNpos : (0:ℝ) < (N k:ℝ) := by
    have : 0 < N k := lt_of_lt_of_le (by omega) hk2
    exact_mod_cast this
  have ha := meanShift_pos hρ k
  have hε : 0 < 1-δ := by linarith
  rw [← Real.sqrt_mul (by positivity : (0:ℝ) ≤ 3*(1-δ)*ρ/64)]
  apply le_trans _ hk1
  apply (Real.sqrt_le_left (by positivity)).mpr
  rw [div_mul_div_comm, div_le_iff₀ (by positivity : (0:ℝ) < 64*(N k:ℝ))]
  have he : (meanShift ρ k/3)^2*(64*(N k:ℝ)) = 64*(N k:ℝ)*(meanShift ρ k)^2/9 := by ring
  rw [he]
  have hk3' : 27*(1-δ)*ρ*log (log (N k:ℝ)) ≤ 64*(N k:ℝ)*(meanShift ρ k)^2 := hk3
  linarith

end ThresholdHC.BernoulliTimeUniform
