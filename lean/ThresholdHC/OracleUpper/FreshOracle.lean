import ThresholdHC.OracleUpper.FreshProduct
import ThresholdHC.OracleLower.Realization
import ThresholdHC.Tier5.StoppingBase

/-! Risk and work of a magnitude-oracle estimator whose transcript law, at
every seed, is the product law of `freshProduct` with a seed-dependent
stopping length, and whose output is affine in the signed flips of a fixed
window. The squared risk is the seed integral of the exact conditional second
moment. The work is at most the seed integral of the stopping length: almost
every realized tape follows its policy, the policy stops at the stopping length,
and the seed marginal of the oracle law is the random law of the estimator. -/
noncomputable section
namespace ThresholdHC.OracleUpper
open MeasureTheory
open scoped ENNReal
open ThresholdHC ThresholdHC.Tier3 ThresholdHC.Tier5 ThresholdHC.Tier6 ThresholdHC.OracleLower

/-- Conditional second moment of an affine flip statistic about a target,
when K fresh flips with signed means `e k` are bought. -/
def seedMoment (K : ℕ) (e : ℕ → ℝ) (κ β : ℝ) : ℝ :=
  (κ + β * ∑ k ∈ Finset.range K, e k)^2 + β^2 * ∑ k ∈ Finset.range K, (1 - (e k)^2)

private theorem bounded_finite {α : Type} [Finite α] (f : α → ℝ) : ∃ C : ℝ, ∀ a, |f a| ≤ C := by
  obtain ⟨C, hC⟩ := (Set.finite_range fun a => |f a|).bddAbove
  exact ⟨C, fun a => hC ⟨a, rfl⟩⟩

theorem oracle_square_integral {R : Type} [MeasurableSpace R] (A : OracleEstimator R)
    (q : SignLaw) (K : R → ℕ) (π : R → ℕ → ℝ) (m : ℕ) (c β θ : ℝ) (hK : ∀ u, K u ≤ m)
    (hlaw : ∀ u (n : ℕ) (w : Prefix n), creationLaw (A.policy u) (fun i => (A.gap u i : ℝ))
      (fun i => q.val (A.gap u i)) w = freshProduct (K u) (π u) w)
    (hout : ∀ z, A.output z = c + β * ∑ k : Fin m, flipValue (z.2 k)) :
    ∫ z, (A.output z - θ)^2 ∂oracleLaw A q =
      ∫ u, seedMoment (K u) (fun k => 2 * π u k - 1) (c - θ) β ∂A.randomLaw := by
  let f : Prefix m → ℝ := fun w => ((c - θ) + β * ∑ k, flipValue (w k))^2
  obtain ⟨C, hC⟩ := bounded_finite f
  have hr := (oracle_realization R A q).2 m (fun _ w => f w) (fun _ => measurable_const)
    ⟨C, fun _ w => hC w⟩
  have hl : ∫ z, (A.output z - θ)^2 ∂oracleLaw A q =
      ∫ z, f (processPrefix m z.2) ∂oracleLaw A q := by
    congr 1
    funext z
    rw [hout]
    simp only [f, processPrefix]
    ring
  rw [hl, hr]
  congr 1
  funext u
  simp_rw [hlaw u m]
  rw [freshProduct_moment, min_eq_right (hK u)]
  rfl

theorem oracle_squared_risk {R : Type} [MeasurableSpace R] (A : OracleEstimator R)
    (q : SignLaw) (K : R → ℕ) (π : R → ℕ → ℝ) (m : ℕ) (c β θ : ℝ) (hK : ∀ u, K u ≤ m)
    (hlaw : ∀ u (n : ℕ) (w : Prefix n), creationLaw (A.policy u) (fun i => (A.gap u i : ℝ))
      (fun i => q.val (A.gap u i)) w = freshProduct (K u) (π u) w)
    (hout : ∀ z, A.output z = c + β * ∑ k : Fin m, flipValue (z.2 k)) :
    squaredRisk (oracleLaw A q) A.output θ =
      ENNReal.ofReal (∫ u, seedMoment (K u) (fun k => 2 * π u k - 1) (c - θ) β ∂A.randomLaw) := by
  rw [← oracle_square_integral A q K π m c β θ hK hlaw hout]
  let f : Prefix m → ℝ := fun w => (c + β * ∑ k, flipValue (w k) - θ)^2
  obtain ⟨C, hC⟩ := bounded_finite f
  have he : (fun z : R × ProcessTape => (A.output z - θ)^2) =
      fun z => f (processPrefix m z.2) := by
    funext z
    rw [hout]
    rfl
  have hm : Measurable (fun z : R × ProcessTape => f (processPrefix m z.2)) :=
    (measurable_of_countable f).comp
      (Measurable.of_eval fun i => (measurable_pi_apply i.val).comp measurable_snd)
  have hi : Integrable (fun z : R × ProcessTape => (A.output z - θ)^2) (oracleLaw A q) := by
    rw [he]
    exact (integrable_const C).mono' hm.aestronglyMeasurable
      (ae_of_all _ fun z => by rw [Real.norm_eq_abs]; exact hC _)
  unfold squaredRisk
  rw [ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ fun _ => sq_nonneg _)]

private theorem history_succ (x : ProcessTape) (j : ℕ) :
    processHistory x (j+1) = processHistory x j ++ (x j).toList := by
  unfold processHistory
  rw [List.ofFn_succ']
  cases h : x j <;> simp [processPrefix, List.concat_eq_append, h] <;> rfl

private theorem work_history (x : ProcessTape) (j : ℕ) :
    ThresholdHC.workOf (processPrefix j x) = ((processHistory x j).length : ℝ) := by
  induction j with
  | zero => simp [ThresholdHC.workOf, processHistory]
  | succ j ih =>
    rw [processPrefix_snoc, ThresholdHC.Proofs.workOf_snoc, ih, history_succ, List.length_append]
    cases h : x j <;> simp

/-- A tape that follows a policy stopping at history length K carries at most
K observations. -/
theorem path_work_le (x : ProcessTape) (K : ℕ)
    (hv : ∀ n, (x n).isSome = decide ((processHistory x n).length < K)) :
    totalProcessWork x ≤ K := by
  have hlen (j : ℕ) : (processHistory x j).length ≤ K := by
    induction j with
    | zero => simp [processHistory]
    | succ j ih =>
      rw [history_succ, List.length_append]
      by_cases h : (processHistory x j).length < K
      · cases x j <;> simp <;> omega
      · have hx := hv j
        simp only [h, decide_false] at hx
        have hn : x j = none := Option.not_isSome_iff_eq_none.mp (by simp [hx])
        rw [hn]
        simpa using ih
  apply iSup_le
  intro j
  rw [work_history, ENNReal.ofReal_natCast]
  exact_mod_cast hlen j

theorem oracle_work_le {R : Type} [MeasurableSpace R] (A : OracleEstimator R) (q : SignLaw)
    (K : R → ℕ) (m : ℕ) (hK : ∀ u, K u ≤ m) (hKm : Measurable K)
    (hpol : ∀ u xs, (A.policy u xs).isSome = decide (xs.length < K u)) :
    oracleWork A q ≤ ENNReal.ofReal (∫ u, (K u : ℝ) ∂A.randomLaw) := by
  have hv : ∀ᵐ z ∂oracleLaw A q, ∀ n,
      (z.2 n).isSome = (A.policy z.1 (processHistory z.2 n)).isSome := by
    apply ae_all_iff.mpr
    intro n
    exact realized_creation_valid_step A.randomLaw (oracleLaw A q) Prod.fst Prod.snd
      A.policy (fun r i => A.gap r i) (fun r i => q.val (A.gap r i))
      measurable_fst (fun k b => measurableSet_eq_fun
        ((measurable_pi_apply k).comp measurable_snd) measurable_const)
      A.policy_measurable (oracle_realization R A q).2 n
  have hKr : Measurable (fun u => (K u : ℝ)) :=
    (measurable_of_countable (fun k : ℕ => (k : ℝ))).comp hKm
  have hbound : ∀ u, |(K u : ℝ)| ≤ m := by
    intro u
    rw [abs_of_nonneg (Nat.cast_nonneg _)]
    exact_mod_cast hK u
  have hr := (oracle_realization R A q).2 0 (fun u _ => (K u : ℝ)) (fun _ => hKr)
    ⟨m, fun u _ => hbound u⟩
  have hseed : ∫ z, (K z.1 : ℝ) ∂oracleLaw A q = ∫ u, (K u : ℝ) ∂A.randomLaw := by
    refine hr.trans ?_
    congr 1
    funext u
    rw [← Finset.sum_mul, (creationLaw_total 0 (A.policy u) (fun i => (A.gap u i : ℝ))
      (fun i => q.val (A.gap u i)) (fun i => ⟨(A.gap u i).property.1.le, (A.gap u i).property.2⟩)
      (fun i => q.property.2 (A.gap u i))).2, one_mul]
  have hi : Integrable (fun z : R × ProcessTape => (K z.1 : ℝ)) (oracleLaw A q) :=
    (integrable_const (m : ℝ)).mono' (hKr.comp measurable_fst).aestronglyMeasurable
      (ae_of_all _ fun z => by rw [Real.norm_eq_abs]; exact hbound z.1)
  unfold oracleWork
  calc
    _ ≤ ∫⁻ z, ENNReal.ofReal (K z.1 : ℝ) ∂oracleLaw A q := by
      apply lintegral_mono_ae
      filter_upwards [hv] with z hz
      rw [ENNReal.ofReal_natCast]
      apply path_work_le
      intro n
      rw [hz n, hpol]
    _ = ENNReal.ofReal (∫ z, (K z.1 : ℝ) ∂oracleLaw A q) :=
      (ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ fun _ => Nat.cast_nonneg _)).symm
    _ = _ := by rw [hseed]

end ThresholdHC.OracleUpper
