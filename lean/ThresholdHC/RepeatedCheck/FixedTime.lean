import ThresholdHC.RepeatedCheck.Specification
import ThresholdHC.Proofs.Tier2.ClassifierProbability

/-! Display (28) of `research/2026-10-30-confidence-transfer/ANYTIME.md`: the
fixed-time Chebyshev bound. The head count of the first `n` flips is a sum of
`n` independent bits with mean `θ`, so its variance is `nθ(1-θ)`, and Markov's
inequality for the squared deviation at level `3n/4` gives the miss bound
`4θ(1-θ)/3`, which is at most `1/4` for `θ ≤ 1/4`. -/

noncomputable section
open MeasureTheory ProbabilityTheory
open ThresholdHC.Tier2

namespace ThresholdHC.RepeatedCheck

theorem bit_sq (b : Bool) : bit b ^ 2 = bit b := by
  cases b <;> simp [bit]

theorem abs_bit_le (b : Bool) : |bit b| ≤ 1 := by
  cases b <;> simp [bit]

/-- The real head count of the first `n` flips is the sum of the first `n`
observation bits. -/
theorem heads_cast (ω : ℕ → Bool) (n : ℕ) :
    ((((Finset.range n).filter (fun t => ω t = true)).card : ℕ) : ℝ) =
      ∑ i ∈ Finset.range n, observations i ω := by
  rw [Finset.natCast_card_filter]
  rfl

theorem memLp_observations (θ : unitInterval) (i : ℕ) :
    MemLp (observations i) 2 (tapeMeasure θ) :=
  MemLp.of_bound (measurable_observations i).aestronglyMeasurable 1
    (ae_of_all _ fun ω => by rw [Real.norm_eq_abs]; exact abs_bit_le (ω i))

theorem variance_observations (θ : unitInterval) (i : ℕ) :
    variance (observations i) (tapeMeasure θ) = (θ : ℝ) * (1 - θ) := by
  rw [variance_eq_sub (memLp_observations θ i)]
  have h2 : (observations i) ^ 2 = observations i := funext fun ω => bit_sq (ω i)
  rw [h2, observations_mean]
  ring

theorem variance_heads (θ : unitInterval) (n : ℕ) :
    variance (∑ i ∈ Finset.range n, observations i) (tapeMeasure θ) =
      n * ((θ : ℝ) * (1 - θ)) := by
  rw [IndepFun.variance_sum (fun i _ => memLp_observations θ i)
    (fun i _ j _ hij => (observations_independent θ).indepFun hij)]
  simp [variance_observations]

theorem integral_heads (θ : unitInterval) (n : ℕ) :
    ∫ ω, (∑ i ∈ Finset.range n, observations i) ω ∂tapeMeasure θ = n * (θ : ℝ) := by
  simp only [Finset.sum_apply]
  rw [integral_finsetSum _ (fun i _ => (memLp_observations θ i).integrable one_le_two)]
  simp [observations_mean]

/-- The exact second moment of the centred head count. -/
theorem integral_sq_deviation (θ : unitInterval) (n : ℕ) :
    ∫ ω, (∑ i ∈ Finset.range n, observations i ω - n * (θ : ℝ)) ^ 2 ∂tapeMeasure θ =
      n * ((θ : ℝ) * (1 - θ)) := by
  have hm : AEMeasurable (∑ i ∈ Finset.range n, observations i) (tapeMeasure θ) :=
    Finset.aemeasurable_sum _ fun i _ => (measurable_observations i).aemeasurable
  rw [← variance_heads θ n, variance_eq_integral hm, integral_heads]
  simp only [Finset.sum_apply]

theorem integrable_sq_deviation (θ : unitInterval) (n : ℕ) :
    Integrable (fun ω => (∑ i ∈ Finset.range n, observations i ω - n * (θ : ℝ)) ^ 2)
      (tapeMeasure θ) := by
  have hL : MemLp (fun ω => ∑ i ∈ Finset.range n, observations i ω - n * (θ : ℝ)) 2
      (tapeMeasure θ) := by
    have hs : MemLp (∑ i ∈ Finset.range n, observations i) 2 (tapeMeasure θ) :=
      memLp_finsetSum' _ (fun i _ => memLp_observations θ i)
    have h := hs.sub (memLp_const (n * (θ : ℝ)))
    convert h using 1
    funext ω
    simp [Finset.sum_apply]
  exact hL.integrable_sq

/-- Fixed-time miss bound `4θ(1-θ)/3` for the polynomial miss event. -/
theorem fixed_time_tail (θ : unitInterval) (n : ℕ) :
    (tapeMeasure θ).real
      {ω | 3 * (n : ℝ) < 4 * ((((Finset.range n).filter (fun t => ω t = true)).card : ℝ) -
        n * (θ : ℝ)) ^ 2} ≤ 4 * (θ : ℝ) * (1 - θ) / 3 := by
  have hθ0 : 0 ≤ (θ : ℝ) := θ.2.1
  have hθ1 : (θ : ℝ) ≤ 1 := θ.2.2
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    have he : {ω : ℕ → Bool | 3 * ((0 : ℕ) : ℝ) < 4 * ((((Finset.range 0).filter
        (fun t => ω t = true)).card : ℝ) - ((0 : ℕ) : ℝ) * (θ : ℝ)) ^ 2} = ∅ := by
      ext ω
      simp
    rw [he, measureReal_empty]
    have : 0 ≤ (θ : ℝ) * (1 - θ) := mul_nonneg hθ0 (by linarith)
    linarith
  · have hnr : (0 : ℝ) < n := by exact_mod_cast hn
    set f : (ℕ → Bool) → ℝ := fun ω => (∑ i ∈ Finset.range n, observations i ω - n * (θ : ℝ)) ^ 2
      with hf
    have hmarkov := mul_meas_ge_le_integral_of_nonneg (μ := tapeMeasure θ) (f := f)
      (ae_of_all _ fun ω => sq_nonneg _) (integrable_sq_deviation θ n) (3 * n / 4)
    rw [hf, integral_sq_deviation] at hmarkov
    have hsub : {ω | 3 * (n : ℝ) < 4 * ((((Finset.range n).filter (fun t => ω t = true)).card : ℝ) -
        n * (θ : ℝ)) ^ 2} ⊆ {ω | 3 * (n : ℝ) / 4 ≤ f ω} := by
      intro ω hω
      simp only [Set.mem_ofPred_eq, heads_cast] at hω ⊢
      rw [hf]
      linarith
    have hmono := measureReal_mono (μ := tapeMeasure θ) hsub
    have hpos : (0 : ℝ) < 3 * n / 4 := by positivity
    calc _ ≤ (tapeMeasure θ).real {ω | 3 * (n : ℝ) / 4 ≤ f ω} := hmono
      _ ≤ n * ((θ : ℝ) * (1 - θ)) / (3 * n / 4) := by
          rw [le_div_iff₀ hpos]
          linarith
      _ = 4 * (θ : ℝ) * (1 - θ) / 3 := by
          field_simp

theorem quarter_bound (θ : ℝ) (h : θ ≤ 1/4) : 4 * θ * (1 - θ) / 3 ≤ 1/4 := by
  nlinarith

/-- Display (28): the fixed-time miss probability is at most `1/4` for every
`θ ≤ 1/4` and every `n`. -/
theorem fixedTime_holds : FixedTimeStatement := by
  intro θ hθ n
  exact (fixed_time_tail θ n).trans (quarter_bound θ hθ)

/-- At `θ = 1/4` the polynomial miss event is the paper's literal event
`(4H_n - n)² > 12n`. -/
theorem quarter_event (θ : unitInterval) (hθ : (θ : ℝ) = 1/4) (n : ℕ) :
    {ω : ℕ → Bool | 12 * (n : ℝ) < (4 * (((Finset.range n).filter (fun t => ω t = true)).card : ℝ) - n) ^ 2} =
      {ω | 3 * (n : ℝ) < 4 * ((((Finset.range n).filter (fun t => ω t = true)).card : ℝ) -
        n * (θ : ℝ)) ^ 2} := by
  ext ω
  simp only [Set.mem_ofPred_eq, hθ]
  constructor <;> intro h <;> nlinarith

/-- Display (28) at `θ = 1/4` in the paper's literal form. -/
theorem fixed_time_quarter (θ : unitInterval) (hθ : (θ : ℝ) = 1/4) (n : ℕ) :
    (Measure.infinitePi (fun _ : ℕ => bernoulliMeasure true false θ)).real
      {ω | 12 * (n : ℝ) < (4 * (((Finset.range n).filter (fun t => ω t = true)).card : ℝ) - n) ^ 2} ≤ 1/4 := by
  rw [quarter_event θ hθ n]
  exact fixedTime_holds θ (le_of_eq hθ) n

end ThresholdHC.RepeatedCheck
