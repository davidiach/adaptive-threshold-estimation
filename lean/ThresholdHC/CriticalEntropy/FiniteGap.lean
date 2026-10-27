import ThresholdHC.CriticalEntropy.StoppingWindow
import ThresholdHC.CriticalEntropy.GeometricOverlap
import ThresholdHC.CriticalEntropy.Packing

/-! The finite-gap sign-entropy theorem for actual observable Bernoulli tests. -/

noncomputable section
open MeasureTheory ProbabilityTheory Real
open scoped ENNReal

namespace ThresholdHC.CriticalEntropy

theorem inverse_gap_scales_separated {K : ℕ} (d : Fin K → EntropyGap)
    (hgap : ∀ i j, j.val = i.val+1 → 2*(d j : ℝ) ≤ (d i : ℝ)) :
    ∀ i j, i ≤ j → (4 : ℝ)^(j.val-i.val)*(1/(d i : ℝ)^2) ≤ 1/(d j : ℝ)^2 := by
  apply geometric_separation_of_adjacent
  intro i j hij
  rw [mul_one_div]
  apply (div_le_div_iff₀ (sq_pos_of_pos (d i).property.1) (sq_pos_of_pos (d j).property.1)).mpr
  have hsq := (sq_le_sq₀ (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (d j).property.1.le)
    (d i).property.1.le).mpr
    (hgap i j hij)
  nlinarith

theorem signTest_window_overlap {R : Type} [MeasurableSpace R]
    (ν : Measure R) (A : SignTest R) {K : ℕ} (d : Fin K → EntropyGap)
    (hgap : ∀ i j, j.val = i.val+1 → 2*(d j : ℝ) ≤ (d i : ℝ))
    (c : ℝ) (hc : 0 ≤ c) (G : Finset (Fin K))
    (hcost : ∀ i ∈ G, (d i : ℝ)^2*(expectedSignTestWork ν (signParameter (d i) false) A).toReal ≤ 2*c)
    (z : R × (ℕ → Bool)) :
    (∑ i ∈ G, (signTestWindow A (entropyLowerTime (d i))
      (entropyUpperTime (expectedSignTestWork ν (signParameter (d i) false) A).toReal)).indicator
        (fun _ => (1 : ℝ)) z) ≤ 1+log (1024*(16*c+2))/log 4 := by
  classical
  let events := fun i : Fin K => signTestWindow A (entropyLowerTime (d i))
    (entropyUpperTime (expectedSignTestWork ν (signParameter (d i) false) A).toReal)
  let s := G.filter (fun i => z ∈ events i)
  have hcount : (∑ i ∈ G, (events i).indicator (fun _ => (1 : ℝ)) z) = (s.card : ℝ) := by
    simp only [Set.indicator_apply, Finset.sum_boole, s]
  change (∑ i ∈ G, (events i).indicator (fun _ => (1 : ℝ)) z) ≤ _
  rw [hcount]
  cases hstop : A.stop z with
  | top =>
    have hs : s = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro i hi
      have hmem := (Finset.mem_filter.mp hi).2
      have hle := hmem.2.2
      rw [hstop] at hle
      simp at hle
    rw [hs, Finset.card_empty, Nat.cast_zero]
    have hlog : 0 ≤ log (1024*(16*c+2)) := log_nonneg (by nlinarith)
    have hlog4 : 0 < log (4 : ℝ) := log_pos (by norm_num)
    positivity
  | coe k =>
    have hcard := geometric_interval_card s (fun i => 1/(d i : ℝ)^2)
      (fun i => one_div_pos.mpr (sq_pos_of_pos (d i).property.1)) (inverse_gap_scales_separated d hgap)
      (1/2048) (8*c+1) k (by norm_num) (by linarith) (by
        intro i hi
        obtain ⟨hiG, hiE⟩ := Finset.mem_filter.mp hi
        exact signTest_window_scale ν A (d i) z k hstop c (hcost i hiG) hiE)
    have he : (8*c+1)/(1/2048 : ℝ) = 1024*(16*c+2) := by ring
    simpa only [he] using hcard

/-- Finite-gap sign entropy (BC2): one observable test must pay a logarithmic
average cost across separated gaps. Only the negative-law work is charged.
There is no supplied information, event-packing, or fair-termination premise. -/
theorem finite_gap_sign_entropy {R : Type} [MeasurableSpace R]
    (ν : Measure R) [IsProbabilityMeasure ν] (A : SignTest R)
    (K : ℕ) (d : Fin K → EntropyGap) (hK : 32 ≤ log (K : ℝ))
    (hgap : ∀ i j, j.val = i.val+1 → 2*(d j : ℝ) ≤ (d i : ℝ))
    (hfinite : ∀ i b, expectedSignTestWork ν (signParameter (d i) b) A ≠ ∞)
    (herror : ∀ i b, (ν.prod (Tier2.tapeMeasure (signParameter (d i) b))).real
      {z | A.output z ≠ b} ≤ 1/10) :
    (K : ℝ)*log (K : ℝ)/512 ≤
      ∑ i, (d i : ℝ)^2*(expectedSignTestWork ν (signParameter (d i) false) A).toReal := by
  classical
  have hKnat : 0 < K := by
    by_contra hn
    have hz : K = 0 := by omega
    simp [hz] at hK
    linarith
  have hKpos : (0 : ℝ) < K := by exact_mod_cast hKnat
  let cost := fun i : Fin K => (d i : ℝ)^2*(expectedSignTestWork ν (signParameter (d i) false) A).toReal
  let c := (∑ i, cost i)/(K : ℝ)
  have hcost0 : ∀ i, 0 ≤ cost i := fun i => mul_nonneg (sq_nonneg _) ENNReal.toReal_nonneg
  have hc : 0 ≤ c := div_nonneg (Finset.sum_nonneg (fun i _ => hcost0 i)) hKpos.le
  have hmean : ∑ i, cost i = (K : ℝ)*c := by dsimp [c]; field_simp
  obtain ⟨G, hGcard, hGcost⟩ := half_low_cost cost hcost0 c hc hmean
  let events := fun i : Fin K => signTestWindow A (entropyLowerTime (d i))
    (entropyUpperTime (expectedSignTestWork ν (signParameter (d i) false) A).toReal)
  have hmass : ∀ i ∈ G, exp (-128*c-8) ≤
      (ν.prod (Tier2.tapeMeasure ⟨1/2, by norm_num⟩)).real (events i) := by
    intro i hi
    have hm : (ν.prod (Tier2.tapeMeasure (signParameter (d i) false))).real
        {z | A.output z = true} ≤ 1/10 := by simpa using herror i false
    have hp : (ν.prod (Tier2.tapeMeasure (signParameter (d i) true))).real
        {z | A.output z = false} ≤ 1/10 := by simpa using herror i true
    have hw := signTest_fair_window ν A (d i) hm hp (hfinite i false)
    exact (exp_le_exp.mpr (by have := hGcost i hi; dsimp [cost] at this; linarith)).trans hw
  have hpack := event_packing (ν.prod (Tier2.tapeMeasure ⟨1/2, by norm_num⟩)) G events
    (fun i _ => measurable_signTestWindow A _ _)
    (exp (-128*c-8)) (1+log (1024*(16*c+2))/log 4) hmass
    (fun z => signTest_window_overlap ν A d hgap c hc G hGcost z)
  have hhalf := mul_le_mul_of_nonneg_right hGcard (exp_pos (-128*c-8)).le
  have hbound := entropy_of_gap_count K c hKpos hK hc (hhalf.trans hpack)
  have hmul := mul_le_mul_of_nonneg_left hbound hKpos.le
  rw [← hmean] at hmul
  simpa only [mul_div_assoc] using hmul

end ThresholdHC.CriticalEntropy
