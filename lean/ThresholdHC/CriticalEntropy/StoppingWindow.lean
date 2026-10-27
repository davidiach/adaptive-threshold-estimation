import ThresholdHC.CriticalEntropy.SignTest
import ThresholdHC.CriticalEntropy.EarlyDecision

/-! Constructing the stopping windows used by the finite-gap entropy bound. -/

noncomputable section
open MeasureTheory ProbabilityTheory Real
open scoped ENNReal

namespace ThresholdHC.CriticalEntropy

theorem signTest_early_minus {R : Type} [MeasurableSpace R]
    (ν : Measure R) [IsProbabilityMeasure ν] (A : SignTest R)
    (d : EntropyGap) (n : ℕ) (hn : (n : ℝ)*(d : ℝ)^2 ≤ 1/1024)
    (hplus : (ν.prod (Tier2.tapeMeasure (signParameter d true))).real
      {z | A.output z = false} ≤ 1/10) :
    (ν.prod (Tier2.tapeMeasure (signParameter d false))).real
      {z | A.stop z ≤ n ∧ A.output z = false} ≤ 9/40 := by
  rw [← signTest_prefix_probability ν _ A n false]
  apply early_event_probability _ _ (A.prefixEvent n false)
    (A.measurable_prefixEvent n false) (early_prefix_information ν d n hn)
  rw [signTest_prefix_probability]
  have hsub : {z : R × (ℕ → Bool) | A.stop z ≤ n ∧ A.output z = false} ⊆
      {z | A.output z = false} := fun _ hz => hz.2
  exact (measureReal_mono hsub).trans hplus

def entropyLowerTime (d : EntropyGap) : ℕ := ⌊(1/1024 : ℝ)/(d : ℝ)^2⌋₊

/-- The extra one avoids division by zero when the expected work is zero.
The paper's coarser window and information constants still apply. -/
def entropyUpperTime (w : ℝ) : ℕ := ⌈4*w⌉₊ + 1

theorem entropyLowerTime_bounds (d : EntropyGap) :
    (1/2048 : ℝ)/(d : ℝ)^2 ≤ entropyLowerTime d ∧
    (entropyLowerTime d : ℝ)*(d : ℝ)^2 ≤ 1/1024 := by
  have hd : 0 < (d : ℝ)^2 := sq_pos_of_pos d.property.1
  have hx : 2 ≤ (1/1024 : ℝ)/(d : ℝ)^2 := by
    apply (le_div_iff₀ hd).mpr
    have hs := mul_nonneg (show 0 ≤ 1/128-(d : ℝ) by linarith [d.property.2])
      (show 0 ≤ 1/128+(d : ℝ) by linarith [d.property.1])
    nlinarith
  have hf := Nat.floor_le (show 0 ≤ (1/1024 : ℝ)/(d : ℝ)^2 by positivity)
  have hlt := Nat.lt_floor_add_one ((1/1024 : ℝ)/(d : ℝ)^2)
  constructor
  · change _ ≤ (⌊(1/1024 : ℝ)/(d : ℝ)^2⌋₊ : ℝ)
    have he : (1/2048 : ℝ)/(d : ℝ)^2 = ((1/1024 : ℝ)/(d : ℝ)^2)/2 := by ring
    rw [he]
    linarith
  · exact (le_div_iff₀ hd).mp hf

theorem entropyUpperTime_bounds (w : ℝ) (hw : 0 ≤ w) :
    0 < entropyUpperTime w ∧ 4*w ≤ (entropyUpperTime w : ℝ) ∧
      (entropyUpperTime w : ℝ) < 4*w+2 := by
  have h1 := Nat.le_ceil (4*w)
  have h2 := Nat.ceil_lt_add_one (show 0 ≤ 4*w by positivity)
  simp only [entropyUpperTime, Nat.cast_add, Nat.cast_one]
  exact ⟨by omega, by linarith, by linarith⟩

theorem signTest_quarter_late {R : Type} [MeasurableSpace R]
    (ν : Measure R) [IsProbabilityMeasure ν] (p : unitInterval) (A : SignTest R)
    (hfinite : expectedSignTestWork ν p A ≠ ∞) :
    (ν.prod (Tier2.tapeMeasure p)).real
      {z | (entropyUpperTime (expectedSignTestWork ν p A).toReal : ℕ∞) < A.stop z} ≤ 1/4 := by
  have hu := entropyUpperTime_bounds (expectedSignTestWork ν p A).toReal ENNReal.toReal_nonneg
  have hup : (0 : ℝ) < entropyUpperTime (expectedSignTestWork ν p A).toReal := by exact_mod_cast hu.1
  have hm := signTest_late_probability ν p A
    (entropyUpperTime (expectedSignTestWork ν p A).toReal) hfinite
  nlinarith

/-- The stopping window is populated under the negative law. All probability
bounds are derived from observability, two-sided correctness, and actual work. -/
theorem signTest_negative_window {R : Type} [MeasurableSpace R]
    (ν : Measure R) [IsProbabilityMeasure ν] (A : SignTest R) (d : EntropyGap)
    (hminus : (ν.prod (Tier2.tapeMeasure (signParameter d false))).real
      {z | A.output z = true} ≤ 1/10)
    (hplus : (ν.prod (Tier2.tapeMeasure (signParameter d true))).real
      {z | A.output z = false} ≤ 1/10)
    (hfinite : expectedSignTestWork ν (signParameter d false) A ≠ ∞) :
    (17/40 : ℝ) ≤ (ν.prod (Tier2.tapeMeasure (signParameter d false))).real
      (signTestWindow A (entropyLowerTime d)
        (entropyUpperTime (expectedSignTestWork ν (signParameter d false) A).toReal)) := by
  exact signTest_window_probability _ A _ _ hminus
    (signTest_early_minus ν A d _ (entropyLowerTime_bounds d).2 hplus)
    (signTest_quarter_late ν _ A hfinite)

def restrictPrefix {R : Type} (n u : ℕ) (hnu : n ≤ u) :
    R × (Fin u → Bool) → R × (Fin n → Bool) :=
  fun z => (z.1, fun i => z.2 ⟨i.val, lt_of_lt_of_le i.isLt hnu⟩)

def signTestWindowPrefix {R : Type} [MeasurableSpace R]
    (A : SignTest R) (n u : ℕ) (hnu : n ≤ u) : Set (R × (Fin u → Bool)) :=
  A.prefixEvent u false \ (restrictPrefix n u hnu) ⁻¹' A.prefixEvent n false

theorem measurable_signTestWindowPrefix {R : Type} [MeasurableSpace R]
    (A : SignTest R) (n u : ℕ) (hnu : n ≤ u) :
    MeasurableSet (signTestWindowPrefix A n u hnu) := by
  have hm : Measurable (restrictPrefix (R := R) n u hnu) :=
    measurable_fst.prodMk (Measurable.of_eval (fun i : Fin n =>
      (measurable_pi_apply (⟨i.val, lt_of_lt_of_le i.isLt hnu⟩ : Fin u)).comp measurable_snd))
  exact (A.measurable_prefixEvent u false).diff (hm (A.measurable_prefixEvent n false))

theorem signTestWindowPrefix_preimage {R : Type} [MeasurableSpace R]
    (A : SignTest R) (n u : ℕ) (hnu : n ≤ u) :
    (Prod.map id (Tier2.tapePrefix u)) ⁻¹' signTestWindowPrefix A n u hnu =
      signTestWindow A n u := by
  ext z
  change ((z.1, Tier2.tapePrefix u z.2) ∈ A.prefixEvent u false ∧
    ¬ (z.1, Tier2.tapePrefix n z.2) ∈ A.prefixEvent n false) ↔
      A.output z = false ∧ (n : ℕ∞) < A.stop z ∧ A.stop z ≤ u
  rw [A.observable, A.observable]
  constructor
  · rintro ⟨hu, hn⟩
    exact ⟨hu.2, lt_of_not_ge (fun h => hn ⟨h, hu.2⟩), hu.1⟩
  · rintro ⟨hb, hn, hu⟩
    exact ⟨⟨hu, hb⟩, fun h => hn.not_ge h.1⟩

theorem signTestWindowPrefix_probability {R : Type} [MeasurableSpace R]
    (ν : Measure R) [IsProbabilityMeasure ν] (p : unitInterval)
    (A : SignTest R) (n u : ℕ) (hnu : n ≤ u) :
    (ν.prod (Tier2.finiteMeasure p u)).real (signTestWindowPrefix A n u hnu) =
      (ν.prod (Tier2.tapeMeasure p)).real (signTestWindow A n u) := by
  rw [← seeded_tape_prefix_map ν p u,
    map_measureReal_apply (measurable_id.prodMap (Tier2.measurable_prefix u))
      (measurable_signTestWindowPrefix A n u hnu), signTestWindowPrefix_preimage]

theorem signTestWindow_positive_imp_lt {R : Type} [MeasurableSpace R]
    (P : Measure (R × (ℕ → Bool))) (A : SignTest R) (n u : ℕ)
    (hmass : 0 < P.real (signTestWindow A n u)) : n < u := by
  by_contra h
  have hun : (u : ℕ∞) ≤ n := by exact_mod_cast (not_lt.mp h)
  have he : signTestWindow A n u = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro z hz
    exact hz.2.1.not_ge (hz.2.2.trans hun)
  rw [he, measureReal_empty] at hmass
  exact (lt_irrefl 0) hmass

/-- The events in the entropy-packing argument are now derived from an
observable sign test. They all live under the same seeded fair-coin law. -/
theorem signTest_fair_window {R : Type} [MeasurableSpace R]
    (ν : Measure R) [IsProbabilityMeasure ν] (A : SignTest R) (d : EntropyGap)
    (hminus : (ν.prod (Tier2.tapeMeasure (signParameter d false))).real
      {z | A.output z = true} ≤ 1/10)
    (hplus : (ν.prod (Tier2.tapeMeasure (signParameter d true))).real
      {z | A.output z = false} ≤ 1/10)
    (hfinite : expectedSignTestWork ν (signParameter d false) A ≠ ∞) :
    exp (-64*((d : ℝ)^2*(expectedSignTestWork ν (signParameter d false) A).toReal)-8) ≤
      (ν.prod (Tier2.tapeMeasure ⟨1/2, by norm_num⟩)).real
        (signTestWindow A (entropyLowerTime d)
          (entropyUpperTime (expectedSignTestWork ν (signParameter d false) A).toReal)) := by
  let w := (expectedSignTestWork ν (signParameter d false) A).toReal
  let n := entropyLowerTime d
  let u := entropyUpperTime w
  have hmass := signTest_negative_window ν A d hminus hplus hfinite
  have hnu : n ≤ u := (signTestWindow_positive_imp_lt _ A n u
    (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 17/40) hmass)).le
  rw [← signTestWindowPrefix_probability ν _ A n u hnu]
  have hp := signParameter_interior d false
  apply fair_prefix_event_mass_lower ν (signParameter d false) hp.1 hp.2 u ((d : ℝ)^2*w)
  · have hu := entropyUpperTime_bounds w (ENNReal.toReal_nonneg)
    have hd : 0 < (d : ℝ)^2 := sq_pos_of_pos d.property.1
    have hmul := mul_le_mul_of_nonneg_right hu.2.2.le hd.le
    have hs := mul_nonneg (show 0 ≤ 1/128-(d : ℝ) by linarith [d.property.2])
      (show 0 ≤ 1/128+(d : ℝ) by linarith [d.property.1])
    change (u : ℝ)*((1/2 + -(d : ℝ))-1/2)^2 ≤ 4*((d : ℝ)^2*w)+1/4
    dsimp [u] at *
    nlinarith
  · exact measurable_signTestWindowPrefix A n u hnu
  · rw [signTestWindowPrefix_probability]
    exact le_trans (by norm_num : (1/4 : ℝ) ≤ 17/40) hmass

/-- On a path which stops after `k` flips, each low-cost window lies in a
common scale interval. This is the bridge to geometric overlap counting. -/
theorem signTest_window_scale {R : Type} [MeasurableSpace R]
    (ν : Measure R) (A : SignTest R) (d : EntropyGap)
    (z : R × (ℕ → Bool)) (k : ℕ) (hk : A.stop z = k)
    (c : ℝ) (hcost : (d : ℝ)^2*(expectedSignTestWork ν (signParameter d false) A).toReal ≤ 2*c)
    (hmem : z ∈ signTestWindow A (entropyLowerTime d)
      (entropyUpperTime (expectedSignTestWork ν (signParameter d false) A).toReal)) :
    (1/2048 : ℝ)*(1/(d : ℝ)^2) ≤ k ∧ (k : ℝ) ≤ (8*c+1)*(1/(d : ℝ)^2) := by
  let w := (expectedSignTestWork ν (signParameter d false) A).toReal
  have hn : entropyLowerTime d < k := by
    have h := hmem.2.1
    rw [hk] at h
    exact_mod_cast h
  have hu : k ≤ entropyUpperTime w := by
    have h := hmem.2.2
    rw [hk] at h
    exact_mod_cast h
  have hnr : (entropyLowerTime d : ℝ) ≤ k := by exact_mod_cast hn.le
  have hur : (k : ℝ) ≤ entropyUpperTime w := by exact_mod_cast hu
  have hbounds := entropyUpperTime_bounds w ENNReal.toReal_nonneg
  have hd : 0 < (d : ℝ)^2 := sq_pos_of_pos d.property.1
  constructor
  · simpa only [mul_one_div] using (entropyLowerTime_bounds d).1.trans hnr
  · rw [mul_one_div]
    apply (le_div_iff₀ hd).mpr
    have hmul := mul_le_mul_of_nonneg_right (hur.trans hbounds.2.2.le) hd.le
    have hs := mul_nonneg (show 0 ≤ 1/128-(d : ℝ) by linarith [d.property.2])
      (show 0 ≤ 1/128+(d : ℝ) by linarith [d.property.1])
    change (d : ℝ)^2*w ≤ 2*c at hcost
    nlinarith

end ThresholdHC.CriticalEntropy
