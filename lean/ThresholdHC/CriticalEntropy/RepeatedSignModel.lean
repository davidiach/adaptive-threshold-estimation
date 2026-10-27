import ThresholdHC.CriticalEntropy.RepeatedModel
import ThresholdHC.CriticalEntropy.SignTest

/-!
The repeated real-output estimator induces an observable sign test. Its
threshold and repetition count are fixed before any flips; neither the gap
nor the sign is supplied to the policy. Prefix legality is proved pointwise.
-/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace ThresholdHC.CriticalEntropy

theorem stopped_before_prefix_ext {R E : Type} [MeasurableSpace R] [MeasurableSpace E]
    (A : StoppedProcedure R E) (r : R) (ω ω' : ℕ → Bool) (n : ℕ)
    (h : Tier2.tapePrefix n ω = Tier2.tapePrefix n ω')
    (hle : A.stop (r,ω) ≤ n) :
    A.stop (r,ω') = A.stop (r,ω) ∧ A.output (r,ω') = A.output (r,ω) := by
  have hfinite : A.stop (r,ω) ≠ ⊤ := by
    intro ht
    simp only [ht, top_le_iff, ENat.natCast_ne_top] at hle
  obtain ⟨k,hk⟩ := ENat.ne_top_iff_exists.mp hfinite
  have hk' : (k : ℕ∞) ≤ n := by rw [hk]; exact hle
  have hkn : k ≤ n := by exact_mod_cast hk'
  obtain ⟨hs,ho⟩ := stopped_prefix_ext A r ω ω' k (prefix_eq_restrict h hkn) hk.symm
  exact ⟨hs.trans hk,ho⟩

def stoppedToSignTest {R : Type} [MeasurableSpace R]
    (A : StoppedProcedure R Bool) : SignTest R where
  stop := A.stop
  output := A.output
  measurable_stop := A.measurable_stop
  measurable_output := A.measurable_output
  prefixEvent := fun n b => {z | A.stop (z.1,completePrefix n z.2) ≤ n ∧
    A.output (z.1,completePrefix n z.2) = b}
  measurable_prefixEvent := by
    intro n b
    have hg : Measurable (fun z : R × (Fin n → Bool) => (z.1,completePrefix n z.2)) :=
      measurable_fst.prodMk ((measurable_completePrefix n).comp measurable_snd)
    exact ((A.measurable_stop.comp hg)
      (Set.to_countable {t : ℕ∞ | t ≤ n}).measurableSet).inter
      (measurableSet_eq_fun (A.measurable_output.comp hg) measurable_const)
  observable := by
    intro n b z
    change (A.stop (z.1,completePrefix n (Tier2.tapePrefix n z.2)) ≤ n ∧
      A.output (z.1,completePrefix n (Tier2.tapePrefix n z.2)) = b) ↔
      A.stop z ≤ n ∧ A.output z = b
    have hp := tapePrefix_completePrefix n (Tier2.tapePrefix n z.2)
    constructor
    · rintro ⟨ht,ho⟩
      obtain ⟨hs,he⟩ := stopped_before_prefix_ext A z.1 _ z.2 n hp ht
      exact ⟨hs ▸ ht, he.trans ho⟩
    · rintro ⟨ht,ho⟩
      obtain ⟨hs,he⟩ := stopped_before_prefix_ext A z.1 z.2 _ n hp.symm ht
      exact ⟨hs ▸ ht, he.trans ho⟩

def repeatedSignDecision (n : ℕ) (t : ℝ) (x : Fin n → ℝ) : Bool :=
  if (n : ℝ)*t < ∑ i, x i then true else false

theorem measurable_repeatedSignDecision (n : ℕ) (t : ℝ) :
    Measurable (repeatedSignDecision n t) := by
  unfold repeatedSignDecision
  exact Measurable.ite (measurableSet_lt measurable_const (by fun_prop))
    measurable_const measurable_const

def repeatedSignTest {R : Type} [MeasurableSpace R]
    (A : StoppedProcedure R ℝ) (n : ℕ) (t : ℝ) : SignTest (Fin n → R) :=
  stoppedToSignTest (postprocessProcedure (repeatedProcedure A n)
    (repeatedSignDecision n t) (measurable_repeatedSignDecision n t))

end ThresholdHC.CriticalEntropy
