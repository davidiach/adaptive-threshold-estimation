import ThresholdHC.AnytimeLower.ObservedTesting

/-!
First-crossing testing with threshold two thirds of the displacement.

These are copies of the first-crossing lemmas of `ThresholdHC.AnytimeLower`
with two changes: the one-sided event bound is kept in the form
`exp (-(K+log 2)/(1-delta)) <= Q(s)`, valid for every `delta < 1`, and the
crossing threshold is `theta + 2 a/3`, so that every half-width below `a/3`
is detected. The separation `3 a_k <= a_i` for `i < k` is unchanged.
-/

noncomputable section
open MeasureTheory InformationTheory Real Set Filter
open scoped ENNReal Topology
namespace ThresholdHC.BernoulliTimeUniform
open ThresholdHC.Tier3 ThresholdHC.Tier6 ThresholdHC.RareAboveTwo ThresholdHC.AnytimeLower

/-- A high-power event cannot be too rare under a law with bounded KL,
for every confidence level `delta < 1`. -/
theorem event_log_lower {Ω : Type} [MeasurableSpace Ω]
    (P Q : Measure Ω) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (s : Set Ω) (hs : MeasurableSet s) {δ K : ℝ}
    (hd : δ < 1) (hK : 0 ≤ K)
    (hP : 1-δ ≤ P.real s) (hkl : klDiv P Q ≤ ENNReal.ofReal K) :
    exp (-(K+log 2)/(1-δ)) ≤ Q.real s := by
  classical
  have hδ : 0 < 1-δ := by linarith
  have hlog2 : 0 ≤ log 2 := log_nonneg (by norm_num)
  have hac := (klDiv_ne_top_iff.mp (ne_of_lt (hkl.trans_lt ENNReal.ofReal_lt_top))).1
  have hQpos : 0 < Q.real s := by
    by_contra hn
    have hq : Q.real s = 0 := le_antisymm (not_lt.mp hn) measureReal_nonneg
    have hp : P.real s = 0 := (measureReal_eq_zero_iff).mpr (hac ((measureReal_eq_zero_iff).mp hq))
    linarith
  have hQone : Q.real s ≤ 1 := measureReal_le_one
  by_cases hQeq : Q.real s = 1
  · rw [hQeq]
    exact exp_le_one_iff.mpr (div_nonpos_of_nonpos_of_nonneg (by linarith) hδ.le)
  have hQlt : Q.real s < 1 := lt_of_le_of_ne hQone hQeq
  let test : Ω → Bool := fun x => decide (x ∈ s)
  have htrue : test ⁻¹' {true} = s := by ext x; simp [test]
  have hfalse : test ⁻¹' {false} = sᶜ := by ext x; simp [test]
  have htest : Measurable test := by
    apply measurable_to_bool
    rw [htrue]
    exact hs
  have hmapQ (b : Bool) : 0 < (Q.map test) {b} := by
    rw [Measure.map_apply htest (measurableSet_singleton b)]
    cases b
    · rw [hfalse]
      apply ENNReal.toReal_pos_iff.mp ?_ |>.1
      change 0 < Q.real sᶜ
      rw [probReal_compl_eq_one_sub hs]
      linarith
    · rw [htrue]
      exact (ENNReal.toReal_pos_iff.mp hQpos).1
  have hmap (M : Measure Ω) (b : Bool) :
      (M.map test).real {b} = if b then M.real s else M.real sᶜ := by
    rw [map_measureReal_apply htest (measurableSet_singleton b)]
    cases b <;> simp [htrue,hfalse]
  have hid : klDiv (P.map test) (Q.map test) = ENNReal.ofReal (klB (P.real s) (Q.real s)) := by
    rw [klDiv_finite_of_positive (P.map test) (Q.map test) hmapQ]
    simp only [Fintype.sum_bool,hmap,Bool.false_eq_true,↓reduceIte]
    rw [probReal_compl_eq_one_sub hs,probReal_compl_eq_one_sub hs]
    rfl
  have hk : klB (P.real s) (Q.real s) ≤ K := by
    apply (ENNReal.ofReal_le_ofReal_iff hK).mp
    rw [← hid]
    exact (klDiv_map_le P Q htest).trans hkl
  have hb := binary_event_log_bound (p := P.real s) ⟨measureReal_nonneg,measureReal_le_one⟩ ⟨hQpos,hQlt⟩
  have hlq : log (Q.real s) ≤ 0 := log_nonpos hQpos.le hQone
  have hm := mul_le_mul_of_nonneg_right hP (neg_nonneg.mpr hlq)
  have hl : -(K+log 2)/(1-δ) ≤ log (Q.real s) := by
    apply (div_le_iff₀ hδ).mpr
    nlinarith only [hm,hb,hk]
  have he := exp_le_exp.mpr hl
  rwa [exp_log hQpos] at he

/-- Disjoint first-crossing events, each readable from its own observed
prefix, cost at most the total error probability of the reference law. -/
theorem crossing_information_budget {Ω : Type} [MeasurableSpace Ω]
    {X : ℕ → Type} [∀ k, MeasurableSpace (X k)]
    (Q : Measure Ω) [IsProbabilityMeasure Q]
    (P : ℕ → Measure Ω) [∀ k, IsProbabilityMeasure (P k)]
    (E : ℕ → Set Ω) (hE : ∀ k, MeasurableSet (E k))
    (obs : ∀ k, Ω → X k) (hobs : ∀ k, Measurable (obs k))
    (A : ∀ k, Set (X k)) (hA : ∀ k, MeasurableSet (A k))
    (hread : ∀ k, obs k ⁻¹' A k = firstCrossing E k)
    {δ : ℝ} (hd : δ < 1) (K : ℕ → ℝ) (hK : ∀ k, 0 ≤ K k)
    (hpower : ∀ k, 1-δ ≤ (P k).real (firstCrossing E k))
    (herror : Q.real (⋃ k, E k) ≤ δ)
    (hkl : ∀ k, klDiv ((P k).map (obs k)) (Q.map (obs k)) ≤ ENNReal.ofReal (K k))
    (s : Finset ℕ) :
    ∑ k ∈ s, exp (-(K k+log 2)/(1-δ)) ≤ δ := by
  have htest (k : ℕ) : exp (-(K k+log 2)/(1-δ)) ≤ Q.real (firstCrossing E k) := by
    let : IsProbabilityMeasure (Q.map (obs k)) :=
      (Measure.isProbabilityMeasure_map_iff (hobs k).aemeasurable).2 inferInstance
    let : IsProbabilityMeasure ((P k).map (obs k)) :=
      (Measure.isProbabilityMeasure_map_iff (hobs k).aemeasurable).2 inferInstance
    have hp : 1-δ ≤ ((P k).map (obs k)).real (A k) := by
      rw [map_measureReal_apply (hobs k) (hA k),hread k]
      exact hpower k
    have ht := event_log_lower ((P k).map (obs k)) (Q.map (obs k))
      (A k) (hA k) hd (hK k) hp (hkl k)
    simpa [map_measureReal_apply (hobs k) (hA k),hread k] using ht
  exact (Finset.sum_le_sum (s := s) (fun k _ => htest k)).trans
    ((sum_firstCrossing_le Q E hE s).trans herror)

theorem crossing_information_summable {Ω : Type} [MeasurableSpace Ω]
    {X : ℕ → Type} [∀ k, MeasurableSpace (X k)]
    (Q : Measure Ω) [IsProbabilityMeasure Q]
    (P : ℕ → Measure Ω) [∀ k, IsProbabilityMeasure (P k)]
    (E : ℕ → Set Ω) (hE : ∀ k, MeasurableSet (E k))
    (obs : ∀ k, Ω → X k) (hobs : ∀ k, Measurable (obs k))
    (A : ∀ k, Set (X k)) (hA : ∀ k, MeasurableSet (A k))
    (hread : ∀ k, obs k ⁻¹' A k = firstCrossing E k)
    {δ : ℝ} (hd : δ < 1) (K : ℕ → ℝ) (hK : ∀ k, 0 ≤ K k)
    (hpower : ∀ k, 1-δ ≤ (P k).real (firstCrossing E k))
    (herror : Q.real (⋃ k, E k) ≤ δ)
    (hkl : ∀ k, klDiv ((P k).map (obs k)) (Q.map (obs k)) ≤ ENNReal.ofReal (K k)) :
    Summable (fun k => exp (-(K k+log 2)/(1-δ))) :=
  summable_of_sum_le (fun _ => (exp_pos _).le)
    (crossing_information_budget Q P E hE obs hobs A hA hread hd K hK hpower herror hkl)

/-- Crossing events at two thirds of each displacement. -/
def twoThirdEvents {Ω : Type} (z : ℕ → Ω → ℝ) (θ : ℝ) (a : ℕ → ℝ) : ℕ → Set Ω :=
  fun k => {x | θ+2*a k/3 < z k x}

theorem accuracy_firstCrossing_third {Ω : Type} (z : ℕ → Ω → ℝ)
    (θ : ℝ) (a t : ℕ → ℝ)
    (hsep : ∀ i k, i < k → 3*a k ≤ a i) (hw : ∀ i, t i < a i/3)
    (k : ℕ) (x : Ω) (hx : ∀ i, |z i x-(θ+a k)| ≤ t i) :
    x ∈ firstCrossing (twoThirdEvents z θ a) k := by
  rw [mem_firstCrossing]
  constructor
  · have hh := (abs_le.mp (hx k)).1
    change θ+2*a k/3 < z k x
    linarith [hw k]
  · intro i hi
    have hh := (abs_le.mp (hx i)).2
    change ¬θ+2*a i/3 < z i x
    have hs := hsep i k hi
    linarith [hw i]

theorem accuracy_no_crossing_third {Ω : Type} (z : ℕ → Ω → ℝ)
    (θ : ℝ) (a t : ℕ → ℝ) (ha : ∀ i, 0 < a i) (hw : ∀ i, t i < a i/3)
    (x : Ω) (hx : ∀ i, |z i x-θ| ≤ t i) :
    x ∉ ⋃ k, twoThirdEvents z θ a k := by
  intro hm
  obtain ⟨k,hk⟩ := Set.mem_iUnion.mp hm
  have hh := (abs_le.mp (hx k)).2
  change θ+2*a k/3 < z k x at hk
  linarith [hw k,ha k]

theorem separated_third_summable {Ω : Type} [MeasurableSpace Ω]
    {X : ℕ → Type} [∀ k, MeasurableSpace (X k)]
    (Q : Measure Ω) [IsProbabilityMeasure Q]
    (P : ℕ → Measure Ω) [∀ k, IsProbabilityMeasure (P k)]
    (z : ℕ → Ω → ℝ) (hz : ∀ k, Measurable (z k))
    (obs : ∀ k, Ω → X k) (hobs : ∀ k, Measurable (obs k))
    (readback : ∀ k, ℕ → X k → ℝ) (hr : ∀ k i, Measurable (readback k i))
    (hread : ∀ k i, i ≤ k → ∀ x, readback k i (obs k x) = z i x)
    (θ : ℝ) (a t : ℕ → ℝ) (ha : ∀ i, 0 < a i)
    (hsep : ∀ i k, i < k → 3*a k ≤ a i) (hw : ∀ i, t i < a i/3)
    {δ : ℝ} (hd : δ < 1)
    (hbase : 1-δ ≤ Q.real {x | ∀ i, |z i x-θ| ≤ t i})
    (halt : ∀ k, 1-δ ≤ (P k).real {x | ∀ i, |z i x-(θ+a k)| ≤ t i})
    (K : ℕ → ℝ) (hK : ∀ k, 0 ≤ K k)
    (hkl : ∀ k, klDiv ((P k).map (obs k)) (Q.map (obs k)) ≤ ENNReal.ofReal (K k)) :
    Summable (fun k => exp (-(K k+log 2)/(1-δ))) := by
  let E := twoThirdEvents z θ a
  have hE (k : ℕ) : MeasurableSet (E k) :=
    measurableSet_lt measurable_const (hz k)
  let A (k : ℕ) := firstCrossing (twoThirdEvents (readback k) θ a) k
  have hA (k : ℕ) : MeasurableSet (A k) :=
    measurableSet_firstCrossing _ (fun i => measurableSet_lt measurable_const (hr k i)) k
  have hpre (k : ℕ) : obs k ⁻¹' A k = firstCrossing E k := by
    ext x
    simp only [Set.mem_preimage,A,mem_firstCrossing,E,twoThirdEvents,Set.mem_ofPred_eq]
    rw [hread k k le_rfl x]
    constructor <;> rintro ⟨hk,hi⟩ <;> refine ⟨hk,?_⟩
    · intro i hik
      simpa only [hread k i hik.le x] using hi i hik
    · intro i hik
      simpa only [hread k i hik.le x] using hi i hik
  have hp (k : ℕ) : 1-δ ≤ (P k).real (firstCrossing E k) :=
    (halt k).trans (measureReal_mono (fun x hx =>
      accuracy_firstCrossing_third z θ a t hsep hw k x hx))
  have hS : MeasurableSet {x | ∀ i, |z i x-θ| ≤ t i} := by
    simp only [Set.ofPred_forall]
    exact MeasurableSet.iInter (fun i => measurableSet_le ((hz i).sub_const θ).abs measurable_const)
  have he : Q.real (⋃ k, E k) ≤ δ := by
    have hh : (⋃ k, E k) ⊆ {x | ∀ i, |z i x-θ| ≤ t i}ᶜ := by
      intro x hx hg
      exact accuracy_no_crossing_third z θ a t ha hw x hg hx
    have hh' := measureReal_mono (μ := Q) hh
    rw [probReal_compl_eq_one_sub hS] at hh'
    linarith
  exact crossing_information_summable Q P E hE obs hobs A hA hpre hd K hK hp he hkl

theorem separated_third_frequently {Ω : Type} [MeasurableSpace Ω]
    {X : ℕ → Type} [∀ k, MeasurableSpace (X k)]
    (Q : Measure Ω) [IsProbabilityMeasure Q]
    (P : ℕ → Measure Ω) [∀ k, IsProbabilityMeasure (P k)]
    (z : ℕ → Ω → ℝ) (hz : ∀ k, Measurable (z k))
    (obs : ∀ k, Ω → X k) (hobs : ∀ k, Measurable (obs k))
    (readback : ∀ k, ℕ → X k → ℝ) (hr : ∀ k i, Measurable (readback k i))
    (hread : ∀ k i, i ≤ k → ∀ x, readback k i (obs k x) = z i x)
    (θ : ℝ) (a t : ℕ → ℝ) (ha : ∀ i, 0 < a i)
    (hsep : ∀ i k, i < k → 3*a k ≤ a i)
    {δ : ℝ} (hd : δ < 1)
    (hbase : 1-δ ≤ Q.real {x | ∀ i, |z i x-θ| ≤ t i})
    (halt : ∀ k, 1-δ ≤ (P k).real {x | ∀ i, |z i x-(θ+a k)| ≤ t i})
    (K : ℕ → ℝ) (hK : ∀ k, 0 ≤ K k)
    (hkl : ∀ k, klDiv ((P k).map (obs k)) (Q.map (obs k)) ≤ ENNReal.ofReal (K k))
    (hdiv : ¬Summable (fun k => exp (-(K k+log 2)/(1-δ)))) :
    ∃ᶠ k in atTop, a k/3 ≤ t k := by
  by_contra hh
  simp only [not_frequently,not_le] at hh
  obtain ⟨m,hm⟩ := eventually_atTop.mp hh
  have hbase' : 1-δ ≤ Q.real {x | ∀ i, |z (i+m) x-θ| ≤ t (i+m)} :=
    hbase.trans (measureReal_mono (fun _ hx i => hx (i+m)))
  have halt' (k : ℕ) : 1-δ ≤ (P (k+m)).real
      {x | ∀ i, |z (i+m) x-(θ+a (k+m))| ≤ t (i+m)} :=
    (halt (k+m)).trans (measureReal_mono (fun _ hx i => hx (i+m)))
  have hs := separated_third_summable Q (fun k => P (k+m))
    (fun i => z (i+m)) (fun i => hz (i+m))
    (fun k => obs (k+m)) (fun k => hobs (k+m))
    (fun k i => readback (k+m) (i+m)) (fun k i => hr (k+m) (i+m))
    (fun k i hi x => hread (k+m) (i+m) (Nat.add_le_add_right hi m) x)
    θ (fun i => a (i+m)) (fun i => t (i+m)) (fun i => ha (i+m))
    (fun i k hi => hsep (i+m) (k+m) (Nat.add_lt_add_right hi m))
    (fun i => hm (i+m) (Nat.le_add_left m i)) hd hbase' halt'
    (fun k => K (k+m)) (fun k => hK (k+m)) (fun k => hkl (k+m))
  exact hdiv ((summable_nat_add_iff m).mp hs)

/-- The sequential lower bound in the original hidden-gap experiment with
threshold two thirds of each displacement, for every confidence level below
one. -/
theorem observed_third_frequently {R : Type} [MeasurableSpace R]
    (μ : Measure Gap) [IsProbabilityMeasure μ] (A : AdaptiveEstimator R)
    (H : ∀ n, R × Prefix n → ℝ) (hH : ∀ n, Measurable (H n))
    {ρ δ : ℝ} (hd : δ < 1) (t : ℕ → ℝ)
    (hacc : OnlineAccuracy μ A H ρ δ t)
    (q : SignLaw) (hq : RarePrior μ ρ q)
    (r : ℕ → SignLaw) (hr : ∀ k, RarePrior μ ρ (r k))
    (a : ℕ → ℝ) (ha : ∀ k, 0 < a k)
    (hmean : ∀ k, signMean μ (r k).val = signMean μ q.val+a k)
    (hsep : ∀ i k, i < k → 3*a k ≤ a i)
    (N : ℕ → ℕ) (hN : Monotone N)
    (K : ℕ → ℝ) (hK : ∀ k, 0 ≤ K k)
    (hkl : ∀ k, klDiv (observablePrefixLaw μ A (r k) (N k))
      (observablePrefixLaw μ A q (N k)) ≤ ENNReal.ofReal (K k))
    (hdiv : ¬Summable (fun k => exp (-(K k+log 2)/(1-δ)))) :
    ∃ᶠ k in atTop, a k/3 ≤ t (N k) := by
  have hb : 1-δ ≤ (experimentLaw μ A q).real
      {x | ∀ i, |prefixEstimate H (N i) x-signMean μ q.val| ≤ t (N i)} :=
    (hacc q hq).trans (measureReal_mono (fun _ hx i => hx (N i)))
  have hp (k : ℕ) : 1-δ ≤ (experimentLaw μ A (r k)).real
      {x | ∀ i, |prefixEstimate H (N i) x-(signMean μ q.val+a k)| ≤ t (N i)} := by
    rw [← hmean k]
    exact (hacc (r k) (hr k)).trans (measureReal_mono (fun _ hx i => hx (N i)))
  exact separated_third_frequently (experimentLaw μ A q)
    (fun k => experimentLaw μ A (r k))
    (fun k => prefixEstimate H (N k))
    (fun k => (hH _).comp (measurable_prefixData _))
    (fun k => prefixData (N k)) (fun k => measurable_prefixData _)
    (prefixReadback H N hN) (measurable_prefixReadback H hH N hN)
    (prefixReadback_eq H N hN) (signMean μ q.val) a (fun k => t (N k))
    ha hsep hd hb hp K hK hkl hdiv

end ThresholdHC.BernoulliTimeUniform
