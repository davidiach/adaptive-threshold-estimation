import ThresholdHC.UnknownRarity.Specification
import ThresholdHC.NonnegativeUnbiased.Support

/-! Null-set transfer for stopped transcripts at interior gaps.

When every gap lies strictly between `0` and `1/2`, both coin biases `1/2 ± d`
lie strictly between zero and one, so a finite transcript that has positive
probability under one sign prior has positive probability under every sign
prior (`support_interior`). Once the policy stops, a valid tape stays empty,
so membership of the seed and tape in a measurable set is read from a finite
prefix. Hence a set that is null under one sign law is null under any sign law
at which the algorithm stops almost surely (`null_transfer`). This adapts
`NonnegativeUnbiased.nonnegative_not_unbiased`, with an arbitrary measurable
set in place of the nonzero-output event and arbitrary priors in place of the
two fixed ones. -/
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace ThresholdHC.UnknownRarity
open ThresholdHC ThresholdHC.Tier3 ThresholdHC.Tier4 ThresholdHC.Tier5 ThresholdHC.Tier6
open ThresholdHC.Proofs

/-- At interior gaps, every transcript possible under one prior in `[0,1]` is
possible under every prior in `[0,1]`. -/
theorem support_interior {n : ℕ} (pol : List Bool → Option ℕ) (d : ℕ → ℝ)
    (hd : ∀ i, 0 < d i ∧ d i < 1/2) (q v : ℕ → ℝ) (hq : ∀ i, 0 ≤ q i ∧ q i ≤ 1)
    (hv : ∀ i, 0 ≤ v i ∧ v i ≤ 1) (w : Prefix n)
    (h1 : creationLaw pol d v w ≠ 0) : creationLaw pol d q w ≠ 0 := by
  unfold creationLaw at *
  rw [transcriptLaw_factor] at *
  obtain ⟨hval, hp⟩ := mul_ne_zero_iff.mp h1
  refine mul_ne_zero hval ?_
  rw [Finset.prod_ne_zero_iff] at *
  intro i hi
  have hpi := hp i hi
  have hdi := hd i.val
  have hqi := hq i.val
  have hvi := hv i.val
  have ha0 := coinLike_nonneg (capPolicy (coinCap n pol) pol) w i
    (p := 1/2 + d i.val) (by linarith) (by linarith)
  have hb0 := coinLike_nonneg (capPolicy (coinCap n pol) pol) w i
    (p := 1/2 - d i.val) (by linarith) (by linarith)
  have hab : coinLike (capPolicy (coinCap n pol) pol) w i (1/2 + d i.val) ≠ 0 ∨
      coinLike (capPolicy (coinCap n pol) pol) w i (1/2 - d i.val) ≠ 0 := by
    by_contra hcon
    push Not at hcon
    apply hpi
    rw [hcon.1, hcon.2]
    ring
  have ha : coinLike (capPolicy (coinCap n pol) pol) w i (1/2 + d i.val) ≠ 0 :=
    hab.elim id (fun hb => NonnegativeUnbiased.coinLike_ne_zero _ _ _
      ⟨by linarith, by linarith⟩ hb)
  have hb : coinLike (capPolicy (coinCap n pol) pol) w i (1/2 - d i.val) ≠ 0 :=
    hab.elim (fun ha => NonnegativeUnbiased.coinLike_ne_zero _ _ _
      ⟨by linarith, by linarith⟩ ha) id
  have hapos := lt_of_le_of_ne ha0 (Ne.symm ha)
  have hbpos := lt_of_le_of_ne hb0 (Ne.symm hb)
  have hsum : 0 < q i.val * coinLike (capPolicy (coinCap n pol) pol) w i (1/2 + d i.val) +
      (1 - q i.val) * coinLike (capPolicy (coinCap n pol) pol) w i (1/2 - d i.val) := by
    rcases lt_or_eq_of_le hqi.1 with hq0 | hq0
    · exact add_pos_of_pos_of_nonneg (mul_pos hq0 hapos)
        (mul_nonneg (by linarith) hb0)
    · rw [← hq0]
      simp only [zero_mul, sub_zero, one_mul, zero_add]
      exact hbpos
  exact hsum.ne'

/-- Under the gap law `dirac g`, every fresh coin has gap `g` almost surely. -/
theorem dirac_gap_ae {R : Type} [MeasurableSpace R] (A : AdaptiveEstimator R) (g : Gap) :
    ∀ᵐ u ∂populationSeedLaw (Measure.dirac g) A, ∀ i, ((u.2 i : Gap) : ℝ) = g := by
  have hmap : Measurable (fun u : R => (u, fun _ : ℕ => g)) :=
    measurable_id.prodMk measurable_const
  have hS : MeasurableSet {u : PopulationSeed R | ∀ i, ((u.2 i : Gap) : ℝ) = g} := by
    rw [Set.ofPred_forall]
    exact MeasurableSet.iInter fun i => measurableSet_eq_fun
      (measurable_subtype_coe.comp ((measurable_pi_apply i).comp measurable_snd)) measurable_const
  rw [populationSeedLaw, Measure.infinitePi_dirac, Measure.prod_dirac,
    ae_map_iff hmap.aemeasurable hS]
  exact ae_of_all _ (fun _ _ => rfl)

open Classical in
/-- The indicator, read from a prefix of length `n`, that the policy has
stopped and the seed with the padded tape lies in `S`. -/
def setEvent {R : Type} [MeasurableSpace R] (A : AdaptiveEstimator R) (S : Set (R × ProcessTape))
    (n : ℕ) (u : PopulationSeed R) (w : Prefix n) : ℝ :=
  if A.policy u.1 (NonnegativeUnbiased.hist w) = none ∧ (u.1, NonnegativeUnbiased.pad w) ∈ S
  then 1 else 0

theorem setEvent_measurable {R : Type} [MeasurableSpace R] (A : AdaptiveEstimator R)
    {S : Set (R × ProcessTape)} (hS : MeasurableSet S) (n : ℕ) (w : Prefix n) :
    Measurable (fun u : PopulationSeed R => setEvent A S n u w) := by
  classical
  have hT : MeasurableSet {u : PopulationSeed R |
      A.policy u.1 (NonnegativeUnbiased.hist w) = none ∧ (u.1, NonnegativeUnbiased.pad w) ∈ S} :=
    (measurable_fst (A.policy_measurable (NonnegativeUnbiased.hist w) none)).inter
      ((measurable_fst.prodMk measurable_const) hS)
  unfold setEvent
  exact Measurable.ite hT measurable_const measurable_const

theorem setEvent_bound {R : Type} [MeasurableSpace R] (A : AdaptiveEstimator R)
    (S : Set (R × ProcessTape)) (n : ℕ) (u : PopulationSeed R) (w : Prefix n) :
    0 ≤ setEvent A S n u w ∧ setEvent A S n u w ≤ 1 := by
  unfold setEvent; split_ifs <;> norm_num

theorem setEvent_joint {R : Type} [MeasurableSpace R] (A : AdaptiveEstimator R)
    {S : Set (R × ProcessTape)} (hS : MeasurableSet S) (n : ℕ) :
    Measurable (fun z : PopulationSeed R × ProcessTape =>
      setEvent A S n z.1 (processPrefix n z.2)) := by
  have hF : Measurable (fun p : PopulationSeed R × Prefix n => setEvent A S n p.1 p.2) :=
    measurable_from_prod_countable_left (fun w => setEvent_measurable A hS n w)
  exact hF.comp (measurable_jointPrefix n)

/-- A measurable set of seeds and tapes that is null under the sign law `q` is
null under every sign law `v` at which the algorithm stops almost surely,
provided all gaps lie below `1/2` almost surely. -/
theorem null_transfer {R : Type} [MeasurableSpace R] (μ : Measure Gap) [IsProbabilityMeasure μ]
    (A : AdaptiveEstimator R)
    (hgap : ∀ᵐ u ∂populationSeedLaw μ A, ∀ i, ((u.2 i : Gap) : ℝ) < 1/2)
    (q v : SignLaw)
    (hstop : ∀ᵐ z ∂experimentLaw μ A v, ∃ n, A.policy z.1.1 (processHistory z.2 n) = none)
    (S : Set (R × ProcessTape)) (hS : MeasurableSet S)
    (h0 : ∀ᵐ z ∂experimentLaw μ A q, (z.1.1, z.2) ∉ S) :
    ∀ᵐ z ∂experimentLaw μ A v, (z.1.1, z.2) ∉ S := by
  classical
  -- Every stopped transcript whose padded tape lies in `S` has probability zero under `v`.
  have hE : ∀ n, ∀ᵐ z ∂experimentLaw μ A v, setEvent A S n z.1 (processPrefix n z.2) = 0 := by
    intro n
    have real (r : SignLaw) := (population_realization R μ A r).2 n (setEvent A S n)
      (fun w => setEvent_measurable A hS n w)
      ⟨1, fun u w => by
        have hb := setEvent_bound A S n u w
        rw [abs_le]; constructor <;> linarith [hb.1, hb.2]⟩
    have hzero0 : (∫ z, setEvent A S n z.1 (processPrefix n z.2) ∂experimentLaw μ A q) = 0 := by
      apply integral_eq_zero_of_ae
      filter_upwards [h0, StoppingProgram.original_path_valid μ A q] with z hz hv
      change setEvent A S n z.1 (processPrefix n z.2) = 0
      unfold setEvent
      rw [ite_eq_right_iff]
      rintro ⟨hs, ho⟩
      rw [NonnegativeUnbiased.pad_prefix (A.policy z.1.1) z.2 hv n hs] at ho
      exact absurd ho hz
    rw [real q] at hzero0
    let G (r : SignLaw) (u : PopulationSeed R) := ∑ w : Prefix n,
      creationLaw (populationPolicy A u) (populationGap u) (populationPrior r u) w *
        setEvent A S n u w
    have cnn (r : SignLaw) (u : PopulationSeed R) := (creationLaw_total n (populationPolicy A u)
      (populationGap u) (populationPrior r u) (populationGap_range u) (populationPrior_range r u))
    have Gm (r : SignLaw) : Measurable (G r) := Finset.measurable_sum _ fun w _ =>
      (measurable_creationLaw _ (measurable_populationPolicy A) _ _ measurable_populationGap
        (measurable_populationPrior r) w).mul (setEvent_measurable A hS n w)
    have Gnn (r : SignLaw) (u : PopulationSeed R) : 0 ≤ G r u := Finset.sum_nonneg fun w _ =>
      mul_nonneg ((cnn r u).1 w) (setEvent_bound A S n u w).1
    have Gle (r : SignLaw) (u : PopulationSeed R) : G r u ≤ 1 := by
      calc G r u ≤ ∑ w : Prefix n,
            creationLaw (populationPolicy A u) (populationGap u) (populationPrior r u) w * 1 :=
            Finset.sum_le_sum fun w _ =>
              mul_le_mul_of_nonneg_left (setEvent_bound A S n u w).2 ((cnn r u).1 w)
        _ = 1 := by simp only [mul_one]; exact (cnn r u).2
    have Gi (r : SignLaw) : Integrable (G r) (populationSeedLaw μ A) :=
      (integrable_const (1:ℝ)).mono' (Gm r).aestronglyMeasurable (ae_of_all _ fun u => by
        rw [Real.norm_eq_abs, abs_of_nonneg (Gnn r u)]; exact Gle r u)
    have hG0 : G q =ᵐ[populationSeedLaw μ A] 0 :=
      (integral_eq_zero_iff_of_nonneg (Gnn q) (Gi q)).1 hzero0
    have hG1 : G v =ᵐ[populationSeedLaw μ A] 0 := by
      filter_upwards [hG0, hgap] with u hu0 hgu
      have hterms := (Finset.sum_eq_zero_iff_of_nonneg (fun w _ =>
        mul_nonneg ((cnn q u).1 w) (setEvent_bound A S n u w).1)).1 hu0
      apply Finset.sum_eq_zero
      intro w _
      by_cases hf : setEvent A S n u w = 0
      · rw [hf, mul_zero]
      · have hc0 : creationLaw (populationPolicy A u) (populationGap u)
            (populationPrior q u) w = 0 := by
          rcases mul_eq_zero.1 (hterms w (Finset.mem_univ w)) with h | h
          · exact h
          · exact absurd h hf
        have hc1 : creationLaw (populationPolicy A u) (populationGap u)
            (populationPrior v u) w = 0 := by
          by_contra hne
          exact support_interior (populationPolicy A u) (populationGap u)
            (fun i => ⟨(u.2 i).property.1, hgu i⟩) (populationPrior q u) (populationPrior v u)
            (populationPrior_range q u) (populationPrior_range v u) w hne hc0
        rw [hc1, zero_mul]
    have hint1 : (∫ z, setEvent A S n z.1 (processPrefix n z.2) ∂experimentLaw μ A v) = 0 := by
      rw [real v]
      exact (integral_congr_ae hG1).trans (by simp)
    have hi1 : Integrable (fun z : PopulationSeed R × ProcessTape =>
        setEvent A S n z.1 (processPrefix n z.2)) (experimentLaw μ A v) :=
      (integrable_const (1:ℝ)).mono' (setEvent_joint A hS n).aestronglyMeasurable
        (ae_of_all _ fun z => by
          have hb := setEvent_bound A S n z.1 (processPrefix n z.2)
          rw [Real.norm_eq_abs, abs_of_nonneg hb.1]; exact hb.2)
    exact (integral_eq_zero_iff_of_nonneg
      (fun z : PopulationSeed R × ProcessTape => (setEvent_bound A S n z.1 (processPrefix n z.2)).1)
      hi1).1 hint1
  -- Since the algorithm stops almost surely under `v`, the seed and tape avoid `S`.
  filter_upwards [ae_all_iff.2 hE, hstop, StoppingProgram.original_path_valid μ A v]
    with z hz hs hv
  obtain ⟨n, hn⟩ := hs
  have hzn := hz n
  unfold setEvent at hzn
  rw [ite_eq_right_iff] at hzn
  intro hmem
  exact one_ne_zero (hzn ⟨hn, by
    rw [NonnegativeUnbiased.pad_prefix (A.policy z.1.1) z.2 hv n hn]; exact hmem⟩)

/-- At a point-mass gap `g < 1/2`, the transfer applies to every pair of sign laws. -/
theorem dirac_null_transfer {R : Type} [MeasurableSpace R] (g : Gap) (hg : (g : ℝ) < 1/2)
    (A : AdaptiveEstimator R) (q v : SignLaw)
    (hstop : ∀ᵐ z ∂experimentLaw (Measure.dirac g) A v,
      ∃ n, A.policy z.1.1 (processHistory z.2 n) = none)
    (S : Set (R × ProcessTape)) (hS : MeasurableSet S)
    (h0 : ∀ᵐ z ∂experimentLaw (Measure.dirac g) A q, (z.1.1, z.2) ∉ S) :
    ∀ᵐ z ∂experimentLaw (Measure.dirac g) A v, (z.1.1, z.2) ∉ S := by
  have hgap : ∀ᵐ u ∂populationSeedLaw (Measure.dirac g) A, ∀ i, ((u.2 i : Gap) : ℝ) < 1/2 := by
    filter_upwards [dirac_gap_ae A g] with u hu i
    rw [hu i]
    exact hg
  exact null_transfer (Measure.dirac g) A hgap q v hstop S hS h0

theorem stopped_transcript_ac_proof : StoppedTranscriptACStatement := by
  intro d hd R _ A q v hstop
  have hm : Measurable (fun z : PopulationSeed R × ProcessTape => (z.1.1, z.2)) :=
    measurable_fst.fst.prodMk measurable_snd
  refine Measure.AbsolutelyContinuous.mk fun S hS h0 => ?_
  rw [Measure.map_apply hm hS] at h0 ⊢
  have hq : ∀ᵐ z ∂experimentLaw (Measure.dirac d) A q, (z.1.1, z.2) ∉ S := by
    rw [ae_iff]
    simp only [not_not]
    exact h0
  have hv := dirac_null_transfer d hd A q v hstop S hS hq
  rw [ae_iff] at hv
  simp only [not_not] at hv
  exact hv

/-- Finite expected work implies almost-sure stopping (Tier 5 `creation_stops`). -/
theorem stops_of_expectedWork {R : Type} [MeasurableSpace R] (μ : Measure Gap)
    [IsProbabilityMeasure μ] (A : AdaptiveEstimator R) (q : SignLaw)
    (hw : expectedWork μ A q < ∞) :
    ∀ᵐ z ∂experimentLaw μ A q, ∃ n, A.policy z.1.1 (processHistory z.2 n) = none :=
  Tier5.creation_stops (PopulationSeed R) (PopulationSeed R × ProcessTape)
    (populationSeedLaw μ A) (experimentLaw μ A q) Prod.fst Prod.snd (populationPolicy A)
    populationGap (populationPrior q) measurable_fst RareAboveTwo.observable_tape_measurable
    (measurable_populationPolicy A) (population_realization R μ A q).2 hw

end ThresholdHC.UnknownRarity
