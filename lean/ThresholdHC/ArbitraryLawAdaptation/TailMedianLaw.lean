import ThresholdHC.ArbitraryLawAdaptation.TailMedianProbability
import ThresholdHC.ArbitraryLawAdaptation.TailProbeLaw

/-! The median tail certificate on fresh coins of the original population.

`m` probes at depth `J` run on independent streams of coins with the actual
population tape law. For every probability law `μ` of positive gaps and every
measurable gap-dependent sign law, with `F(2^{-J}) = μ((0, 2^{-J}])`:

* except with probability `2 exp(-m/8)`, and hence with probability at least
  `1 - δ` when `m ≥ 8 log(2/δ)`, the median covers `F(2^{-J})` for every choice
  of the probes' flip budgets and coin caps, and at the common budget `b` and
  coin cap `M` it is at most `min{1, 128 max(u_J, W_J/b, 1/M)}`;
* with `b = 4^J` and no active coin cap this is statement (1) of the tail
  certificate;
* with fresh streams at every depth and `m_J ≥ 8 log(2J(J+1)/δ)`, both hold
  at every depth `J ≥ 1` at once with probability at least `1 - δ`.

Splitting one sequence of independent coins by the pairing function gives the
independent streams used here, so the probes and the depths can draw disjoint
coins of a single coin array. -/

noncomputable section
open MeasureTheory Real
namespace ThresholdHC.ArbitraryLawAdaptation
open ThresholdHC.Tier2 ThresholdHC.Tier6 ThresholdHC.CriticalEntropy
open ThresholdHC.ObservableSimulation

/-- Splitting one sequence of independent draws by the pairing function gives a
sequence of independent streams: stream `j` reads the draws `Nat.pair j i`. -/
theorem infinitePi_map_blocks {X : Type*} [MeasurableSpace X] (S : Measure X)
    [IsProbabilityMeasure S] :
    (Measure.infinitePi (fun _ : ℕ => S)).map (fun (ω : ℕ → X) (j i : ℕ) => ω (Nat.pair j i)) =
      Measure.infinitePi (fun _ : ℕ => Measure.infinitePi (fun _ : ℕ => S)) := by
  have h1 := Measure.infinitePi_map_piCongrLeft (X := fun _ : ℕ × ℕ => X)
    (fun _ : ℕ × ℕ => S) Nat.pairEquiv.symm
  have h2 := Measure.infinitePi_map_curry (fun (_ _ : ℕ) => S)
  rw [← h2, ← h1, Measure.map_map (by fun_prop) (by fun_prop)]
  congr 1
  funext ω j i
  simp [MeasurableEquiv.curry, MeasurableEquiv.piCongrLeft, Equiv.piCongrLeft_apply_eq_cast]

/-- Splitting twice gives independent streams for every depth and every probe:
probe `j` of depth `J` reads the draws `Nat.pair J (Nat.pair j i)`. -/
theorem infinitePi_map_depth_blocks {X : Type*} [MeasurableSpace X] (S : Measure X)
    [IsProbabilityMeasure S] :
    (Measure.infinitePi (fun _ : ℕ => S)).map
        (fun (ω : ℕ → X) (J j i : ℕ) => ω (Nat.pair J (Nat.pair j i))) =
      Measure.infinitePi (fun _ : ℕ => Measure.infinitePi (fun _ : ℕ =>
        Measure.infinitePi (fun _ : ℕ => S))) := by
  have hsplit : Measurable (fun (ω : ℕ → X) (j i : ℕ) => ω (Nat.pair j i)) :=
    Measurable.of_eval fun j => Measurable.of_eval fun i => measurable_pi_apply _
  have hcomp : (fun (ω : ℕ → X) (J j i : ℕ) => ω (Nat.pair J (Nat.pair j i))) =
      (fun (x : ℕ → ℕ → X) (J : ℕ) => (fun (ω : ℕ → X) (j i : ℕ) => ω (Nat.pair j i)) (x J)) ∘
        (fun (ω : ℕ → X) (J k : ℕ) => ω (Nat.pair J k)) := rfl
  have hinner : Measurable (fun (x : ℕ → ℕ → X) (J : ℕ) =>
      (fun (ω : ℕ → X) (j i : ℕ) => ω (Nat.pair j i)) (x J)) :=
    Measurable.of_eval fun J => hsplit.comp (measurable_pi_apply J)
  rw [hcomp, ← Measure.map_map hinner hsplit, infinitePi_map_blocks S,
    Measure.infinitePi_map_pi (f := fun _ (ω : ℕ → X) (j i : ℕ) => ω (Nat.pair j i)) _
      (fun _ => hsplit)]
  congr 1
  funext _
  exact infinitePi_map_blocks S

/-- A lower bound on a good event from a measurable failure event of the image
law. The good event itself need not be measurable. -/
theorem one_sub_le_real_preimage {Y Z : Type*} [MeasurableSpace Y] [MeasurableSpace Z]
    (P : Measure Y) [IsProbabilityMeasure P] {f : Y → Z} (hf : Measurable f) {Bad Good : Set Z}
    (hBad : MeasurableSet Bad) (hcover : ∀ z, z ∉ Bad → z ∈ Good) {ε : ℝ}
    (h : (P.map f).real Bad ≤ ε) : 1 - ε ≤ P.real (f ⁻¹' Good) := by
  have hsub : (Set.univ : Set Y) ⊆ f ⁻¹' Good ∪ f ⁻¹' Bad := by
    intro y _
    by_cases hy : f y ∈ Bad
    · exact Or.inr hy
    · exact Or.inl (hcover _ hy)
  have h1 := measureReal_mono (μ := P) hsub
  rw [probReal_univ] at h1
  have h2 := measureReal_union_le (μ := P) (f ⁻¹' Good) (f ⁻¹' Bad)
  rw [map_measureReal_apply hf hBad] at h
  linarith

theorem measurableSet_exists_depth {Y : Type*} [MeasurableSpace Y] (Bad : ℕ → Set Y)
    (hmeas : ∀ J, MeasurableSet (Bad J)) :
    MeasurableSet {ω : ℕ → Y | ∃ J, 1 ≤ J ∧ ω J ∈ Bad J} := by
  have h : {ω : ℕ → Y | ∃ J, 1 ≤ J ∧ ω J ∈ Bad J} =
      ⋃ J, {ω : ℕ → Y | 1 ≤ J ∧ ω J ∈ Bad J} := by
    ext ω
    simp
  rw [h]
  refine MeasurableSet.iUnion fun J => ?_
  by_cases hJ : 1 ≤ J
  · have heq : {ω : ℕ → Y | 1 ≤ J ∧ ω J ∈ Bad J} = (fun ω : ℕ → Y => ω J) ⁻¹' Bad J := by
      ext ω
      simp [hJ]
    rw [heq]
    exact (measurable_pi_apply J) (hmeas J)
  · have heq : {ω : ℕ → Y | 1 ≤ J ∧ ω J ∈ Bad J} = ∅ := by
      ext ω
      simp [hJ]
    rw [heq]
    exact MeasurableSet.empty

/-- With flip budget and coin cap `4^J` the coin cap is inactive in the bound. -/
theorem tail_bound_uncapped (μ : Measure Gap) [IsProbabilityMeasure μ] (J : ℕ) :
    min 1 (128 * max (max (tailUnresolvedMass μ J)
        ((∫ d : Gap, tailWorkEnvelope J d ∂μ) / ((4 ^ J : ℕ) : ℝ))) (1 / ((4 ^ J : ℕ) : ℝ))) =
      min 1 (128 * max (tailUnresolvedMass μ J)
        ((∫ d : Gap, tailWorkEnvelope J d ∂μ) / 4 ^ J)) := by
  have hW := one_le_tailWorkEnvelope_integral μ J
  have hN' : (0 : ℝ) < (4 : ℝ) ^ J := by positivity
  have hle : 1 / (4 : ℝ) ^ J ≤ (∫ d : Gap, tailWorkEnvelope J d ∂μ) / 4 ^ J :=
    div_le_div_of_nonneg_right hW hN'.le
  push_cast
  rw [max_eq_left (hle.trans (le_max_right _ _))]

/-- On the original population the median certificate fails with probability
at most `2 exp(-m/8)`. -/
theorem original_medianFailure_le (μ : Measure Gap) [IsProbabilityMeasure μ] (q : SignLaw)
    (J m b M : ℕ) (hm : 0 < m) (hb : 0 < b) (hM : 0 < M) :
    (Measure.infinitePi (fun _ : ℕ =>
        Measure.infinitePi (fun _ : ℕ => originalPopulationTapeLaw μ q))).real
      (medianFailure J m b M (μ.real {d : Gap | (d : ℝ) ≤ (1 / 2) ^ J})
        (min 1 (128 * max (max (tailUnresolvedMass μ J)
          ((∫ d : Gap, tailWorkEnvelope J d ∂μ) / b)) (1 / M)))) ≤
      2 * exp (-(m : ℝ) / 8) := by
  have hFu : μ.real {d : Gap | (d : ℝ) ≤ (1 / 2) ^ J} ≤
      2 * (originalPopulationTapeLaw μ q).real {t | tailUnresolved J t} := by
    rw [original_tail_unresolved μ q J]
    have h := tail_unresolved_mass_lower μ J
    linarith
  have h := stream_medianFailure_le (originalPopulationTapeLaw μ q) J m b M hm hb hM
    measureReal_le_one hFu (original_tail_expected_work μ q J)
  rwa [original_tail_unresolved μ q J] at h

/-- The median over `m` independent probes on the original population. Except
with probability `2 exp(-m/8)`, the median covers the small-gap mass for every
choice of the probes' flip budgets and coin caps, and at the common budget `b`
and coin cap `M` it is at most `min{1, 128 max(u_J, W_J/b, 1/M)}`. -/
theorem original_median_certificate_exp (μ : Measure Gap) [IsProbabilityMeasure μ]
    (q : SignLaw) (J m b M : ℕ) (hm : 0 < m) (hb : 0 < b) (hM : 0 < M) :
    1 - 2 * exp (-(m : ℝ) / 8) ≤
      (Measure.infinitePi (fun _ : ℕ =>
          Measure.infinitePi (fun _ : ℕ => originalPopulationTapeLaw μ q))).real
        {ω | (∀ b' M' : ℕ → ℕ,
            μ.real {d : Gap | (d : ℝ) ≤ (1 / 2) ^ J} ≤ medianUpper J m b' M' ω) ∧
          medianUpper J m (fun _ => b) (fun _ => M) ω ≤
            min 1 (128 * max (max (tailUnresolvedMass μ J)
              ((∫ d : Gap, tailWorkEnvelope J d ∂μ) / b)) (1 / M))} := by
  have hfail := original_medianFailure_le μ q J m b M hm hb hM
  have hcover : (Set.univ : Set (ℕ → ℕ → ℕ → Bool)) ⊆
      {ω | (∀ b' M' : ℕ → ℕ,
          μ.real {d : Gap | (d : ℝ) ≤ (1 / 2) ^ J} ≤ medianUpper J m b' M' ω) ∧
        medianUpper J m (fun _ => b) (fun _ => M) ω ≤
          min 1 (128 * max (max (tailUnresolvedMass μ J)
            ((∫ d : Gap, tailWorkEnvelope J d ∂μ) / b)) (1 / M))} ∪
        medianFailure J m b M (μ.real {d : Gap | (d : ℝ) ≤ (1 / 2) ^ J})
          (min 1 (128 * max (max (tailUnresolvedMass μ J)
            ((∫ d : Gap, tailWorkEnvelope J d ∂μ) / b)) (1 / M))) := by
    intro ω _
    by_cases h : ω ∈ medianFailure J m b M (μ.real {d : Gap | (d : ℝ) ≤ (1 / 2) ^ J})
        (min 1 (128 * max (max (tailUnresolvedMass μ J)
          ((∫ d : Gap, tailWorkEnvelope J d ∂μ) / b)) (1 / M)))
    · exact Or.inr h
    · exact Or.inl (median_good_of_not_failure h)
  have h1 := measureReal_mono (μ := Measure.infinitePi (fun _ : ℕ =>
    Measure.infinitePi (fun _ : ℕ => originalPopulationTapeLaw μ q))) hcover
  rw [probReal_univ] at h1
  have h2 := measureReal_union_le (μ := Measure.infinitePi (fun _ : ℕ =>
      Measure.infinitePi (fun _ : ℕ => originalPopulationTapeLaw μ q)))
    {ω | (∀ b' M' : ℕ → ℕ,
        μ.real {d : Gap | (d : ℝ) ≤ (1 / 2) ^ J} ≤ medianUpper J m b' M' ω) ∧
      medianUpper J m (fun _ => b) (fun _ => M) ω ≤
        min 1 (128 * max (max (tailUnresolvedMass μ J)
          ((∫ d : Gap, tailWorkEnvelope J d ∂μ) / b)) (1 / M))}
    (medianFailure J m b M (μ.real {d : Gap | (d : ℝ) ≤ (1 / 2) ^ J})
      (min 1 (128 * max (max (tailUnresolvedMass μ J)
        ((∫ d : Gap, tailWorkEnvelope J d ∂μ) / b)) (1 / M))))
  linarith

/-- The median certificate at confidence `1 - δ`, with the coin cap. For
`m ≥ 8 log(2/δ)` probes, with probability at least `1 - δ` the median covers
the small-gap mass for every choice of the probes' flip budgets and coin caps,
and at the common budget `b` and coin cap `M` it is at most
`min{1, 128 max(u_J, W_J/b, 1/M)}`. -/
theorem original_median_certificate (μ : Measure Gap) [IsProbabilityMeasure μ] (q : SignLaw)
    (J m b M : ℕ) (hm : 0 < m) (hb : 0 < b) (hM : 0 < M) {δ : ℝ} (hδ : 0 < δ)
    (hmδ : 8 * log (2 / δ) ≤ m) :
    1 - δ ≤
      (Measure.infinitePi (fun _ : ℕ =>
          Measure.infinitePi (fun _ : ℕ => originalPopulationTapeLaw μ q))).real
        {ω | (∀ b' M' : ℕ → ℕ,
            μ.real {d : Gap | (d : ℝ) ≤ (1 / 2) ^ J} ≤ medianUpper J m b' M' ω) ∧
          medianUpper J m (fun _ => b) (fun _ => M) ω ≤
            min 1 (128 * max (max (tailUnresolvedMass μ J)
              ((∫ d : Gap, tailWorkEnvelope J d ∂μ) / b)) (1 / M))} := by
  have h := original_median_certificate_exp μ q J m b M hm hb hM
  have hcal := two_exp_le_of_log_le hδ hmδ
  linarith

/-- Statement (1) of the tail certificate. `m ≥ 8 log(2/δ)` probes, each with
flip budget `N = 4^J` and no active coin cap, are charged at most `m 4^J`
flips on every path. With probability at least `1 - δ` their median `U`
satisfies `F(2^{-J}) ≤ U ≤ min{1, 128 max(u_J, W_J/N)}`, and the lower bound
holds for every choice of the probes' flip budgets and coin caps. -/
theorem original_tail_certificate (μ : Measure Gap) [IsProbabilityMeasure μ] (q : SignLaw)
    (J m : ℕ) (hm : 0 < m) {δ : ℝ} (hδ : 0 < δ) (hmδ : 8 * log (2 / δ) ≤ m) :
    1 - δ ≤
      (Measure.infinitePi (fun _ : ℕ =>
          Measure.infinitePi (fun _ : ℕ => originalPopulationTapeLaw μ q))).real
        {ω | (∀ b' M' : ℕ → ℕ,
            μ.real {d : Gap | (d : ℝ) ≤ (1 / 2) ^ J} ≤ medianUpper J m b' M' ω) ∧
          medianUpper J m (fun _ => 4 ^ J) (fun _ => 4 ^ J) ω ≤
            min 1 (128 * max (tailUnresolvedMass μ J)
              ((∫ d : Gap, tailWorkEnvelope J d ∂μ) / 4 ^ J))} := by
  have hN : 0 < 4 ^ J := pow_pos (by norm_num) J
  have h := original_median_certificate μ q J m (4 ^ J) (4 ^ J) hm hN hN hδ hmδ
  rwa [tail_bound_uncapped μ J] at h

/-- Some depth `J ≥ 1` fails with probability at most `δ`, when depth `J` runs
`m_J ≥ 8 log(2J(J+1)/δ)` probes on its own independent streams. -/
theorem original_depthFailure_le (μ : Measure Gap) [IsProbabilityMeasure μ] (q : SignLaw)
    (m b M : ℕ → ℕ) {δ : ℝ} (hδ : 0 < δ) (hm : ∀ J : ℕ, 1 ≤ J → 0 < m J)
    (hmδ : ∀ J : ℕ, 1 ≤ J → 8 * log (2 * ((J : ℝ) * (J + 1)) / δ) ≤ m J)
    (hb : ∀ J : ℕ, 1 ≤ J → 0 < b J) (hM : ∀ J : ℕ, 1 ≤ J → 0 < M J) :
    (Measure.infinitePi (fun _ : ℕ => Measure.infinitePi (fun _ : ℕ =>
        Measure.infinitePi (fun _ : ℕ => originalPopulationTapeLaw μ q)))).real
      {ω | ∃ J, 1 ≤ J ∧ ω J ∈ medianFailure J (m J) (b J) (M J)
        (μ.real {d : Gap | (d : ℝ) ≤ (1 / 2) ^ J})
        (min 1 (128 * max (max (tailUnresolvedMass μ J)
          ((∫ d : Gap, tailWorkEnvelope J d ∂μ) / b J)) (1 / M J)))} ≤ δ := by
  have hbad : ∀ J, 1 ≤ J →
      (Measure.infinitePi (fun _ : ℕ =>
          Measure.infinitePi (fun _ : ℕ => originalPopulationTapeLaw μ q))).real
        (medianFailure J (m J) (b J) (M J) (μ.real {d : Gap | (d : ℝ) ≤ (1 / 2) ^ J})
          (min 1 (128 * max (max (tailUnresolvedMass μ J)
            ((∫ d : Gap, tailWorkEnvelope J d ∂μ) / b J)) (1 / M J)))) ≤
        δ / ((J : ℝ) * (J + 1)) := by
    intro J hJ
    have hJ' : (0 : ℝ) < (J : ℝ) * (J + 1) := by
      have h1 : (1 : ℝ) ≤ J := by exact_mod_cast hJ
      positivity
    have hcal : 8 * log (2 / (δ / ((J : ℝ) * (J + 1)))) ≤ m J := by
      rw [div_div_eq_mul_div]
      exact hmδ J hJ
    exact (original_medianFailure_le μ q J (m J) (b J) (M J) (hm J hJ) (hb J hJ)
      (hM J hJ)).trans (two_exp_le_of_log_le (div_pos hδ hJ') hcal)
  exact depth_union_bound
    (Measure.infinitePi (fun _ : ℕ =>
      Measure.infinitePi (fun _ : ℕ => originalPopulationTapeLaw μ q)))
    (fun J => medianFailure J (m J) (b J) (M J) (μ.real {d : Gap | (d : ℝ) ≤ (1 / 2) ^ J})
      (min 1 (128 * max (max (tailUnresolvedMass μ J)
        ((∫ d : Gap, tailWorkEnvelope J d ∂μ) / b J)) (1 / M J))))
    (fun J => measurableSet_medianFailure _ _ _ _ _ _) hδ.le hbad

/-- Every depth at once. Depth `J ≥ 1` runs `m_J ≥ 8 log(2J(J+1)/δ)` probes on
its own independent streams, with common flip budget `b_J` and coin cap `M_J`.
With probability at least `1 - δ`, at every depth `J ≥ 1` the median covers the
small-gap mass `F(2^{-J})` for every choice of the probes' flip budgets and
coin caps, and is at most `min{1, 128 max(u_J, W_J/b_J, 1/M_J)}`. -/
theorem original_median_all_depths (μ : Measure Gap) [IsProbabilityMeasure μ] (q : SignLaw)
    (m b M : ℕ → ℕ) {δ : ℝ} (hδ : 0 < δ) (hm : ∀ J : ℕ, 1 ≤ J → 0 < m J)
    (hmδ : ∀ J : ℕ, 1 ≤ J → 8 * log (2 * ((J : ℝ) * (J + 1)) / δ) ≤ m J)
    (hb : ∀ J : ℕ, 1 ≤ J → 0 < b J) (hM : ∀ J : ℕ, 1 ≤ J → 0 < M J) :
    1 - δ ≤
      (Measure.infinitePi (fun _ : ℕ => Measure.infinitePi (fun _ : ℕ =>
          Measure.infinitePi (fun _ : ℕ => originalPopulationTapeLaw μ q)))).real
        {ω | ∀ J, 1 ≤ J →
          (∀ b' M' : ℕ → ℕ,
            μ.real {d : Gap | (d : ℝ) ≤ (1 / 2) ^ J} ≤ medianUpper J (m J) b' M' (ω J)) ∧
          medianUpper J (m J) (fun _ => b J) (fun _ => M J) (ω J) ≤
            min 1 (128 * max (max (tailUnresolvedMass μ J)
              ((∫ d : Gap, tailWorkEnvelope J d ∂μ) / b J)) (1 / M J))} := by
  have hfail := original_depthFailure_le μ q m b M hδ hm hmδ hb hM
  rw [← Measure.map_id (μ := Measure.infinitePi (fun _ : ℕ => Measure.infinitePi (fun _ : ℕ =>
    Measure.infinitePi (fun _ : ℕ => originalPopulationTapeLaw μ q))))] at hfail
  exact one_sub_le_real_preimage
    (Measure.infinitePi (fun _ : ℕ => Measure.infinitePi (fun _ : ℕ =>
      Measure.infinitePi (fun _ : ℕ => originalPopulationTapeLaw μ q)))) measurable_id
    (measurableSet_exists_depth _ fun J => measurableSet_medianFailure _ _ _ _ _ _)
    (Good := {z | ∀ J, 1 ≤ J →
      (∀ b' M' : ℕ → ℕ,
        μ.real {d : Gap | (d : ℝ) ≤ (1 / 2) ^ J} ≤ medianUpper J (m J) b' M' (z J)) ∧
      medianUpper J (m J) (fun _ => b J) (fun _ => M J) (z J) ≤
        min 1 (128 * max (max (tailUnresolvedMass μ J)
          ((∫ d : Gap, tailWorkEnvelope J d ∂μ) / b J)) (1 / M J))})
    (fun z hz J hJ => median_good_of_not_failure fun hmem => hz ⟨J, hJ, hmem⟩) hfail

/-- Statement (1) on a single coin array. Probe `j` reads the coins
`Nat.pair j i` of one sequence of independent fresh coins. With probability at
least `1 - δ` the median `U` of `m ≥ 8 log(2/δ)` probes, each with flip budget
`4^J`, satisfies `F(2^{-J}) ≤ U ≤ min{1, 128 max(u_J, W_J/4^J)}`, and the lower
bound holds for every choice of the probes' flip budgets and coin caps. -/
theorem original_tail_certificate_array (μ : Measure Gap) [IsProbabilityMeasure μ]
    (q : SignLaw) (J m : ℕ) (hm : 0 < m) {δ : ℝ} (hδ : 0 < δ) (hmδ : 8 * log (2 / δ) ≤ m) :
    1 - δ ≤
      (Measure.infinitePi (fun _ : ℕ => originalPopulationTapeLaw μ q)).real
        {ω | (∀ b' M' : ℕ → ℕ, μ.real {d : Gap | (d : ℝ) ≤ (1 / 2) ^ J} ≤
            medianUpper J m b' M' (fun j i => ω (Nat.pair j i))) ∧
          medianUpper J m (fun _ => 4 ^ J) (fun _ => 4 ^ J) (fun j i => ω (Nat.pair j i)) ≤
            min 1 (128 * max (tailUnresolvedMass μ J)
              ((∫ d : Gap, tailWorkEnvelope J d ∂μ) / 4 ^ J))} := by
  have hN : 0 < 4 ^ J := pow_pos (by norm_num) J
  have hsplit : Measurable (fun (ω : ℕ → ℕ → Bool) (j i : ℕ) => ω (Nat.pair j i)) :=
    Measurable.of_eval fun j => Measurable.of_eval fun i => measurable_pi_apply _
  have hfail := original_medianFailure_le μ q J m (4 ^ J) (4 ^ J) hm hN hN
  rw [← infinitePi_map_blocks (originalPopulationTapeLaw μ q)] at hfail
  have h := one_sub_le_real_preimage
    (Measure.infinitePi (fun _ : ℕ => originalPopulationTapeLaw μ q)) hsplit
    (measurableSet_medianFailure _ _ _ _ _ _)
    (Good := {z | (∀ b' M' : ℕ → ℕ,
        μ.real {d : Gap | (d : ℝ) ≤ (1 / 2) ^ J} ≤ medianUpper J m b' M' z) ∧
      medianUpper J m (fun _ => 4 ^ J) (fun _ => 4 ^ J) z ≤
        min 1 (128 * max (tailUnresolvedMass μ J)
          ((∫ d : Gap, tailWorkEnvelope J d ∂μ) / 4 ^ J))})
    (fun z hz => by
      have hg := median_good_of_not_failure hz
      rw [tail_bound_uncapped μ J] at hg
      exact hg) hfail
  have hcal := two_exp_le_of_log_le hδ hmδ
  exact le_trans (by linarith) h

/-- Every depth at once on a single coin array. Probe `j` of depth `J` reads
the coins `Nat.pair J (Nat.pair j i)` of one sequence of independent fresh
coins. With probability at least `1 - δ`, at every depth `J ≥ 1` the median of
`m_J ≥ 8 log(2J(J+1)/δ)` probes covers `F(2^{-J})` for every choice of the
probes' flip budgets and coin caps, and at the common budget `b_J` and coin
cap `M_J` it is at most `min{1, 128 max(u_J, W_J/b_J, 1/M_J)}`. -/
theorem original_median_all_depths_array (μ : Measure Gap) [IsProbabilityMeasure μ]
    (q : SignLaw) (m b M : ℕ → ℕ) {δ : ℝ} (hδ : 0 < δ) (hm : ∀ J : ℕ, 1 ≤ J → 0 < m J)
    (hmδ : ∀ J : ℕ, 1 ≤ J → 8 * log (2 * ((J : ℝ) * (J + 1)) / δ) ≤ m J)
    (hb : ∀ J : ℕ, 1 ≤ J → 0 < b J) (hM : ∀ J : ℕ, 1 ≤ J → 0 < M J) :
    1 - δ ≤
      (Measure.infinitePi (fun _ : ℕ => originalPopulationTapeLaw μ q)).real
        {ω | ∀ J, 1 ≤ J →
          (∀ b' M' : ℕ → ℕ, μ.real {d : Gap | (d : ℝ) ≤ (1 / 2) ^ J} ≤
            medianUpper J (m J) b' M' (fun j i => ω (Nat.pair J (Nat.pair j i)))) ∧
          medianUpper J (m J) (fun _ => b J) (fun _ => M J)
              (fun j i => ω (Nat.pair J (Nat.pair j i))) ≤
            min 1 (128 * max (max (tailUnresolvedMass μ J)
              ((∫ d : Gap, tailWorkEnvelope J d ∂μ) / b J)) (1 / M J))} := by
  have hsplit : Measurable
      (fun (ω : ℕ → ℕ → Bool) (J j i : ℕ) => ω (Nat.pair J (Nat.pair j i))) :=
    Measurable.of_eval fun J => Measurable.of_eval fun j => Measurable.of_eval fun i =>
      measurable_pi_apply _
  have hfail := original_depthFailure_le μ q m b M hδ hm hmδ hb hM
  rw [← infinitePi_map_depth_blocks (originalPopulationTapeLaw μ q)] at hfail
  exact one_sub_le_real_preimage
    (Measure.infinitePi (fun _ : ℕ => originalPopulationTapeLaw μ q)) hsplit
    (measurableSet_exists_depth _ fun J => measurableSet_medianFailure _ _ _ _ _ _)
    (Good := {z | ∀ J, 1 ≤ J →
      (∀ b' M' : ℕ → ℕ,
        μ.real {d : Gap | (d : ℝ) ≤ (1 / 2) ^ J} ≤ medianUpper J (m J) b' M' (z J)) ∧
      medianUpper J (m J) (fun _ => b J) (fun _ => M J) (z J) ≤
        min 1 (128 * max (max (tailUnresolvedMass μ J)
          ((∫ d : Gap, tailWorkEnvelope J d ∂μ) / b J)) (1 / M J))})
    (fun z hz J hJ => median_good_of_not_failure fun hmem => hz ⟨J, hJ, hmem⟩) hfail

end ThresholdHC.ArbitraryLawAdaptation
