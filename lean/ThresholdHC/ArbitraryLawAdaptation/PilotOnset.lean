import ThresholdHC.ArbitraryLawAdaptation.TailPilot
import ThresholdHC.ArbitraryLawAdaptation.TailOracle

/-! The pilot's work estimates (A12), its onset and the floors of the selection
functional.

Split the gap law `μ` at its lowest-gap quantile of mass `ρ`, with a fraction
of a boundary atom when needed: `μ = ν + σ`, where `ν` has mass `ρ` and the
core `σ` has gaps at least the quantile threshold `a > 0`. For the pilot of
target depth `J`, with `N = 4^J`, `t = 2^{-J}` and the budgets `b_j` of (A6),
every depth `1 ≤ j ≤ J` satisfies

  `W_{j,ν}/b_j ≤ 8192 τ_ν(t)`  and  `W_{j,σ}/b_j ≤ 2048 (J+1)³ t²/a²`,

where `W_{j,·}` integrates the work envelope of depth `j` and `τ_ν` is the tail
modulus. This is (A12). The pilot's onset condition at depth `J` is
`2048 (J+1)³ 2^{-J}/a² ≤ √ρ`; it holds at every large depth. Under it, with
`K = K_{μ,ρ}(N)` the entropy-tail selection functional and `ρ ≤ 1/4`,

  `W_j/b_j ≤ 8193 K`  and  `16/M ≤ K`.

These are deterministic statements about the gap law. The threshold `a` and
the onset are proof quantities; the pilot receives neither. -/

noncomputable section
open MeasureTheory Real
open scoped ENNReal Topology
namespace ThresholdHC.ArbitraryLawAdaptation
open ThresholdHC.Tier6 ThresholdHC.EntropyTailQuantile

/-- The pilot's onset condition at target depth `J`: `2048 (J+1)³ 2^{-J}/a² ≤ √ρ`,
where `a` is the quantile threshold of mass `ρ` of the gap law. -/
def PilotOnset (μ : Measure Gap) (ρ : ℝ) (J : ℕ) : Prop :=
  2048 * ((J : ℝ) + 1) ^ 3 * (1 / 2) ^ J / (quantileThreshold μ ρ) ^ 2 ≤ Real.sqrt ρ

/-- The lowest-gap split of a gap law at mass `ρ`. The quantile part has mass
`ρ` and gaps at most the threshold `a`; the core has gaps at least `a`; and
`a > 0`. A boundary atom at `a` is split between the two parts. -/
theorem lowest_gap_split (μ : Measure Gap) [IsProbabilityMeasure μ] {ρ : ℝ} (hρ : 0 < ρ)
    (hρ1 : ρ ≤ 1) :
    quantileTail μ ρ + quantileCore μ ρ = μ ∧
      quantileTail μ ρ Set.univ = ENNReal.ofReal ρ ∧
      0 < quantileThreshold μ ρ ∧
      (∀ᵐ d : Gap ∂quantileTail μ ρ, (d : ℝ) ≤ quantileThreshold μ ρ) ∧
      ∀ᵐ d : Gap ∂quantileCore μ ρ, quantileThreshold μ ρ ≤ (d : ℝ) :=
  ⟨quantileTail_add_core μ hρ hρ1, quantileTail_mass μ hρ hρ1,
    (quantileThreshold_properties μ hρ hρ1).1, quantileTail_support μ ρ,
    quantileCore_support μ ρ⟩

/-- `2048 (J+1)³ 2^{-J}/a² ≤ √ρ` at every large `J`. -/
theorem pilot_onset_exists {a ρ : ℝ} (ha : 0 < a) (hρ : 0 < ρ) :
    ∃ J₀ : ℕ, ∀ J : ℕ, J₀ ≤ J →
      2048 * ((J : ℝ) + 1) ^ 3 * (1 / 2) ^ J / a ^ 2 ≤ Real.sqrt ρ := by
  have h (k : ℕ) : Filter.Tendsto (fun n : ℕ => (n : ℝ) ^ k / (2 : ℝ) ^ n) Filter.atTop (𝓝 0) :=
    tendsto_pow_const_div_const_pow_of_one_lt k (by norm_num)
  have hsum : Filter.Tendsto
      (fun n : ℕ => 2048 / a ^ 2 * ((n : ℝ) ^ 3 / (2 : ℝ) ^ n + 3 * ((n : ℝ) ^ 2 / (2 : ℝ) ^ n) +
        3 * ((n : ℝ) ^ 1 / (2 : ℝ) ^ n) + (n : ℝ) ^ 0 / (2 : ℝ) ^ n))
      Filter.atTop (𝓝 0) := by
    have h' := ((((h 3).add ((h 2).const_mul 3)).add ((h 1).const_mul 3)).add (h 0)).const_mul
      (2048 / a ^ 2)
    simpa using h'
  have hev := hsum.eventually (ge_mem_nhds (Real.sqrt_pos.mpr hρ))
  obtain ⟨J₀, hJ₀⟩ := Filter.eventually_atTop.mp hev
  refine ⟨J₀, fun J hJ => ?_⟩
  have h' := hJ₀ J hJ
  have hT : (0 : ℝ) < 2 ^ J := by positivity
  have heq : 2048 * ((J : ℝ) + 1) ^ 3 * (1 / 2) ^ J / a ^ 2 =
      2048 / a ^ 2 * ((J : ℝ) ^ 3 / (2 : ℝ) ^ J + 3 * ((J : ℝ) ^ 2 / (2 : ℝ) ^ J) +
        3 * ((J : ℝ) ^ 1 / (2 : ℝ) ^ J) + (J : ℝ) ^ 0 / (2 : ℝ) ^ J) := by
    rw [half_pow_eq]
    field_simp
    ring
  rw [heq]
  exact h'

/-- The pilot's onset condition holds at every large target depth. The onset
depends on the law only through its quantile threshold. -/
theorem pilotOnset_eventually (μ : Measure Gap) [IsProbabilityMeasure μ] {ρ : ℝ} (hρ : 0 < ρ)
    (hρ1 : ρ ≤ 1) : ∃ J₀ : ℕ, ∀ J : ℕ, J₀ ≤ J → PilotOnset μ ρ J :=
  pilot_onset_exists (quantileThreshold_properties μ hρ hρ1).1 hρ

/-- The pilot's onset condition implies the onset condition of the tail
certificate. -/
theorem pilotOnset_tailOnset {μ : Measure Gap} {ρ : ℝ} {J : ℕ} (h : PilotOnset μ ρ J) :
    TailOnset μ ρ J := by
  unfold PilotOnset at h
  unfold TailOnset
  refine le_trans ?_ h
  have hJ : (1 : ℝ) ≤ (J : ℝ) + 1 := by
    have h0 : (0 : ℝ) ≤ J := Nat.cast_nonneg J
    linarith
  have hcube : (J : ℝ) + 1 ≤ ((J : ℝ) + 1) ^ 3 := by
    calc (J : ℝ) + 1 = ((J : ℝ) + 1) ^ 1 := (pow_one _).symm
      _ ≤ ((J : ℝ) + 1) ^ 3 := pow_le_pow_right₀ hJ (by norm_num)
  have ht : (0 : ℝ) < (1 / 2) ^ J := by positivity
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hcube (by norm_num)) ht.le

/-- Under the pilot's onset condition, `2 · 2^{-J} ≤ √ρ`. -/
theorem pilotOnset_small (μ : Measure Gap) [IsProbabilityMeasure μ] {ρ : ℝ} (hρ : 0 < ρ)
    (hρ1 : ρ ≤ 1) {J : ℕ} (h : PilotOnset μ ρ J) : 2 * (1 / 2 : ℝ) ^ J ≤ Real.sqrt ρ := by
  unfold PilotOnset at h
  obtain ⟨ha, ha2, -, -⟩ := quantileThreshold_properties μ hρ hρ1
  have ht : (0 : ℝ) < (1 / 2) ^ J := by positivity
  have hJ0 : (0 : ℝ) ≤ J := Nat.cast_nonneg J
  have ha4 : (quantileThreshold μ ρ) ^ 2 ≤ 1 / 4 := by nlinarith
  have hcube : (1 : ℝ) ≤ ((J : ℝ) + 1) ^ 3 := one_le_pow₀ (by linarith)
  have h1 : 2 * (1 / 2 : ℝ) ^ J ≤
      2048 * ((J : ℝ) + 1) ^ 3 * (1 / 2) ^ J / (quantileThreshold μ ρ) ^ 2 := by
    rw [le_div_iff₀ (by positivity)]
    nlinarith [mul_nonneg ht.le (sub_nonneg.mpr ha4), mul_nonneg ht.le (sub_nonneg.mpr hcube)]
  linarith

/-- The reciprocal part of the budget of depth `j`. -/
theorem reciprocal_le_pilotBudget (J j : ℕ) :
    (4 : ℝ) ^ J / (2 * (j : ℝ) * ((j : ℝ) + 1)) ≤ (pilotBudget J j : ℝ) := by
  have h := Nat.le_ceil ((4 : ℝ) ^ J / (2 * (j : ℝ) * ((j : ℝ) + 1)))
  have h2 : (0 : ℝ) ≤ ((2 ^ (J + j - 2) : ℕ) : ℝ) := Nat.cast_nonneg _
  unfold pilotBudget
  rw [Nat.cast_add]
  linarith

/-- The geometric part of the budget of depth `j`. -/
theorem geometric_le_pilotBudget (J j : ℕ) :
    (2 : ℝ) ^ (J + j - 2) ≤ (pilotBudget J j : ℝ) := by
  have h : (0 : ℝ) ≤ ((⌈(4 : ℝ) ^ J / (2 * (j : ℝ) * ((j : ℝ) + 1))⌉₊ : ℕ) : ℝ) :=
    Nat.cast_nonneg _
  unfold pilotBudget
  rw [Nat.cast_add]
  push_cast
  linarith

/-- The work envelope of depth `j` against the tail kernel:
`w_j(d) ≤ 2048 · 4^j min{1, 2^{-j}/d}`. -/
theorem tailWorkEnvelope_le_tail (j : ℕ) (d : Gap) :
    tailWorkEnvelope j d ≤ 2048 * 4 ^ j * min 1 ((1 / 2) ^ j / (d : ℝ)) := by
  have h := tailWorkEnvelope_div_le j d
  have hN : (0 : ℝ) < 4 ^ j := by positivity
  rw [div_le_iff₀ hN] at h
  linarith

/-- The work envelope of depth `j` on gaps at least `a`:
`w_j(d) ≤ 1024 (j+1)/a²`. -/
theorem tailWorkEnvelope_le_core (j : ℕ) {a : ℝ} (ha : 0 < a) (d : Gap) (had : a ≤ (d : ℝ)) :
    tailWorkEnvelope j d ≤ 1024 * ((j : ℝ) + 1) / a ^ 2 := by
  have hd0 : (0 : ℝ) < d := d.property.1
  have ha2 : 0 < a ^ 2 := by positivity
  have hd2 : a ^ 2 ≤ (d : ℝ) ^ 2 := pow_le_pow_left₀ ha.le had 2
  have hL : 1 + tailLog j d ≤ (j : ℝ) + 1 := by linarith [tailLog_le j d]
  have hj : (0 : ℝ) ≤ (j : ℝ) + 1 := by positivity
  calc tailWorkEnvelope j d ≤ 1024 / (d : ℝ) ^ 2 * (1 + tailLog j d) := min_le_right _ _
    _ ≤ 1024 / (d : ℝ) ^ 2 * ((j : ℝ) + 1) := mul_le_mul_of_nonneg_left hL (by positivity)
    _ ≤ 1024 / a ^ 2 * ((j : ℝ) + 1) :=
        mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_left (by norm_num) ha2 hd2) hj
    _ = 1024 * ((j : ℝ) + 1) / a ^ 2 := by ring

/-- The tail kernel at a larger scale: `min{1, s/d} ≤ (s/t) min{1, t/d}` for
`0 < t ≤ s`. -/
theorem tailKernel_scale {t s : ℝ} (ht : 0 < t) (hts : t ≤ s) (d : Gap) :
    min 1 (s / (d : ℝ)) ≤ s / t * min 1 (t / (d : ℝ)) := by
  have hd0 : (0 : ℝ) < d := d.property.1
  have hst : 1 ≤ s / t := by rwa [le_div_iff₀ ht, one_mul]
  rcases le_total 1 (t / (d : ℝ)) with h1 | h1
  · rw [min_eq_left h1, mul_one]
    exact (min_le_left _ _).trans hst
  · rw [min_eq_right h1]
    refine (min_le_right _ _).trans_eq ?_
    field_simp

/-- The tail modulus at a larger scale: `τ_ν(s) ≤ (s/t) τ_ν(t)` for `0 < t ≤ s`. -/
theorem tailModulus_scale (ν : Measure Gap) [IsFiniteMeasure ν] {t s : ℝ} (ht : 0 < t)
    (hts : t ≤ s) : tailModulus ν s ≤ s / t * tailModulus ν t := by
  unfold tailModulus
  rw [← integral_const_mul]
  exact integral_mono (tailKernel_integrable ν (ht.le.trans hts))
    ((tailKernel_integrable ν ht.le).const_mul _) fun d => tailKernel_scale ht hts d

theorem integrable_tailWorkEnvelope (ξ : Measure Gap) [IsFiniteMeasure ξ] (j : ℕ) :
    Integrable (fun d : Gap => tailWorkEnvelope j d) ξ :=
  ThresholdHC.Tier5.integrable_of_abs_bound ξ _
    ((measurable_tailWorkEnvelope j).comp measurable_subtype_coe) (4 ^ j) fun d => by
      rw [abs_of_nonneg (tailWorkEnvelope_nonneg j d)]
      exact tailWorkEnvelope_le j d

/-- The work of depth `j` splits at the quantile. -/
theorem work_split (μ : Measure Gap) [IsProbabilityMeasure μ] {ρ : ℝ} (hρ : 0 < ρ)
    (hρ1 : ρ ≤ 1) (j : ℕ) :
    ∫ d : Gap, tailWorkEnvelope j d ∂μ =
      ∫ d : Gap, tailWorkEnvelope j d ∂quantileTail μ ρ +
        ∫ d : Gap, tailWorkEnvelope j d ∂quantileCore μ ρ := by
  have hν : IsFiniteMeasure (quantileTail μ ρ) :=
    isFiniteMeasure_of_le μ (quantileTail_le μ hρ hρ1)
  have hσ : IsFiniteMeasure (quantileCore μ ρ) := isFiniteMeasure_of_le μ Measure.sub_le
  conv_lhs => rw [← quantileTail_add_core μ hρ hρ1]
  exact integral_add_measure (integrable_tailWorkEnvelope _ j) (integrable_tailWorkEnvelope _ j)

/-- The work of depth `j` on the quantile part: `W_{j,ν} ≤ 2048 · 4^j τ_ν(2^{-j})`. -/
theorem quantile_work_le (μ : Measure Gap) [IsProbabilityMeasure μ] {ρ : ℝ} (hρ : 0 < ρ)
    (hρ1 : ρ ≤ 1) (j : ℕ) :
    ∫ d : Gap, tailWorkEnvelope j d ∂quantileTail μ ρ ≤
      2048 * 4 ^ j * tailModulus (quantileTail μ ρ) ((1 / 2) ^ j) := by
  have hν : IsFiniteMeasure (quantileTail μ ρ) :=
    isFiniteMeasure_of_le μ (quantileTail_le μ hρ hρ1)
  unfold tailModulus
  rw [← integral_const_mul]
  exact integral_mono (integrable_tailWorkEnvelope _ j)
    ((tailKernel_integrable _ (by positivity)).const_mul _) fun d => tailWorkEnvelope_le_tail j d

/-- The work of depth `j` on the core: `W_{j,σ} ≤ 1024 (j+1)/a²`. -/
theorem core_work_le (μ : Measure Gap) [IsProbabilityMeasure μ] {ρ : ℝ} (hρ : 0 < ρ)
    (hρ1 : ρ ≤ 1) (j : ℕ) :
    ∫ d : Gap, tailWorkEnvelope j d ∂quantileCore μ ρ ≤
      1024 * ((j : ℝ) + 1) / (quantileThreshold μ ρ) ^ 2 := by
  have hσle : quantileCore μ ρ ≤ μ := Measure.sub_le
  have hσ : IsFiniteMeasure (quantileCore μ ρ) := isFiniteMeasure_of_le μ hσle
  have ha := (quantileThreshold_properties μ hρ hρ1).1
  have hmass : (quantileCore μ ρ).real Set.univ ≤ 1 := by
    have h : quantileCore μ ρ Set.univ ≤ 1 :=
      (Measure.le_iff'.1 hσle Set.univ).trans_eq measure_univ
    have h' := ENNReal.toReal_mono ENNReal.one_ne_top h
    simpa [measureReal_def] using h'
  have hc0 : 0 ≤ 1024 * ((j : ℝ) + 1) / (quantileThreshold μ ρ) ^ 2 := by positivity
  calc ∫ d : Gap, tailWorkEnvelope j d ∂quantileCore μ ρ
      ≤ ∫ _d : Gap, 1024 * ((j : ℝ) + 1) / (quantileThreshold μ ρ) ^ 2 ∂quantileCore μ ρ := by
        apply integral_mono_ae (integrable_tailWorkEnvelope _ j) (integrable_const _)
        filter_upwards [quantileCore_support μ ρ] with d hd
        exact tailWorkEnvelope_le_core j ha d hd
    _ = (quantileCore μ ρ).real Set.univ *
          (1024 * ((j : ℝ) + 1) / (quantileThreshold μ ρ) ^ 2) := by
        rw [integral_const, smul_eq_mul]
    _ ≤ 1 * (1024 * ((j : ℝ) + 1) / (quantileThreshold μ ρ) ^ 2) :=
        mul_le_mul_of_nonneg_right hmass hc0
    _ = 1024 * ((j : ℝ) + 1) / (quantileThreshold μ ρ) ^ 2 := one_mul _

/-- (A12), quantile part: `W_{j,ν}/b_j ≤ 8192 τ_ν(2^{-J})` at every depth
`1 ≤ j ≤ J` of the pilot. -/
theorem pilot_quantile_work (μ : Measure Gap) [IsProbabilityMeasure μ] {ρ : ℝ} (hρ : 0 < ρ)
    (hρ1 : ρ ≤ 1) {J j : ℕ} (hj1 : 1 ≤ j) (hjJ : j ≤ J) :
    (∫ d : Gap, tailWorkEnvelope j d ∂quantileTail μ ρ) / (pilotBudget J j : ℝ) ≤
      8192 * tailModulus (quantileTail μ ρ) ((1 / 2) ^ J) := by
  have hν : IsFiniteMeasure (quantileTail μ ρ) :=
    isFiniteMeasure_of_le μ (quantileTail_le μ hρ hρ1)
  have hτ0 : 0 ≤ tailModulus (quantileTail μ ρ) ((1 / 2) ^ J) :=
    tailModulus_nonneg _ (by positivity)
  have hbpos : (0 : ℝ) < (pilotBudget J j : ℝ) := by exact_mod_cast pilotBudget_pos J j
  have hb : (2 : ℝ) ^ J * 2 ^ j / 4 ≤ (pilotBudget J j : ℝ) := by
    have h := geometric_le_pilotBudget J j
    have he : (2 : ℝ) ^ (J + j - 2) * 4 = 2 ^ J * 2 ^ j := by
      rw [← pow_add, show (4 : ℝ) = 2 ^ 2 by norm_num, ← pow_add]
      congr 1
      omega
    linarith
  have hscale : tailModulus (quantileTail μ ρ) ((1 / 2) ^ j) ≤
      2 ^ J / 2 ^ j * tailModulus (quantileTail μ ρ) ((1 / 2) ^ J) := by
    have h := tailModulus_scale (quantileTail μ ρ) (t := (1 / 2 : ℝ) ^ J) (s := (1 / 2 : ℝ) ^ j)
      (by positivity) (pow_le_pow_of_le_one (by norm_num) (by norm_num) hjJ)
    have he : (1 / 2 : ℝ) ^ j / (1 / 2) ^ J = 2 ^ J / 2 ^ j := by
      rw [half_pow_eq, half_pow_eq]
      field_simp
    rwa [he] at h
  rw [div_le_iff₀ hbpos]
  calc ∫ d : Gap, tailWorkEnvelope j d ∂quantileTail μ ρ
      ≤ 2048 * 4 ^ j * tailModulus (quantileTail μ ρ) ((1 / 2) ^ j) := quantile_work_le μ hρ hρ1 j
    _ ≤ 2048 * 4 ^ j * (2 ^ J / 2 ^ j * tailModulus (quantileTail μ ρ) ((1 / 2) ^ J)) :=
        mul_le_mul_of_nonneg_left hscale (by positivity)
    _ = 8192 * tailModulus (quantileTail μ ρ) ((1 / 2) ^ J) * ((2 : ℝ) ^ J * 2 ^ j / 4) := by
        rw [four_pow_eq]
        field_simp
        ring
    _ ≤ 8192 * tailModulus (quantileTail μ ρ) ((1 / 2) ^ J) * (pilotBudget J j : ℝ) :=
        mul_le_mul_of_nonneg_left hb (mul_nonneg (by norm_num) hτ0)

/-- (A12), core part: `W_{j,σ}/b_j ≤ 2048 (J+1)³ (2^{-J})²/a²` at every depth
`1 ≤ j ≤ J` of the pilot. -/
theorem pilot_core_work (μ : Measure Gap) [IsProbabilityMeasure μ] {ρ : ℝ} (hρ : 0 < ρ)
    (hρ1 : ρ ≤ 1) {J j : ℕ} (hj1 : 1 ≤ j) (hjJ : j ≤ J) :
    (∫ d : Gap, tailWorkEnvelope j d ∂quantileCore μ ρ) / (pilotBudget J j : ℝ) ≤
      2048 * ((J : ℝ) + 1) ^ 3 * ((1 / 2) ^ J) ^ 2 / (quantileThreshold μ ρ) ^ 2 := by
  have ha := (quantileThreshold_properties μ hρ hρ1).1
  have hA : 0 < (quantileThreshold μ ρ) ^ 2 := by positivity
  have hbpos : (0 : ℝ) < (pilotBudget J j : ℝ) := by exact_mod_cast pilotBudget_pos J j
  have hj0 : (0 : ℝ) < (j : ℝ) := by exact_mod_cast hj1
  have hjJ' : (j : ℝ) ≤ (J : ℝ) := by exact_mod_cast hjJ
  have hN : (0 : ℝ) < 4 ^ J := by positivity
  have hcube : (j : ℝ) * ((j : ℝ) + 1) ^ 2 ≤ ((J : ℝ) + 1) ^ 3 := by
    have h1 : (j : ℝ) + 1 ≤ (J : ℝ) + 1 := by linarith
    have h2 : ((j : ℝ) + 1) ^ 2 ≤ ((J : ℝ) + 1) ^ 2 := pow_le_pow_left₀ (by positivity) h1 2
    calc (j : ℝ) * ((j : ℝ) + 1) ^ 2 ≤ ((J : ℝ) + 1) * ((J : ℝ) + 1) ^ 2 :=
          mul_le_mul (by linarith) h2 (by positivity) (by positivity)
      _ = ((J : ℝ) + 1) ^ 3 := by ring
  have hs : ((1 / 2 : ℝ) ^ J) ^ 2 = 1 / 4 ^ J := by
    rw [half_pow_eq, four_pow_eq, one_div_pow]
  have hkey : 1024 * ((j : ℝ) + 1) / (quantileThreshold μ ρ) ^ 2 ≤
      2048 * ((J : ℝ) + 1) ^ 3 * ((1 / 2) ^ J) ^ 2 / (quantileThreshold μ ρ) ^ 2 *
        ((4 : ℝ) ^ J / (2 * (j : ℝ) * ((j : ℝ) + 1))) := by
    have hrhs : 2048 * ((J : ℝ) + 1) ^ 3 * ((1 / 2) ^ J) ^ 2 / (quantileThreshold μ ρ) ^ 2 *
        ((4 : ℝ) ^ J / (2 * (j : ℝ) * ((j : ℝ) + 1))) =
        1024 * ((J : ℝ) + 1) ^ 3 / ((quantileThreshold μ ρ) ^ 2 * ((j : ℝ) * ((j : ℝ) + 1))) := by
      rw [hs]
      field_simp
      ring
    rw [hrhs, div_le_div_iff₀ hA (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_left hcube hA.le]
  rw [div_le_iff₀ hbpos]
  calc ∫ d : Gap, tailWorkEnvelope j d ∂quantileCore μ ρ
      ≤ 1024 * ((j : ℝ) + 1) / (quantileThreshold μ ρ) ^ 2 := core_work_le μ hρ hρ1 j
    _ ≤ 2048 * ((J : ℝ) + 1) ^ 3 * ((1 / 2) ^ J) ^ 2 / (quantileThreshold μ ρ) ^ 2 *
          ((4 : ℝ) ^ J / (2 * (j : ℝ) * ((j : ℝ) + 1))) := hkey
    _ ≤ 2048 * ((J : ℝ) + 1) ^ 3 * ((1 / 2) ^ J) ^ 2 / (quantileThreshold μ ρ) ^ 2 *
          (pilotBudget J j : ℝ) :=
        mul_le_mul_of_nonneg_left (reciprocal_le_pilotBudget J j) (by positivity)

/-- (A12). At every depth `1 ≤ j ≤ J` of the pilot,
`W_j/b_j ≤ 8192 τ_ν(2^{-J}) + 2048 (J+1)³ (2^{-J})²/a²`. -/
theorem pilot_work_le (μ : Measure Gap) [IsProbabilityMeasure μ] {ρ : ℝ} (hρ : 0 < ρ)
    (hρ1 : ρ ≤ 1) {J j : ℕ} (hj1 : 1 ≤ j) (hjJ : j ≤ J) :
    (∫ d : Gap, tailWorkEnvelope j d ∂μ) / (pilotBudget J j : ℝ) ≤
      8192 * tailModulus (quantileTail μ ρ) ((1 / 2) ^ J) +
        2048 * ((J : ℝ) + 1) ^ 3 * ((1 / 2) ^ J) ^ 2 / (quantileThreshold μ ρ) ^ 2 := by
  rw [work_split μ hρ hρ1 j, add_div]
  exact add_le_add (pilot_quantile_work μ hρ hρ1 hj1 hjJ) (pilot_core_work μ hρ hρ1 hj1 hjJ)

/-- The quantile-tail floor of the selection functional at budget `4^J`:
`τ_ν(2^{-J}) ≤ K_{μ,ρ}(4^J)`. -/
theorem quantile_tail_floor (μ : Measure Gap) [IsProbabilityMeasure μ] {ρ : ℝ} (hρ : 0 < ρ)
    (hρ1 : ρ ≤ 1) (J : ℕ) :
    ENNReal.ofReal (tailModulus (quantileTail μ ρ) ((1 / 2) ^ J)) ≤
      EntropyTail.selection μ ρ (4 ^ J) := by
  have h := quantileTail_le_selectionValue μ hρ hρ1 ((4 : ℝ) ^ J)
  rw [EntropyTail.quantile_selectionValue_eq] at h
  have hbs : EntropyTailQuantile.budgetScale ((4 : ℝ) ^ J) = (1 / 2) ^ J := by
    unfold EntropyTailQuantile.budgetScale
    rw [four_pow_eq, Real.sqrt_sq (by positivity), half_pow_eq, one_div]
  rwa [hbs] at h

/-- (A12) against the oracle. Under the pilot's onset condition, at every
depth `1 ≤ j ≤ J` of the pilot, `W_j/b_j ≤ 8193 K_{μ,ρ}(4^J)`. -/
theorem pilot_work_le_oracle (μ : Measure Gap) [IsProbabilityMeasure μ] {ρ : ℝ} (hρ : 0 < ρ)
    (hρ4 : ρ ≤ 1 / 4) {J j : ℕ} (hj1 : 1 ≤ j) (hjJ : j ≤ J) (hon : PilotOnset μ ρ J) :
    ENNReal.ofReal ((∫ d : Gap, tailWorkEnvelope j d ∂μ) / (pilotBudget J j : ℝ)) ≤
      8193 * EntropyTail.selection μ ρ (4 ^ J) := by
  have hρ1 : ρ ≤ 1 := by linarith
  have ht : (0 : ℝ) < (1 / 2) ^ J := by positivity
  have hτ0 : 0 ≤ tailModulus (quantileTail μ ρ) ((1 / 2) ^ J) := tailModulus_nonneg _ ht.le
  have hK := selection_ge_scale μ hρ hρ4 J (pilotOnset_small μ hρ hρ1 hon)
  have hfloor := quantile_tail_floor μ hρ hρ1 J
  have hcore : 2048 * ((J : ℝ) + 1) ^ 3 * ((1 / 2) ^ J) ^ 2 / (quantileThreshold μ ρ) ^ 2 ≤
      1 / 2 * (2 * (1 / 2) ^ J * Real.sqrt ρ) := by
    unfold PilotOnset at hon
    calc 2048 * ((J : ℝ) + 1) ^ 3 * ((1 / 2) ^ J) ^ 2 / (quantileThreshold μ ρ) ^ 2
        = (1 / 2) ^ J *
            (2048 * ((J : ℝ) + 1) ^ 3 * (1 / 2) ^ J / (quantileThreshold μ ρ) ^ 2) := by ring
      _ ≤ (1 / 2) ^ J * Real.sqrt ρ := mul_le_mul_of_nonneg_left hon ht.le
      _ = 1 / 2 * (2 * (1 / 2) ^ J * Real.sqrt ρ) := by ring
  have hreal : (∫ d : Gap, tailWorkEnvelope j d ∂μ) / (pilotBudget J j : ℝ) ≤
      8192 * tailModulus (quantileTail μ ρ) ((1 / 2) ^ J) +
        1 / 2 * (2 * (1 / 2) ^ J * Real.sqrt ρ) :=
    (pilot_work_le μ hρ hρ1 hj1 hjJ).trans (add_le_add le_rfl hcore)
  calc ENNReal.ofReal ((∫ d : Gap, tailWorkEnvelope j d ∂μ) / (pilotBudget J j : ℝ))
      ≤ ENNReal.ofReal (8192 * tailModulus (quantileTail μ ρ) ((1 / 2) ^ J) +
          1 / 2 * (2 * (1 / 2) ^ J * Real.sqrt ρ)) := ENNReal.ofReal_le_ofReal hreal
    _ = ENNReal.ofReal 8192 * ENNReal.ofReal (tailModulus (quantileTail μ ρ) ((1 / 2) ^ J)) +
          ENNReal.ofReal (1 / 2) * ENNReal.ofReal (2 * (1 / 2) ^ J * Real.sqrt ρ) := by
        rw [ENNReal.ofReal_add (mul_nonneg (by norm_num) hτ0) (by positivity),
          ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_mul (by norm_num)]
    _ ≤ ENNReal.ofReal 8192 * EntropyTail.selection μ ρ (4 ^ J) +
          ENNReal.ofReal (1 / 2) * EntropyTail.selection μ ρ (4 ^ J) := by gcongr
    _ = ENNReal.ofReal (8192 + 1 / 2) * EntropyTail.selection μ ρ (4 ^ J) := by
        rw [← add_mul, ← ENNReal.ofReal_add (by norm_num) (by norm_num)]
    _ ≤ ENNReal.ofReal 8193 * EntropyTail.selection μ ρ (4 ^ J) := by
        gcongr
        norm_num
    _ = 8193 * EntropyTail.selection μ ρ (4 ^ J) := by rw [ENNReal.ofReal_ofNat]

/-- The coin cap `M = ⌈√(64 · 4^J/ρ)⌉` satisfies `1/M ≤ √ρ 2^{-J}/8`. -/
theorem inv_pilotCoinCap_le (J : ℕ) {ρ : ℝ} (hρ : 0 < ρ) :
    1 / (pilotCoinCap J ρ : ℝ) ≤ Real.sqrt ρ * (1 / 2) ^ J / 8 := by
  have hs : 0 < Real.sqrt ρ := Real.sqrt_pos.mpr hρ
  have hT : (0 : ℝ) < 2 ^ J := by positivity
  have hx : (0 : ℝ) < 8 * 2 ^ J / Real.sqrt ρ := by positivity
  have hsq : 64 * (4 : ℝ) ^ J / ρ = (8 * 2 ^ J / Real.sqrt ρ) ^ 2 := by
    rw [div_pow, Real.sq_sqrt hρ.le, four_pow_eq]
    ring
  have hsqrt : Real.sqrt (64 * (4 : ℝ) ^ J / ρ) = 8 * 2 ^ J / Real.sqrt ρ := by
    rw [hsq, Real.sqrt_sq hx.le]
  have hM : 8 * 2 ^ J / Real.sqrt ρ ≤ (pilotCoinCap J ρ : ℝ) := by
    unfold pilotCoinCap
    rw [← hsqrt]
    exact Nat.le_ceil _
  calc 1 / (pilotCoinCap J ρ : ℝ) ≤ 1 / (8 * 2 ^ J / Real.sqrt ρ) :=
        one_div_le_one_div_of_le hx hM
    _ = Real.sqrt ρ * (1 / 2) ^ J / 8 := by
        rw [half_pow_eq]
        field_simp

/-- The coin cap against the oracle: `16/M ≤ K_{μ,ρ}(4^J)` once `2 · 2^{-J} ≤ √ρ`,
in particular under the pilot's onset condition. -/
theorem pilot_coin_cap_le_oracle (μ : Measure Gap) [IsProbabilityMeasure μ] {ρ : ℝ}
    (hρ : 0 < ρ) (hρ4 : ρ ≤ 1 / 4) (J : ℕ) (hsmall : 2 * (1 / 2 : ℝ) ^ J ≤ Real.sqrt ρ) :
    ENNReal.ofReal (16 / (pilotCoinCap J ρ : ℝ)) ≤ EntropyTail.selection μ ρ (4 ^ J) := by
  refine (ENNReal.ofReal_le_ofReal ?_).trans (selection_ge_scale μ hρ hρ4 J hsmall)
  have h := inv_pilotCoinCap_le J hρ
  have he : 16 / (pilotCoinCap J ρ : ℝ) = 16 * (1 / (pilotCoinCap J ρ : ℝ)) := by ring
  rw [he]
  linarith

/-- The elementary floor under the pilot's onset condition:
`2 · 2^{-J} √ρ ≤ K_{μ,ρ}(4^J)`. -/
theorem pilotOnset_floor (μ : Measure Gap) [IsProbabilityMeasure μ] {ρ : ℝ} (hρ : 0 < ρ)
    (hρ4 : ρ ≤ 1 / 4) {J : ℕ} (hon : PilotOnset μ ρ J) :
    ENNReal.ofReal (2 * (1 / 2) ^ J * Real.sqrt ρ) ≤ EntropyTail.selection μ ρ (4 ^ J) :=
  selection_ge_scale μ hρ hρ4 J (pilotOnset_small μ hρ (by linarith) hon)

/-- The coin cap under the pilot's onset condition: `16/M ≤ K_{μ,ρ}(4^J)`. -/
theorem pilotOnset_coin_cap (μ : Measure Gap) [IsProbabilityMeasure μ] {ρ : ℝ} (hρ : 0 < ρ)
    (hρ4 : ρ ≤ 1 / 4) {J : ℕ} (hon : PilotOnset μ ρ J) :
    ENNReal.ofReal (16 / (pilotCoinCap J ρ : ℝ)) ≤ EntropyTail.selection μ ρ (4 ^ J) :=
  pilot_coin_cap_le_oracle μ hρ hρ4 J (pilotOnset_small μ hρ (by linarith) hon)

end ThresholdHC.ArbitraryLawAdaptation
