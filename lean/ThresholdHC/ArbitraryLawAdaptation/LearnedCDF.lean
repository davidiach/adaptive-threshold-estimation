import ThresholdHC.ArbitraryLawAdaptation.PilotOnset
import ThresholdHC.ArbitraryLawAdaptation.TailPilotLaw
import ThresholdHC.ArbitraryLawAdaptation.LightMultiplier

/-! The learned law against the multiplier law: (A13) and (A14).

Let `V` be the light multiplier of (A3), independent of the gap `D ∼ μ`, and
let `μ' = L(V D / 2)`. The terminal estimate of the tail test bounds the
unresolved probability of one coin at depth `j` by the probability that
`V D ≤ 2^{-j}`, so

  `u_j ≤ P(V D ≤ 2^{-j}) = F_{μ'}(2^{-(j+1)})`.

When the pilot's certificates satisfy the upper half of (A8), the learned law
`μ̄` of (A9) therefore satisfies, at every point `x`,

  `F_{μ̄}(x) ≤ min{1, 128 F_{μ'}(x) + e}`,   `e = 128 w + 128/M + c_J`,

where `w` bounds `W_j/b_j` at every depth and `c_J` is the mass of the
learned law at zero. This is (A13), with a depth-independent `w` in place of
the maximum. Under the pilot's onset condition `e ≤ 2^22 K_{μ,ρ}(4^J)`, which
is (A14). These are deterministic statements about the gap law and the
certificates. `V`, `μ'` and `e` are proof quantities; the pilot neither
samples nor computes them. -/

noncomputable section
open MeasureTheory Real
open scoped ENNReal
namespace ThresholdHC.ArbitraryLawAdaptation
open ThresholdHC.Tier2 ThresholdHC.Tier6 ThresholdHC.EntropyTailQuantile

/-- The law `μ' = L(V D / 2)` of (A3): the gap `D ∼ μ` times an independent
light multiplier `V`, divided by two. -/
def lightLaw (μ : Measure Gap) : Measure Gap := (μ.prod lightMultiplier).map lightGap

instance lightLaw_probability (μ : Measure Gap) [IsProbabilityMeasure μ] :
    IsProbabilityMeasure (lightLaw μ) := by
  unfold lightLaw
  infer_instance

/-- The mass of `μ'` at gaps at most `2^{-(j+1)}` is the probability that
`V D ≤ 2^{-j}`. -/
theorem lightLaw_apply_le (μ : Measure Gap) (j : ℕ) :
    lightLaw μ {y : Gap | (y : ℝ) ≤ (1 / 2) ^ (j + 1)} =
      (μ.prod lightMultiplier) {z : Gap × Gap | (z.1 : ℝ) * (z.2 : ℝ) ≤ (1 / 2) ^ j} := by
  have hS : MeasurableSet {y : Gap | (y : ℝ) ≤ (1 / 2) ^ (j + 1)} :=
    measurableSet_le measurable_subtype_coe measurable_const
  unfold lightLaw
  rw [Measure.map_apply measurable_lightGap hS]
  congr 1
  ext z
  change (z.1 : ℝ) * (z.2 : ℝ) / 2 ≤ (1 / 2) ^ (j + 1) ↔ (z.1 : ℝ) * (z.2 : ℝ) ≤ (1 / 2) ^ j
  rw [pow_succ, div_le_iff₀ (by norm_num : (0 : ℝ) < 2)]
  constructor <;> intro h <;> linarith

/-- `u_j ≤ F_{μ'}(2^{-(j+1)})`: the unresolved probability of one coin at depth
`j` is at most the mass of `μ'` at gaps at most `2^{-(j+1)}`. This restates the
terminal estimate of the tail test for the law `μ'`. -/
theorem tailUnresolvedMass_le_light (μ : Measure Gap) [IsProbabilityMeasure μ] (j : ℕ) :
    tailUnresolvedMass μ j ≤ (lightLaw μ).real {y : Gap | (y : ℝ) ≤ (1 / 2) ^ (j + 1)} := by
  have hu0 : 0 ≤ tailUnresolvedMass μ j := integral_nonneg (tailUnresolvedProb_nonneg j)
  have h2 : ENNReal.ofReal (tailUnresolvedMass μ j) ≤
      lightLaw μ {y : Gap | (y : ℝ) ≤ (1 / 2) ^ (j + 1)} := by
    rw [lightLaw_apply_le]
    exact tail_unresolved_mass_le_multiplier μ j
  have h3 := ENNReal.toReal_mono (measure_ne_top (lightLaw μ) _) h2
  rwa [ENNReal.toReal_ofReal hu0] at h3

/-- An upper bound for the envelope's distribution function above the last
grid point, from bounds at the grid points. -/
theorem envelopeCDF_le_above {G : ℝ → ℝ} {c : ℕ → ℝ} (hG : Monotone G) (n : ℕ) :
    ∀ x : ℝ, gridPoint (n + 1) ≤ x → (∀ j, j < n + 1 → c j ≤ G (gridPoint (j + 1))) →
      envelopeCDF c n x ≤ G x := by
  induction n with
  | zero =>
    intro x hx hgrid
    have hx0 : 0 ≤ x := (gridPoint_pos 1).le.trans hx
    have hval : envelopeCDF c 0 x = c 0 := by simp [envelopeCDF, hx0]
    rw [hval]
    exact (hgrid 0 (by norm_num)).trans (hG hx)
  | succ n ih =>
    intro x hx hgrid
    have hx0 : 0 ≤ x := (gridPoint_pos (n + 2)).le.trans hx
    by_cases hg : gridPoint (n + 1) ≤ x
    · rw [envelopeCDF_succ_above hg]
      exact ih x hg fun j hj => hgrid j (by omega)
    · rw [envelopeCDF_below_grid hx0 (lt_of_not_ge hg)]
      exact (hgrid (n + 1) (by omega)).trans (hG hx)

/-- An upper bound for the envelope's distribution function at every point:
it suffices to bound the mass at zero by `G 0` and the prefix value `c j` by
`G` at the grid point `2^{-(j+2)}`, for a monotone nonnegative `G`. -/
theorem envelopeCDF_le {G : ℝ → ℝ} {c : ℕ → ℝ} {n : ℕ} (hG : Monotone G)
    (hneg : ∀ x : ℝ, x < 0 → 0 ≤ G x) (hzero : c n ≤ G 0)
    (hgrid : ∀ j, j < n → c j ≤ G (gridPoint (j + 1))) (x : ℝ) :
    envelopeCDF c n x ≤ G x := by
  by_cases hx : 0 ≤ x
  · cases n with
    | zero =>
      have hval : envelopeCDF c 0 x = c 0 := by simp [envelopeCDF, hx]
      rw [hval]
      exact hzero.trans (hG hx)
    | succ n =>
      by_cases hg : gridPoint (n + 1) ≤ x
      · rw [envelopeCDF_succ_above hg]
        exact envelopeCDF_le_above hG n x hg hgrid
      · rw [envelopeCDF_below_grid hx (lt_of_not_ge hg)]
        exact hzero.trans (hG hx)
  · have hval : envelopeCDF c n x = 0 := by simp [envelopeCDF, hx]
    rw [hval]
    exact hneg x (lt_of_not_ge hx)

/-- A bound on `W_j/b_j` that does not depend on the depth `1 ≤ j ≤ J`:
`8192 τ_ν(2^{-J}) + 2048 (J+1)³ (2^{-J})²/a²`. -/
def pilotWorkBound (μ : Measure Gap) (ρ : ℝ) (J : ℕ) : ℝ :=
  8192 * tailModulus (quantileTail μ ρ) ((1 / 2) ^ J) +
    2048 * ((J : ℝ) + 1) ^ 3 * ((1 / 2) ^ J) ^ 2 / (quantileThreshold μ ρ) ^ 2

/-- The slack `e` of (A13): `128 w + 128/M + c`, where `c` is the mass of the
learned law at zero. -/
def learnedSlack (μ : Measure Gap) (ρ : ℝ) (J : ℕ) (c : ℝ) : ℝ :=
  128 * pilotWorkBound μ ρ J + 128 / (pilotCoinCap J ρ : ℝ) + c

theorem pilotWorkBound_nonneg (μ : Measure Gap) (ρ : ℝ) (J : ℕ) : 0 ≤ pilotWorkBound μ ρ J := by
  unfold pilotWorkBound
  have h := tailModulus_nonneg (quantileTail μ ρ) (by positivity : (0 : ℝ) ≤ (1 / 2) ^ J)
  positivity

theorem le_learnedSlack (μ : Measure Gap) (ρ : ℝ) (J : ℕ) (c : ℝ) : c ≤ learnedSlack μ ρ J c := by
  unfold learnedSlack
  have h1 := pilotWorkBound_nonneg μ ρ J
  have h2 : (0 : ℝ) ≤ 128 / (pilotCoinCap J ρ : ℝ) := by positivity
  linarith

/-- (A8) at depth `j` with the depth-independent work bound:
`128 (u_j + W_j/b_j + 1/M) ≤ 128 F_{μ'}(2^{-(j+1)}) + 128 w + 128/M`. -/
theorem pilotBound_le_light (μ : Measure Gap) [IsProbabilityMeasure μ] {ρ : ℝ} (hρ : 0 < ρ)
    (hρ1 : ρ ≤ 1) {J j : ℕ} (hj1 : 1 ≤ j) (hjJ : j ≤ J) :
    pilotBound μ J ρ j ≤
      128 * (lightLaw μ).real {y : Gap | (y : ℝ) ≤ (1 / 2) ^ (j + 1)} +
        128 * pilotWorkBound μ ρ J + 128 / (pilotCoinCap J ρ : ℝ) := by
  have hu := tailUnresolvedMass_le_light μ j
  have hw : (∫ d : Gap, tailWorkEnvelope j d ∂μ) / (pilotBudget J j : ℝ) ≤ pilotWorkBound μ ρ J :=
    pilot_work_le μ hρ hρ1 hj1 hjJ
  unfold pilotBound
  have he : 128 / (pilotCoinCap J ρ : ℝ) = 128 * (1 / (pilotCoinCap J ρ : ℝ)) := by ring
  rw [he]
  linarith

/-- (A13). Let `U i` be certificates of the depths `i + 1 ≤ J` that satisfy
the upper half of (A8), with `U 0 = 1`. The law learned from them, with prefix
minima `c`, satisfies `F_{μ̄}(x) ≤ min{1, 128 F_{μ'}(x) + e}` at every point
`x`, zero and the grid points included, where `e = 128 w + 128/M + c_J`. -/
theorem learned_cdf_le (μ : Measure Gap) [IsProbabilityMeasure μ] {ρ : ℝ} (hρ : 0 < ρ)
    (hρ1 : ρ ≤ 1) {J : ℕ} (U : ℕ → ℝ) (hU0 : ∀ i, 0 ≤ U i) (hU1 : U 0 = 1)
    (hbound : ∀ i, i < J → U i ≤ pilotBound μ J ρ (i + 1)) (x : ℝ) :
    envelopeLaw (prefixMinimum U) (J - 1) (Set.Iic x) ≤
      ENNReal.ofReal (min 1 (128 * (lightLaw μ).real {y : Gap | (y : ℝ) ≤ x} +
        learnedSlack μ ρ J (prefixMinimum U (J - 1)))) := by
  have hc0 : ∀ j, 0 ≤ prefixMinimum U j := prefixMinimum_nonneg hU0
  have hmono : Antitone (prefixMinimum U) := prefixMinimum_antitone U
  have hc1 : ∀ j, prefixMinimum U j ≤ 1 := fun j => by
    have h := hmono (Nat.zero_le j)
    have h0 : prefixMinimum U 0 = U 0 := rfl
    rw [h0, hU1] at h
    exact h
  have hF0 : ∀ y : ℝ, 0 ≤ (lightLaw μ).real {z : Gap | (z : ℝ) ≤ y} := fun _ => measureReal_nonneg
  have hFmono : Monotone fun y : ℝ => (lightLaw μ).real {z : Gap | (z : ℝ) ≤ y} := by
    intro y z hyz
    exact measureReal_mono fun d (hd : (d : ℝ) ≤ y) => le_trans hd hyz
  have he := le_learnedSlack μ ρ J (prefixMinimum U (J - 1))
  have he0 : 0 ≤ learnedSlack μ ρ J (prefixMinimum U (J - 1)) := (hc0 _).trans he
  rw [envelopeLaw_Iic hc0 hmono]
  refine ENNReal.ofReal_le_ofReal ?_
  refine envelopeCDF_le
    (G := fun y : ℝ => min 1 (128 * (lightLaw μ).real {z : Gap | (z : ℝ) ≤ y} +
      learnedSlack μ ρ J (prefixMinimum U (J - 1)))) ?_ ?_ ?_ ?_ x
  · intro y z hyz
    exact min_le_min le_rfl (by linarith [hFmono hyz])
  · intro y _
    exact le_min zero_le_one (by linarith [hF0 y])
  · exact le_min (hc1 _) (by linarith [hF0 0])
  · intro j hj
    have hjJ : j + 1 ≤ J := by omega
    have h1 : prefixMinimum U j ≤ U j := prefixMinimum_le U j
    have h2 := hbound j (by omega)
    have h3 := pilotBound_le_light μ hρ hρ1 (Nat.succ_le_succ (Nat.zero_le j)) hjJ
    have hgp : gridPoint (j + 1) = (1 / 2 : ℝ) ^ (j + 1 + 1) := rfl
    refine le_min (hc1 j) ?_
    rw [hgp]
    unfold learnedSlack
    linarith [hc0 (J - 1)]

/-- The depth-independent work bound against the oracle. Under the pilot's
onset condition, `w ≤ 8193 K_{μ,ρ}(4^J)`. -/
theorem pilotWorkBound_le_oracle (μ : Measure Gap) [IsProbabilityMeasure μ] {ρ : ℝ}
    (hρ : 0 < ρ) (hρ4 : ρ ≤ 1 / 4) {J : ℕ} (hon : PilotOnset μ ρ J) :
    ENNReal.ofReal (pilotWorkBound μ ρ J) ≤ 8193 * EntropyTail.selection μ ρ (4 ^ J) := by
  have hρ1 : ρ ≤ 1 := by linarith
  have ht : (0 : ℝ) < (1 / 2) ^ J := by positivity
  have hτ0 : 0 ≤ tailModulus (quantileTail μ ρ) ((1 / 2) ^ J) := tailModulus_nonneg _ ht.le
  have hK := pilotOnset_floor μ hρ hρ4 hon
  have hfloor := quantile_tail_floor μ hρ hρ1 J
  have hcore : 2048 * ((J : ℝ) + 1) ^ 3 * ((1 / 2) ^ J) ^ 2 / (quantileThreshold μ ρ) ^ 2 ≤
      1 / 2 * (2 * (1 / 2) ^ J * Real.sqrt ρ) := by
    unfold PilotOnset at hon
    calc 2048 * ((J : ℝ) + 1) ^ 3 * ((1 / 2) ^ J) ^ 2 / (quantileThreshold μ ρ) ^ 2
        = (1 / 2) ^ J *
            (2048 * ((J : ℝ) + 1) ^ 3 * (1 / 2) ^ J / (quantileThreshold μ ρ) ^ 2) := by ring
      _ ≤ (1 / 2) ^ J * Real.sqrt ρ := mul_le_mul_of_nonneg_left hon ht.le
      _ = 1 / 2 * (2 * (1 / 2) ^ J * Real.sqrt ρ) := by ring
  have hreal : pilotWorkBound μ ρ J ≤
      8192 * tailModulus (quantileTail μ ρ) ((1 / 2) ^ J) +
        1 / 2 * (2 * (1 / 2) ^ J * Real.sqrt ρ) := by
    unfold pilotWorkBound
    linarith
  calc ENNReal.ofReal (pilotWorkBound μ ρ J)
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

/-- The explicit constant behind (A14). Under the pilot's onset condition,
when the certificate of the deepest depth satisfies the upper half of (A8),
the slack of (A13) is at most `(256 · 8193 + 16 + 128 · 4096) K_{μ,ρ}(4^J)`. -/
theorem learnedSlack_le_explicit (μ : Measure Gap) [IsProbabilityMeasure μ] {ρ : ℝ}
    (hρ : 0 < ρ) (hρ4 : ρ ≤ 1 / 4) {J : ℕ} (hJ : 1 ≤ J) (hon : PilotOnset μ ρ J) (U : ℕ → ℝ)
    (hbound : U (J - 1) ≤ pilotBound μ J ρ J) :
    ENNReal.ofReal (learnedSlack μ ρ J (prefixMinimum U (J - 1))) ≤
      2621712 * EntropyTail.selection μ ρ (4 ^ J) := by
  have hρ1 : ρ ≤ 1 := by linarith
  have hw0 := pilotWorkBound_nonneg μ ρ J
  have hu0 : 0 ≤ tailUnresolvedMass μ J := integral_nonneg (tailUnresolvedProb_nonneg J)
  have hM0 : (0 : ℝ) ≤ 16 / (pilotCoinCap J ρ : ℝ) := by positivity
  have hW0 : 0 ≤ (∫ d : Gap, tailWorkEnvelope J d ∂μ) / 4 ^ J :=
    div_nonneg (integral_nonneg fun d => tailWorkEnvelope_nonneg J d) (by positivity)
  -- The real inequality `e ≤ 256 w + 16 (16/M) + 128 u_J`.
  have hc : prefixMinimum U (J - 1) ≤ U (J - 1) := prefixMinimum_le U (J - 1)
  have hwork : (∫ d : Gap, tailWorkEnvelope J d ∂μ) / (pilotBudget J J : ℝ) ≤
      pilotWorkBound μ ρ J := pilot_work_le μ hρ hρ1 hJ le_rfl
  have hreal : learnedSlack μ ρ J (prefixMinimum U (J - 1)) ≤
      256 * pilotWorkBound μ ρ J + 16 * (16 / (pilotCoinCap J ρ : ℝ)) +
        128 * tailUnresolvedMass μ J := by
    unfold pilotBound at hbound
    unfold learnedSlack
    have he : 128 / (pilotCoinCap J ρ : ℝ) = 8 * (16 / (pilotCoinCap J ρ : ℝ)) := by ring
    have he' : 1 / (pilotCoinCap J ρ : ℝ) = 1 / 16 * (16 / (pilotCoinCap J ρ : ℝ)) := by ring
    rw [he' ] at hbound
    rw [he]
    linarith
  -- The three oracle bounds.
  have hw := pilotWorkBound_le_oracle μ hρ hρ4 hon
  have hM := pilotOnset_coin_cap μ hρ hρ4 hon
  have hu : ENNReal.ofReal (tailUnresolvedMass μ J) ≤
      4096 * EntropyTail.selection μ ρ (4 ^ J) :=
    (ENNReal.ofReal_le_ofReal (by linarith)).trans
      (tail_oracle_comparison μ hρ hρ4 J (pilotOnset_tailOnset hon))
  calc ENNReal.ofReal (learnedSlack μ ρ J (prefixMinimum U (J - 1)))
      ≤ ENNReal.ofReal (256 * pilotWorkBound μ ρ J + 16 * (16 / (pilotCoinCap J ρ : ℝ)) +
          128 * tailUnresolvedMass μ J) := ENNReal.ofReal_le_ofReal hreal
    _ = 256 * ENNReal.ofReal (pilotWorkBound μ ρ J) +
          16 * ENNReal.ofReal (16 / (pilotCoinCap J ρ : ℝ)) +
          128 * ENNReal.ofReal (tailUnresolvedMass μ J) := by
        rw [ENNReal.ofReal_add (by positivity) (by positivity),
          ENNReal.ofReal_add (by positivity) (by positivity),
          ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_mul (by norm_num),
          ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat, ENNReal.ofReal_ofNat,
          ENNReal.ofReal_ofNat]
    _ ≤ 256 * (8193 * EntropyTail.selection μ ρ (4 ^ J)) +
          16 * EntropyTail.selection μ ρ (4 ^ J) +
          128 * (4096 * EntropyTail.selection μ ρ (4 ^ J)) := by gcongr
    _ = 2621712 * EntropyTail.selection μ ρ (4 ^ J) := by ring

/-- (A14). Under the pilot's onset condition, when the certificate of the
deepest depth satisfies the upper half of (A8), the slack of (A13) is at most
`2^22 K_{μ,ρ}(4^J)`; `4194304 = 2^22`. -/
theorem learnedSlack_le_oracle (μ : Measure Gap) [IsProbabilityMeasure μ] {ρ : ℝ} (hρ : 0 < ρ)
    (hρ4 : ρ ≤ 1 / 4) {J : ℕ} (hJ : 1 ≤ J) (hon : PilotOnset μ ρ J) (U : ℕ → ℝ)
    (hbound : U (J - 1) ≤ pilotBound μ J ρ J) :
    ENNReal.ofReal (learnedSlack μ ρ J (prefixMinimum U (J - 1))) ≤
      4194304 * EntropyTail.selection μ ρ (4 ^ J) := by
  refine (learnedSlack_le_explicit μ hρ hρ4 hJ hon U hbound).trans ?_
  gcongr
  norm_num

/-- Under the pilot's onset condition the selection functional is positive
and finite. -/
theorem pilotOnset_selection_pos (μ : Measure Gap) [IsProbabilityMeasure μ] {ρ : ℝ}
    (hρ : 0 < ρ) (hρ4 : ρ ≤ 1 / 4) {J : ℕ} (hon : PilotOnset μ ρ J) :
    EntropyTail.selection μ ρ (4 ^ J) ≠ ⊤ ∧
      0 < (EntropyTail.selection μ ρ (4 ^ J)).toReal := by
  have htop : EntropyTail.selection μ ρ (4 ^ J) ≠ ⊤ :=
    ((EntropyTail.selection_le_rho μ ρ (4 ^ J)).trans_lt ENNReal.ofReal_lt_top).ne
  have hfloor := pilotOnset_floor μ hρ hρ4 hon
  have hpos : (0 : ℝ) < 2 * (1 / 2) ^ J * Real.sqrt ρ := by positivity
  have hne : EntropyTail.selection μ ρ (4 ^ J) ≠ 0 := fun h0 => by
    rw [h0, nonpos_iff_eq_zero, ENNReal.ofReal_eq_zero] at hfloor
    linarith
  exact ⟨htop, ENNReal.toReal_pos hne htop⟩

/-- (A14) with the strict inequality of the paper: `e < 2^22 K_{μ,ρ}(4^J)`. -/
theorem learnedSlack_lt_oracle (μ : Measure Gap) [IsProbabilityMeasure μ] {ρ : ℝ} (hρ : 0 < ρ)
    (hρ4 : ρ ≤ 1 / 4) {J : ℕ} (hJ : 1 ≤ J) (hon : PilotOnset μ ρ J) (U : ℕ → ℝ)
    (hbound : U (J - 1) ≤ pilotBound μ J ρ J) :
    ENNReal.ofReal (learnedSlack μ ρ J (prefixMinimum U (J - 1))) <
      4194304 * EntropyTail.selection μ ρ (4 ^ J) := by
  obtain ⟨htop, hpos⟩ := pilotOnset_selection_pos μ hρ hρ4 hon
  have hle := learnedSlack_le_explicit μ hρ hρ4 hJ hon U hbound
  have hK : EntropyTail.selection μ ρ (4 ^ J) =
      ENNReal.ofReal (EntropyTail.selection μ ρ (4 ^ J)).toReal :=
    (ENNReal.ofReal_toReal htop).symm
  rw [hK, ← ENNReal.ofReal_ofNat 2621712, ← ENNReal.ofReal_mul (by norm_num)] at hle
  rw [hK, ← ENNReal.ofReal_ofNat 4194304, ← ENNReal.ofReal_mul (by norm_num)]
  refine lt_of_le_of_lt hle ((ENNReal.ofReal_lt_ofReal_iff (by positivity)).mpr ?_)
  nlinarith

end ThresholdHC.ArbitraryLawAdaptation
