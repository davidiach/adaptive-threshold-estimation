import ThresholdHC.OracleUpper.Thinning
import ThresholdHC.OracleUpper.Specification
import ThresholdHC.Tier6.HardPair
import ThresholdHC.Tier6.AlgorithmNonempty

/-! The parameters of the thinning estimators and the final bound. With n
the floor of the budget, the threshold is t = 1/(2 sqrt n) and A is the
integral of 1/d over gaps at least t. The window has m = ceil(n/(t A))
indices and the acceptance probability at a gap d at least t is r/d with
r = n/(m A), so the expected number of flips is m r A = n. The output is one
half plus 1/(4 r m) times the sum of the signed flips. Its bias is the
integral of 1/2 - q over gaps below t, at most half their mass, and its
variance is at most A²/(16 n) = (t A/2)². Since the modulus at t is the mass
below t plus t A, the root mean squared error is at most half the modulus at
t. When A = 0 the window is empty, the output is one half and the modulus at
t is one. -/
noncomputable section
namespace ThresholdHC.OracleUpper
open MeasureTheory
open scoped ENNReal
open ThresholdHC ThresholdHC.Tier3 ThresholdHC.Tier6 ThresholdHC.OracleLower

/-- The threshold 1/(2 sqrt n). -/
def floorScale (n : ℕ) : ℝ := 1 / (2 * Real.sqrt n)

/-- The part of the inverse gap at gaps at least t. -/
def invPart (t : ℝ) (d : Gap) : ℝ := if t ≤ (d : ℝ) then 1 / (d : ℝ) else 0

/-- The indicator of gaps below t. -/
def lowPart (t : ℝ) (d : Gap) : ℝ := if t ≤ (d : ℝ) then 0 else 1

/-- The inverse-gap mass A at gaps at least t. -/
def upperInvMass (μ : Measure Gap) (t : ℝ) : ℝ := ∫ d, invPart t d ∂μ

/-- The window length m = ceil(n/(t A)). -/
def thinWindow (μ : Measure Gap) (n : ℕ) : ℕ :=
  ⌈(n : ℝ) / (floorScale n * upperInvMass μ (floorScale n))⌉₊

/-- The acceptance rate r = n/(m A). -/
def thinRate (μ : Measure Gap) (n : ℕ) : ℝ :=
  (n : ℝ) / (thinWindow μ n * upperInvMass μ (floorScale n))

/-- The output scale 1/(4 r m). -/
def thinScale (μ : Measure Gap) (n : ℕ) : ℝ := 1 / (4 * thinRate μ n * thinWindow μ n)

/-- The acceptance probability r/d at gaps at least t. -/
def acceptProb (t r : ℝ) (d : Gap) : ℝ := if t ≤ (d : ℝ) then r / d else 0

theorem rms_le_of_sq {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (g : Ω → ℝ)
    (θ x : ℝ) (hx : 0 ≤ x) (h : squaredRisk P g θ ≤ ENNReal.ofReal (x^2)) :
    rootMeanRisk P g θ ≤ ENNReal.ofReal x := by
  unfold rootMeanRisk
  calc
    squaredRisk P g θ ^ (1/2 : ℝ) ≤ ENNReal.ofReal (x^2) ^ (1/2 : ℝ) :=
      ENNReal.rpow_le_rpow h (by norm_num)
    _ = ENNReal.ofReal x := by
      rw [ENNReal.ofReal_rpow_of_nonneg (sq_nonneg x) (by norm_num), ← Real.sqrt_eq_rpow,
        Real.sqrt_sq hx]

theorem modulus_le_of_le (μ : Measure Gap) [IsProbabilityMeasure μ] {x y : ℝ}
    (hx : 0 ≤ x) (hxy : x ≤ y) : modulus μ x ≤ modulus μ y :=
  integral_mono (integrable_clippedGap μ hx) (integrable_clippedGap μ (hx.trans hxy))
    (fun d => min_le_min_left _ (div_le_div_of_nonneg_right hxy d.property.1.le))

theorem floorScale_pos {n : ℕ} (hn : 1 ≤ n) : 0 < floorScale n := by
  unfold floorScale
  have : 0 < Real.sqrt n := Real.sqrt_pos.mpr (by exact_mod_cast hn)
  positivity

theorem floorScale_sq {n : ℕ} (hn : 1 ≤ n) : (floorScale n)^2 = 1 / (4 * n) := by
  unfold floorScale
  have hs : Real.sqrt (n : ℝ) ^ 2 = n := Real.sq_sqrt (Nat.cast_nonneg n)
  have : 0 < Real.sqrt n := Real.sqrt_pos.mpr (by exact_mod_cast hn)
  field_simp
  rw [hs]
  norm_num

theorem measurable_invPart (t : ℝ) : Measurable (invPart t) :=
  Measurable.ite (measurableSet_le measurable_const measurable_subtype_coe)
    (measurable_const.div measurable_subtype_coe) measurable_const

theorem measurable_lowPart (t : ℝ) : Measurable (lowPart t) :=
  Measurable.ite (measurableSet_le measurable_const measurable_subtype_coe)
    measurable_const measurable_const

theorem measurable_acceptProb (t r : ℝ) : Measurable (acceptProb t r) :=
  Measurable.ite (measurableSet_le measurable_const measurable_subtype_coe)
    (measurable_const.div measurable_subtype_coe) measurable_const

theorem invPart_nonneg (t : ℝ) (d : Gap) : 0 ≤ invPart t d := by
  unfold invPart
  split_ifs
  · exact one_div_nonneg.mpr d.property.1.le
  · exact le_rfl

theorem abs_invPart_le {t : ℝ} (ht : 0 < t) (d : Gap) : |invPart t d| ≤ 1 / t := by
  rw [abs_of_nonneg (invPart_nonneg t d)]
  unfold invPart
  split_ifs with h
  · exact one_div_le_one_div_of_le ht h
  · positivity

theorem abs_lowPart_le (t : ℝ) (d : Gap) : |lowPart t d| ≤ 1 := by
  unfold lowPart
  split_ifs <;> simp

theorem upperInvMass_nonneg (μ : Measure Gap) (t : ℝ) : 0 ≤ upperInvMass μ t :=
  integral_nonneg (invPart_nonneg t)

theorem integrable_invPart (μ : Measure Gap) [IsProbabilityMeasure μ] {t : ℝ} (ht : 0 < t) :
    Integrable (invPart t) μ :=
  integrable_of_abs_le μ _ (measurable_invPart t) _ (abs_invPart_le ht)

theorem integrable_lowPart (μ : Measure Gap) [IsProbabilityMeasure μ] (t : ℝ) :
    Integrable (lowPart t) μ :=
  integrable_of_abs_le μ _ (measurable_lowPart t) _ (abs_lowPart_le t)

theorem lowPart_integral_nonneg (μ : Measure Gap) (t : ℝ) : 0 ≤ ∫ d, lowPart t d ∂μ :=
  integral_nonneg fun d => by unfold lowPart; split_ifs <;> norm_num

theorem thinRate_nonneg (μ : Measure Gap) (n : ℕ) : 0 ≤ thinRate μ n :=
  div_nonneg (Nat.cast_nonneg _) (mul_nonneg (Nat.cast_nonneg _) (upperInvMass_nonneg _ _))

/-- With positive A the window is nonempty and n ≤ t m A, that is, the rate r
is at most t. -/
theorem thin_window_pos (μ : Measure Gap) {n : ℕ} (hn : 1 ≤ n)
    (hA : 0 < upperInvMass μ (floorScale n)) :
    0 < (thinWindow μ n : ℝ) ∧
      (n : ℝ) ≤ floorScale n * (thinWindow μ n * upperInvMass μ (floorScale n)) := by
  have ht := floorScale_pos hn
  have hm : (n : ℝ) / (floorScale n * upperInvMass μ (floorScale n)) ≤ thinWindow μ n :=
    Nat.le_ceil _
  have hpos : 0 < (n : ℝ) / (floorScale n * upperInvMass μ (floorScale n)) :=
    div_pos (by exact_mod_cast hn) (mul_pos ht hA)
  refine ⟨hpos.trans_le hm, ?_⟩
  have h := (div_le_iff₀ (mul_pos ht hA)).mp hm
  nlinarith

theorem thinRate_le (μ : Measure Gap) {n : ℕ} (hn : 1 ≤ n) :
    thinRate μ n ≤ floorScale n := by
  have ht := floorScale_pos hn
  rcases (upperInvMass_nonneg μ (floorScale n)).eq_or_lt with h | h
  · unfold thinRate
    rw [← h]
    simp only [mul_zero, div_zero]
    exact ht.le
  · obtain ⟨hm, hle⟩ := thin_window_pos μ hn h
    unfold thinRate
    rw [div_le_iff₀ (mul_pos hm h)]
    linarith

theorem acceptProb_mem (μ : Measure Gap) {n : ℕ} (hn : 1 ≤ n) (d : Gap) :
    0 ≤ acceptProb (floorScale n) (thinRate μ n) d ∧
      acceptProb (floorScale n) (thinRate μ n) d ≤ 1 := by
  unfold acceptProb
  split_ifs with h
  · refine ⟨div_nonneg (thinRate_nonneg μ n) d.property.1.le, ?_⟩
    rw [div_le_one d.property.1]
    exact (thinRate_le μ hn).trans h
  · exact ⟨le_rfl, zero_le_one⟩

theorem integral_acceptProb (μ : Measure Gap) (t r : ℝ) :
    ∫ d, acceptProb t r d ∂μ = r * upperInvMass μ t := by
  unfold upperInvMass
  rw [← integral_const_mul]
  congr 1
  funext d
  unfold acceptProb invPart
  split_ifs
  · ring
  · ring

/-- The centered sign `2q - 1` at gaps at least `t` and zero below; the
acceptance-weighted flip mean is `2r` times this. -/
def upperSign (q : SignLaw) (t : ℝ) (d : Gap) : ℝ := if t ≤ (d : ℝ) then 2 * q.val d - 1 else 0

theorem integral_accept_flip (μ : Measure Gap) (q : SignLaw) (t r : ℝ) :
    ∫ d, acceptProb t r d * flipMean q d ∂μ = 2 * r * ∫ d, upperSign q t d ∂μ := by
  rw [← integral_const_mul]
  congr 1
  funext d
  unfold acceptProb flipMean upperSign
  have hd : (d : ℝ) ≠ 0 := d.property.1.ne'
  split_ifs
  · field_simp
  · ring

theorem modulus_split (μ : Measure Gap) [IsProbabilityMeasure μ] {t : ℝ} (ht : 0 < t) :
    modulus μ t = t * upperInvMass μ t + ∫ d, lowPart t d ∂μ := by
  unfold modulus upperInvMass
  rw [← integral_const_mul, ← integral_add ((integrable_invPart μ ht).const_mul t)
    (integrable_lowPart μ t)]
  congr 1
  funext d
  unfold clippedGap invPart lowPart
  have hd := d.property.1
  split_ifs with h
  · rw [min_eq_right ((div_le_one hd).mpr h)]
    ring
  · rw [min_eq_left ((one_le_div hd).mpr (le_of_lt (lt_of_not_ge h)))]
    ring

/-- The mass below t is at least one minus half of A, since every gap is at most one half. -/
theorem lowPart_ge (μ : Measure Gap) [IsProbabilityMeasure μ] {t : ℝ} (ht : 0 < t) :
    1 - upperInvMass μ t / 2 ≤ ∫ d, lowPart t d ∂μ := by
  have hle : ∫ d, (1 - lowPart t d) ∂μ ≤ ∫ d, invPart t d / 2 ∂μ := by
    apply integral_mono ((integrable_const 1).sub (integrable_lowPart μ t))
      ((integrable_invPart μ ht).div_const 2)
    intro d
    show 1 - lowPart t d ≤ invPart t d / 2
    unfold lowPart invPart
    have h1 := d.property.1
    have h2 := d.property.2
    split_ifs
    · rw [le_div_iff₀ (by norm_num : (0:ℝ) < 2), sub_zero, one_mul, le_div_iff₀ h1]
      linarith
    · norm_num
  rw [integral_sub (integrable_const 1) (integrable_lowPart μ t), integral_div] at hle
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul] at hle
  unfold upperInvMass
  linarith

theorem bias_eq (μ : Measure Gap) [IsProbabilityMeasure μ] (q : SignLaw) (t : ℝ) :
    1/2 - signMean μ q.val + (1/2) * ∫ d, upperSign q t d ∂μ =
      ∫ d, (if t ≤ (d : ℝ) then 0 else 1/2 - q.val d) ∂μ := by
  have hq : Integrable q.val μ := integrable_of_abs_le μ _ q.property.1 1 (fun d => by
    rw [abs_of_nonneg (q.property.2 d).1]; exact (q.property.2 d).2)
  have hs : Integrable (upperSign q t) μ := integrable_of_abs_le μ _
    (Measurable.ite (measurableSet_le measurable_const measurable_subtype_coe)
      ((measurable_const.mul q.property.1).sub measurable_const) measurable_const) 1 (fun d => by
      unfold upperSign
      have := q.property.2 d
      split_ifs
      · rw [abs_le]; constructor <;> linarith
      · simp)
  have hpt : (fun d : Gap => if t ≤ (d : ℝ) then 0 else 1/2 - q.val d) =
      fun d => (1/2 - q.val d) + (1/2) * upperSign q t d := by
    funext d
    unfold upperSign
    split_ifs <;> ring
  have h1 : Integrable (fun d : Gap => 1/2 - q.val d) μ := (integrable_const _).sub hq
  have h2 : Integrable (fun d : Gap => (1/2) * upperSign q t d) μ := hs.const_mul _
  have e1 : ∫ d, ((1/2 - q.val d) + (1/2) * upperSign q t d) ∂μ =
      ∫ d, (1/2 - q.val d) ∂μ + ∫ d, (1/2) * upperSign q t d ∂μ := integral_add h1 h2
  have e2 : ∫ d, (1/2 - q.val d) ∂μ = ∫ _d, (1/2 : ℝ) ∂μ - ∫ d, q.val d ∂μ :=
    integral_sub (integrable_const _) hq
  have e3 : ∫ d, (1/2) * upperSign q t d ∂μ = (1/2) * ∫ d, upperSign q t d ∂μ :=
    integral_const_mul _ _
  have e4 : ∫ _d, (1/2 : ℝ) ∂μ = 1/2 := by simp
  rw [hpt, e1, e2, e3, e4]
  rfl

theorem bias_abs_le (μ : Measure Gap) [IsProbabilityMeasure μ] (q : SignLaw) (t : ℝ) :
    |∫ d, (if t ≤ (d : ℝ) then 0 else 1/2 - q.val d) ∂μ| ≤ (1/2) * ∫ d, lowPart t d ∂μ := by
  have hb : Integrable (fun d : Gap => if t ≤ (d : ℝ) then 0 else 1/2 - q.val d) μ :=
    integrable_of_abs_le μ _ (Measurable.ite (measurableSet_le measurable_const
      measurable_subtype_coe) measurable_const (measurable_const.sub q.property.1)) 1 (fun d => by
        have := q.property.2 d
        split_ifs
        · simp
        · rw [abs_le]; constructor <;> linarith)
  have up : ∫ d, (if t ≤ (d : ℝ) then 0 else 1/2 - q.val d) ∂μ ≤
      ∫ d, (1/2) * lowPart t d ∂μ := by
    apply integral_mono hb ((integrable_lowPart μ t).const_mul _)
    intro d
    have := q.property.2 d
    dsimp only
    unfold lowPart
    split_ifs <;> linarith
  have lo : ∫ d, (-(1/2)) * lowPart t d ∂μ ≤
      ∫ d, (if t ≤ (d : ℝ) then 0 else 1/2 - q.val d) ∂μ := by
    apply integral_mono ((integrable_lowPart μ t).const_mul _) hb
    intro d
    have := q.property.2 d
    dsimp only
    unfold lowPart
    split_ifs <;> linarith
  rw [integral_const_mul] at up lo
  rw [abs_le]
  constructor <;> linarith

/-- The squared risk of both thinning estimators is at most the square of half
the modulus at the threshold. -/
theorem thin_risk_le (μ : Measure Gap) [IsProbabilityMeasure μ] (q : SignLaw) {n : ℕ}
    (hn : 1 ≤ n) :
    thinRisk μ q (acceptProb (floorScale n) (thinRate μ n)) (thinWindow μ n) (1/2)
      (thinScale μ n) ≤ (modulus μ (floorScale n) / 2)^2 := by
  have ht := floorScale_pos hn
  set t := floorScale n with ht_def
  set A := upperInvMass μ t with hA_def
  set L := ∫ d, lowPart t d ∂μ with hL_def
  set J := ∫ d, upperSign q t d ∂μ with hJ_def
  set b := ∫ d, (if t ≤ (d : ℝ) then 0 else 1/2 - q.val d) ∂μ with hb_def
  have hmod : modulus μ t = t * A + L := modulus_split μ ht
  have hL0 : 0 ≤ L := lowPart_integral_nonneg μ t
  have hA0 : 0 ≤ A := upperInvMass_nonneg μ t
  unfold thinRisk
  rw [integral_accept_flip, integral_acceptProb, hmod]
  rcases hA0.eq_or_lt with h0 | hpos
  · -- A = 0: the window is empty
    have hw : thinWindow μ n = 0 := by
      unfold thinWindow
      rw [← ht_def, ← hA_def, ← h0]
      simp
    rw [hw]
    have hθ := signMean_bounds μ q
    have hlow := lowPart_ge μ ht
    rw [← hA_def, ← h0] at hlow
    simp only [Nat.cast_zero, zero_mul, mul_zero, add_zero]
    rw [← h0, mul_zero, zero_add]
    have : 1 ≤ L := by linarith
    nlinarith
  · -- A > 0
    obtain ⟨hm, hle⟩ := thin_window_pos μ hn hpos
    set m := (thinWindow μ n : ℝ) with hm_def
    set r := thinRate μ n with hr_def
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
    have hrm : r * m = n / A := by
      rw [hr_def]
      unfold thinRate
      rw [← ht_def, ← hA_def, ← hm_def]
      field_simp
    have hβ : thinScale μ n = A / (4 * n) := by
      unfold thinScale
      rw [← hr_def, ← hm_def, mul_assoc, hrm]
      field_simp
    rw [hβ]
    have hbias : 1/2 - signMean μ q.val + A / (4 * n) * (m * (2 * r * J)) = b := by
      rw [hb_def, ← bias_eq μ q t, ← hJ_def]
      have : A / (4 * n) * (m * (2 * r * J)) = (1/2) * J * (A / n * (r * m)) := by ring
      have h1 : A / n * (n / A) = 1 := by field_simp
      rw [this, hrm, h1, mul_one]
    rw [hbias]
    have hvar : (A / (4 * n))^2 * (m * (r * A - (2 * r * J)^2)) ≤ (t * A / 2)^2 := by
      have h1 : (A / (4 * n))^2 * (m * (r * A - (2 * r * J)^2)) ≤
          (A / (4 * n))^2 * (m * (r * A)) := by
        apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
        apply mul_le_mul_of_nonneg_left _ hm.le
        nlinarith [sq_nonneg (2 * r * J)]
      have h2 : (A / (4 * n))^2 * (m * (r * A)) = A^2 / (16 * n) := by
        rw [show m * (r * A) = (r * m) * A by ring, hrm]
        field_simp
        ring
      have h3 : (t * A / 2)^2 = A^2 / (16 * n) := by
        rw [show (t * A / 2)^2 = t^2 * A^2 / 4 by ring, ht_def, floorScale_sq hn]
        field_simp
        ring
      linarith
    have hbL := bias_abs_le μ q t
    rw [← hb_def, ← hL_def] at hbL
    have hb2 : b^2 ≤ ((1/2) * L)^2 := by
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) hbL 2
    have htA : 0 ≤ t * A := mul_nonneg ht.le hA0
    nlinarith

theorem thin_work_le (μ : Measure Gap) [IsProbabilityMeasure μ] {n : ℕ} (hn : 1 ≤ n) :
    (thinWindow μ n : ℝ) * ∫ d, acceptProb (floorScale n) (thinRate μ n) d ∂μ ≤ n := by
  rw [integral_acceptProb]
  rcases (upperInvMass_nonneg μ (floorScale n)).eq_or_lt with h0 | hpos
  · rw [← h0]
    simp
  · obtain ⟨hm, _⟩ := thin_window_pos μ hn hpos
    unfold thinRate
    rw [show (thinWindow μ n : ℝ) * ((n : ℝ) / (thinWindow μ n * upperInvMass μ (floorScale n)) *
      upperInvMass μ (floorScale n)) = n by field_simp]

/-- The floor-form bound for both oracles. -/
theorem oracle_floor_upper_bound (μ : Measure Gap) [IsProbabilityMeasure μ] (B : ℝ) (hB : 1 ≤ B) :
    revealedMinimaxRisk μ B ≤
      ENNReal.ofReal (modulus μ (1 / (2 * Real.sqrt (Nat.floor B : ℝ))) / 2) ∧
    selectedMinimaxRisk μ B ≤
      ENNReal.ofReal (modulus μ (1 / (2 * Real.sqrt (Nat.floor B : ℝ))) / 2) := by
  set n := Nat.floor B with hn_def
  have hn : 1 ≤ n := Nat.le_floor (by exact_mod_cast hB)
  have hnB : (n : ℝ) ≤ B := Nat.floor_le (by linarith)
  have hscale : 1 / (2 * Real.sqrt (n : ℝ)) = floorScale n := rfl
  rw [hscale]
  set p := acceptProb (floorScale n) (thinRate μ n) with hp_def
  have hp : Measurable p := measurable_acceptProb _ _
  have hp01 : ∀ d, 0 ≤ p d ∧ p d ≤ 1 := acceptProb_mem μ hn
  set m := thinWindow μ n
  set β := thinScale μ n
  have hwork : ENNReal.ofReal (m * ∫ d, p d ∂μ) ≤ ENNReal.ofReal B :=
    ENNReal.ofReal_le_ofReal ((thin_work_le μ hn).trans hnB)
  have hx : 0 ≤ modulus μ (floorScale n) / 2 :=
    div_nonneg (modulus_nonneg μ (floorScale_pos hn).le) (by norm_num)
  have hrisk (q : SignLaw) : ENNReal.ofReal (thinRisk μ q p m (1/2) β) ≤
      ENNReal.ofReal ((modulus μ (floorScale n) / 2)^2) :=
    ENNReal.ofReal_le_ofReal (thin_risk_le μ q hn)
  constructor
  · refine le_trans (sInf_le ⟨ℕ → unitInterval, inferInstance, thinRevealed p hp m (1/2) β,
      fun q => (revealed_work μ p hp hp01 m (1/2) β q).trans hwork, rfl⟩) ?_
    apply iSup_le
    intro q
    apply rms_le_of_sq _ _ _ _ hx
    rw [revealed_risk μ p hp hp01 m (1/2) β q]
    exact hrisk q
  · refine le_trans (sInf_le ⟨ThinSeed, inferInstance, thinSelected μ p hp m (1/2) β,
      fun q => (selected_work μ p hp hp01 m (1/2) β q).trans hwork, rfl⟩) ?_
    apply iSup_le
    intro q
    apply rms_le_of_sq _ _ _ _ hx
    rw [selected_risk μ p hp hp01 m (1/2) β q]
    exact hrisk q

theorem floorScale_le (B : ℝ) (hB : 1 ≤ B) : floorScale (Nat.floor B) ≤ 1 / Real.sqrt B := by
  have hn : 1 ≤ Nat.floor B := Nat.le_floor (by exact_mod_cast hB)
  have hn' : (1 : ℝ) ≤ Nat.floor B := by exact_mod_cast hn
  have hlt := Nat.lt_floor_add_one B
  have h4 : B ≤ 4 * (Nat.floor B : ℝ) := by linarith
  have hs : Real.sqrt B ≤ 2 * Real.sqrt (Nat.floor B : ℝ) := by
    calc
      Real.sqrt B ≤ Real.sqrt (4 * (Nat.floor B : ℝ)) := Real.sqrt_le_sqrt h4
      _ = 2 * Real.sqrt (Nat.floor B : ℝ) := by
        rw [Real.sqrt_mul (by norm_num), show (4 : ℝ) = 2^2 by norm_num,
          Real.sqrt_sq (by norm_num)]
  unfold floorScale
  exact one_div_le_one_div_of_le (Real.sqrt_pos.mpr (by linarith)) hs

theorem oracle_modulus_upper_bound (μ : Measure Gap) [IsProbabilityMeasure μ] (B : ℝ)
    (hB : 1 ≤ B) :
    revealedMinimaxRisk μ B ≤ ENNReal.ofReal (modulus μ (1 / Real.sqrt B) / 2) ∧
    selectedMinimaxRisk μ B ≤ ENNReal.ofReal (modulus μ (1 / Real.sqrt B) / 2) := by
  have h := oracle_floor_upper_bound μ B hB
  have hmono : modulus μ (1 / (2 * Real.sqrt (Nat.floor B : ℝ))) / 2 ≤
      modulus μ (1 / Real.sqrt B) / 2 := by
    apply div_le_div_of_nonneg_right _ (by norm_num)
    exact modulus_le_of_le μ (floorScale_pos (Nat.le_floor (by exact_mod_cast hB))).le
      (floorScale_le B hB)
  exact ⟨h.1.trans (ENNReal.ofReal_le_ofReal hmono), h.2.trans (ENNReal.ofReal_le_ofReal hmono)⟩

end ThresholdHC.OracleUpper
