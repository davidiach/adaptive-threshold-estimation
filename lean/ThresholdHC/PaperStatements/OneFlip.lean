import ThresholdHC.PaperStatements.Specification
import ThresholdHC.LargeBudgetRMS.LargeBudgetBinomial
import ThresholdHC.UnbiasedConverse.Full
import ThresholdHC.RareAboveTwo.Nonvacuity

/-! Fresh-flip estimators at a single gap.

`N+1` fresh flips with an affine output of the number of heads have the binomial
mean and variance. At a fixed gap `d` the output `(X - 1/2 + d)/(2d)` of one
flip is unbiased, has unit work and largest variance `1/(16 d^2)`, which attains
the unbiased converse. With `⌊B⌋` flips the unbiased average has squared risk at
most `1/(16 d^2 ⌊B⌋)`, and when `d √B < 1` the constant `1/2` has risk at most
`1/2`; both are at most half the modulus. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace ThresholdHC.PaperStatements
open Tier3 Tier5 Tier6 SharpRMS.LargeBudget UnbiasedConverse

/-- `N+1` fresh flips, then an output that depends on the number of heads. -/
def freshFlips (N : ℕ) (out : ℕ → ℝ) : AdaptiveEstimator Unit where
  randomLaw := Measure.dirac ()
  probability := inferInstance
  policy := fun _ => freshPolicy N
  policy_measurable := fun _ _ => measurableSet_eq_fun measurable_const measurable_const
  output := fun z => out (headsNat (processPrefix (N+1) z.2))
  output_measurable := (measurable_of_countable (fun w : Prefix (N+1) => out (headsNat w))).comp
    (Measurable.of_eval fun i => (measurable_pi_apply i.val).comp measurable_snd)

theorem fresh_budget (μ : Measure Gap) [IsProbabilityMeasure μ] (N : ℕ) (out : ℕ → ℝ)
    (q : SignLaw) : expectedWork μ (freshFlips N out) q ≤ ENNReal.ofReal (N+1) := by
  apply HardBudget.pathwise_expected μ (freshFlips N out) q (by positivity)
  rw [show ⌊((N : ℝ) + 1)⌋₊ = N+1 by exact_mod_cast Nat.floor_natCast (N+1)]
  exact HardBudget.stopAt_pathwise_cap (freshFlips N out) (N+1) (fun _ xs => xs.length)
    (fun _ => rfl)

theorem binomial_linear (b a c : ℝ) (n k : ℕ) :
    binomialAverage b (fun j => a * j + c) n k = a * (k + n * b) + c := by
  induction n generalizing k with
  | zero => simp [binomialAverage]
  | succ n ih =>
    rw [binomialAverage, ih k, ih (k+1)]
    push_cast; ring

theorem binomial_square (b a c : ℝ) (n k : ℕ) :
    binomialAverage b (fun j => (a * j + c)^2) n k =
      (a * (k + n * b) + c)^2 + a^2 * n * b * (1 - b) := by
  induction n generalizing k with
  | zero => simp [binomialAverage]
  | succ n ih =>
    rw [binomialAverage, ih k, ih (k+1)]
    push_cast; ring

theorem fresh_integral (N : ℕ) (out : ℕ → ℝ) (g : Gap) (q : SignLaw) (f : ℕ → ℝ) :
    (∫ z, f (headsNat (processPrefix (N+1) z.2))
        ∂experimentLaw (Measure.dirac g) (freshFlips N out) q) =
      binomialAverage (1/2 + (2 * q.val g - 1) * g) f (N+1) 0 := by
  classical
  let p := q.val g
  let F := fun w : Prefix (N+1) => f (headsNat w)
  obtain ⟨C,hC⟩ := (Set.finite_range fun w => |F w|).bddAbove
  have hbound (w) : |F w| ≤ C := hC ⟨w,rfl⟩
  have hr := (population_realization Unit (Measure.dirac g) (freshFlips N out) q).2
    (N+1) (fun _ => F) (fun _ => measurable_const) ⟨C, fun _ w => hbound w⟩
  have hseed : populationSeedLaw (Measure.dirac g) (freshFlips N out) =
      Measure.dirac ((), fun _ => g) := by
    simp [populationSeedLaw, freshFlips, Measure.infinitePi_dirac, Measure.dirac_prod_dirac]
  rw [hseed, integral_dirac] at hr
  change (∫ z, F (processPrefix (N+1) z.2) ∂experimentLaw (Measure.dirac g) (freshFlips N out) q) =
      ∑ w, creationLaw (freshPolicy N) (fun _ => (g:ℝ)) (fun _ => p) w * F w at hr
  have av := fresh_average N (N+1) le_rfl (g:ℝ) p ⟨g.property.1.le, g.property.2⟩
    (q.property.2 g) f 0
  simp only [zero_add] at av
  exact hr.trans av

theorem heads_le {N : ℕ} (w : Prefix (N+1)) : headsNat w ≤ N+1 := by
  unfold headsNat
  calc (∑ i, if w i = some true then 1 else 0) ≤ ∑ _i : Fin (N+1), 1 :=
        Finset.sum_le_sum (fun i _ => by split_ifs <;> norm_num)
    _ = N+1 := by simp

/-- Mean and squared error of an affine output of the number of heads. -/
theorem fresh_moments (N : ℕ) (a c : ℝ) (g : Gap) (q : SignLaw) (t : ℝ) :
    Integrable (populationOutput (freshFlips N (fun j => a * j + c)))
        (experimentLaw (Measure.dirac g) (freshFlips N (fun j => a * j + c)) q) ∧
    (∫ z, populationOutput (freshFlips N (fun j => a * j + c)) z
        ∂experimentLaw (Measure.dirac g) (freshFlips N (fun j => a * j + c)) q) =
      a * ((N+1) * (1/2 + (2 * q.val g - 1) * g)) + c ∧
    squaredRisk (experimentLaw (Measure.dirac g) (freshFlips N (fun j => a * j + c)) q)
        (populationOutput (freshFlips N (fun j => a * j + c))) t =
      ENNReal.ofReal ((a * ((N+1) * (1/2 + (2 * q.val g - 1) * g)) + c - t)^2 +
        a^2 * (N+1) * (1/2 + (2 * q.val g - 1) * g) * (1 - (1/2 + (2 * q.val g - 1) * g))) := by
  set A := freshFlips N (fun j => a * j + c)
  set P := experimentLaw (Measure.dirac g) A q
  set b := 1/2 + (2 * q.val g - 1) * g
  have hY : ∀ z, populationOutput A z = a * (headsNat (processPrefix (N+1) z.2) : ℕ) + c :=
    fun _ => rfl
  have hbd (z : PopulationSeed Unit × ProcessTape) (s : ℝ) : |(a * (headsNat (processPrefix (N+1) z.2) : ℕ) + c - s)| ≤
      |a| * (N+1) + |c| + |s| := by
    have h0 : ((headsNat (processPrefix (N+1) z.2) : ℕ) : ℝ) ≤ N+1 := by
      exact_mod_cast heads_le _
    have h1 : 0 ≤ ((headsNat (processPrefix (N+1) z.2) : ℕ) : ℝ) := Nat.cast_nonneg _
    calc _ ≤ |a * (headsNat (processPrefix (N+1) z.2) : ℕ)| + |c| + |s| := by
          have := abs_sub (a * (headsNat (processPrefix (N+1) z.2) : ℕ) + c) s
          have := abs_add_le (a * (headsNat (processPrefix (N+1) z.2) : ℕ)) c
          linarith
      _ ≤ |a| * (N+1) + |c| + |s| := by
          rw [abs_mul, abs_of_nonneg h1]
          gcongr
  have hmeas : Measurable (populationOutput A) := measurable_populationOutput A
  have hint : Integrable (populationOutput A) P := by
    refine (integrable_const (|a| * (N+1) + |c| + |0|)).mono' hmeas.aestronglyMeasurable
      (ae_of_all _ fun z => ?_)
    rw [Real.norm_eq_abs, hY z]
    simpa using hbd z 0
  have hmean : (∫ z, populationOutput A z ∂P) = a * ((N+1) * b) + c := by
    have := fresh_integral N (fun j => a * j + c) g q (fun j => a * j + c)
    rw [binomial_linear] at this
    simp only [Nat.cast_zero, zero_add] at this
    push_cast at this
    exact this
  refine ⟨hint, hmean, ?_⟩
  have hsq : Integrable (fun z => (populationOutput A z - t)^2) P := by
    refine (integrable_const ((|a| * (N+1) + |c| + |t|)^2)).mono'
      ((hmeas.sub_const t).pow_const 2).aestronglyMeasurable (ae_of_all _ fun z => ?_)
    rw [Real.norm_eq_abs, abs_pow, hY z]
    exact pow_le_pow_left₀ (abs_nonneg _) (hbd z t) 2
  have hval : (∫ z, (populationOutput A z - t)^2 ∂P) =
      (a * ((N+1) * b) + c - t)^2 + a^2 * (N+1) * b * (1 - b) := by
    have := fresh_integral N (fun j => a * j + c) g q (fun j => (a * j + (c - t))^2)
    rw [binomial_square] at this
    simp only [Nat.cast_zero, zero_add] at this
    push_cast at this
    rw [show (fun z => (populationOutput A z - t)^2) =
        fun z => (a * (headsNat (processPrefix (N+1) z.2) : ℕ) + (c - t))^2 from
        funext fun z => by rw [hY z]; ring]
    rw [this]; ring
  unfold squaredRisk
  rw [← ofReal_integral_eq_lintegral_ofReal hsq (ae_of_all _ fun _ => sq_nonneg _), hval]

/-- The one-flip estimator `(X - 1/2 + d)/(2d)` of the paper. -/
def oneFlip (d : ℝ) : AdaptiveEstimator Unit :=
  freshFlips 0 (fun j => 1/(2*d) * j + (d - 1/2)/(2*d))

def halfLaw : SignLaw := ⟨fun _ => 1/2, measurable_const, fun _ => ⟨by norm_num, by norm_num⟩⟩

theorem one_flip_bounds (d : Gap) :
    UniformlyUnbiased (Measure.dirac d) (oneFlip d) ∧
    UniformVarianceBound (Measure.dirac d) (oneFlip d) (1 / (16 * (d:ℝ)^2)) ∧
    UniformBudget (Measure.dirac d) (oneFlip d) 1 ∧
    evariance (populationOutput (oneFlip d)) (experimentLaw (Measure.dirac d) (oneFlip d) halfLaw) =
      ENNReal.ofReal (1 / (16 * (d:ℝ)^2)) := by
  have hd : 0 < (d:ℝ) := d.property.1
  have hmean (q : SignLaw) := (fresh_moments 0 (1/(2*d)) ((d - 1/2)/(2*d)) d q 0).2.1
  have hint (q : SignLaw) := (fresh_moments 0 (1/(2*d)) ((d - 1/2)/(2*d)) d q 0).1
  have hθ (q : SignLaw) : signMean (Measure.dirac d) q.val = q.val d := by simp [signMean]
  have hm (q : SignLaw) : (∫ z, populationOutput (oneFlip d) z
      ∂experimentLaw (Measure.dirac d) (oneFlip d) q) = q.val d := by
    rw [oneFlip, hmean q]; field_simp; push_cast; ring
  have hvar (q : SignLaw) : evariance (populationOutput (oneFlip d))
      (experimentLaw (Measure.dirac d) (oneFlip d) q) =
      ENNReal.ofReal ((1/2 + (2 * q.val d - 1) * d) * (1 - (1/2 + (2 * q.val d - 1) * d)) /
        (4 * (d:ℝ)^2)) := by
    rw [evariance_eq_lintegral_ofReal, hm q]
    have h := (fresh_moments 0 (1/(2*d)) ((d - 1/2)/(2*d)) d q (q.val d)).2.2
    unfold squaredRisk at h
    rw [oneFlip, h]
    congr 1
    field_simp; push_cast; ring
  refine ⟨fun q => ⟨hint q, (hm q).trans (hθ q).symm⟩, fun q => ?_, fun q => ?_, ?_⟩
  · rw [hvar q]
    apply ENNReal.ofReal_le_ofReal
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [sq_nonneg ((2 * q.val d - 1) * d)]
  · have := fresh_budget (Measure.dirac d) 0 (fun j => 1/(2*(d:ℝ)) * j + ((d:ℝ) - 1/2)/(2*d)) q
    simpa [oneFlip] using this
  · rw [hvar halfLaw]
    congr 1
    simp only [halfLaw]
    field_simp; ring

/-- At the endpoint gap the one-flip output is the observation itself. -/
theorem one_flip_half_range (z : PopulationSeed Unit × ProcessTape) :
    0 ≤ populationOutput (oneFlip (1/2)) z ∧ populationOutput (oneFlip (1/2)) z ≤ 1 := by
  have h0 : ((headsNat (processPrefix (0+1) z.2) : ℕ) : ℝ) ≤ 1 := by
    exact_mod_cast heads_le (N := 0) _
  have h1 : 0 ≤ ((headsNat (processPrefix (0+1) z.2) : ℕ) : ℝ) := Nat.cast_nonneg _
  have hval : populationOutput (oneFlip (1/2)) z = ((headsNat (processPrefix (0+1) z.2) : ℕ) : ℝ) := by
    change 1/(2*(1/2:ℝ)) * ((headsNat (processPrefix (0+1) z.2) : ℕ) : ℝ) + ((1/2:ℝ) - 1/2)/(2*(1/2)) = _
    norm_num
  rw [hval]
  exact ⟨h1, h0⟩

theorem variance_work_lower (μ : Measure Gap) [IsProbabilityMeasure μ] :
    ENNReal.ofReal ((∫ d : Gap, (d:ℝ)⁻¹ ∂μ)^2 / 16) ≤ unbiasedVarianceWork μ := by
  apply le_sInf
  rintro t ⟨R, _, A, V, W, hV, hW, hu, hv, hw, rfl⟩
  exact ENNReal.ofReal_le_ofReal (unbiased_converse R μ A V W hV hW hu hv hw).2

theorem fixed_gap_equality (d : Gap) :
    unbiasedVarianceWork (Measure.dirac d) =
      ENNReal.ofReal ((∫ x : Gap, (x:ℝ)⁻¹ ∂Measure.dirac d)^2 / 16) := by
  apply le_antisymm _ (variance_work_lower _)
  obtain ⟨hu, hv, hw, -⟩ := one_flip_bounds d
  have hd : 0 < (d:ℝ) := d.property.1
  have hmem : unbiasedVarianceWork (Measure.dirac d) ≤
      ENNReal.ofReal (1/(16*(d:ℝ)^2) * 1) :=
    sInf_le ⟨Unit, inferInstance, oneFlip d, 1/(16*(d:ℝ)^2), 1, by positivity, by norm_num,
      hu, hv, hw, rfl⟩
  refine hmem.trans (le_of_eq ?_)
  congr 1
  rw [integral_dirac]
  field_simp

theorem sharp_coefficient (c : ℝ) :
    (∀ (μ : Measure Gap) [IsProbabilityMeasure μ], Integrable (fun d : Gap => (d:ℝ)⁻¹) μ →
      ENNReal.ofReal (c * (∫ d : Gap, (d:ℝ)⁻¹ ∂μ)^2) ≤ unbiasedVarianceWork μ) ↔
    c ≤ 1/16 := by
  constructor
  · intro h
    obtain ⟨hu, hv, hw, -⟩ := one_flip_bounds SharpRMS.endpointGap
    have hI := (unbiased_converse Unit _ _ _ _ (by positivity) (by norm_num) hu hv hw).1
    have h1 := h (Measure.dirac SharpRMS.endpointGap) hI
    rw [fixed_gap_equality, integral_dirac] at h1
    have he : ((SharpRMS.endpointGap : ℝ))⁻¹ = 2 := by
      rw [show ((SharpRMS.endpointGap : ℝ)) = 1/2 from rfl]; norm_num
    rw [he, ENNReal.ofReal_le_ofReal_iff (by norm_num)] at h1
    linarith
  · intro hc μ _ hI
    refine le_trans (ENNReal.ofReal_le_ofReal ?_) (variance_work_lower μ)
    nlinarith [sq_nonneg (∫ d : Gap, (d:ℝ)⁻¹ ∂μ)]

theorem half_gap_unbiased : ∃ A : AdaptiveEstimator Unit,
    (∀ z, 0 ≤ populationOutput A z ∧ populationOutput A z ≤ 1) ∧
    UniformlyUnbiased (Measure.dirac SharpRMS.endpointGap) A ∧
    UniformBudget (Measure.dirac SharpRMS.endpointGap) A 1 :=
  ⟨oneFlip (1/2), one_flip_half_range, (one_flip_bounds SharpRMS.endpointGap).1,
    (one_flip_bounds SharpRMS.endpointGap).2.2.1⟩

/-- `⌊B⌋` fresh flips and the unbiased average output. -/
def pointMassFlips (g : ℝ) (N : ℕ) : AdaptiveEstimator Unit :=
  freshFlips N (fun j => 1/(2*g*(N+1)) * j + (g - 1/2)/(2*g))

theorem point_mass_upper (g : Gap) (B : ℝ) (hB : 1 ≤ B) :
    minimaxRisk (Measure.dirac g) B ≤
      ENNReal.ofReal (modulus (Measure.dirac g) (1 / Real.sqrt B) / 2) := by
  have hg : 0 < (g:ℝ) := g.property.1
  have hsB : 0 < Real.sqrt B := Real.sqrt_pos.2 (by linarith)
  have hθ (q : SignLaw) : signMean (Measure.dirac g) q.val = q.val g := by simp [signMean]
  have hmod : modulus (Measure.dirac g) (1 / Real.sqrt B) = min 1 ((1 / Real.sqrt B) / g) := by
    simp [modulus, clippedGap]
  by_cases hsmall : (g:ℝ) * Real.sqrt B < 1
  · have hm1 : modulus (Measure.dirac g) (1 / Real.sqrt B) = 1 := by
      rw [hmod]; apply min_eq_left
      rw [div_div, one_le_div (by positivity)]; linarith
    rw [hm1]
    have hmem : minimaxRisk (Measure.dirac g) B ≤
        maximalRMSRisk (Measure.dirac g) (RareAboveTwo.constantEstimator (1/2)) :=
      sInf_le ⟨Unit, inferInstance, RareAboveTwo.constantEstimator (1/2), fun q => by
        rw [RareAboveTwo.constant_work]; exact bot_le, rfl⟩
    refine hmem.trans (iSup_le fun q => ?_)
    rw [RareAboveTwo.constant_risk, hθ]
    apply ENNReal.ofReal_le_ofReal
    have := q.property.2 g
    rw [abs_le]; constructor <;> linarith
  · push Not at hsmall
    have hmod' : modulus (Measure.dirac g) (1 / Real.sqrt B) = 1 / ((g:ℝ) * Real.sqrt B) := by
      rw [hmod, min_eq_right]
      · field_simp
      · rw [div_div, div_le_one (by positivity)]; linarith
    obtain ⟨N, hN⟩ : ∃ N : ℕ, ⌊B⌋₊ = N + 1 := ⟨⌊B⌋₊ - 1, by
      have : 1 ≤ ⌊B⌋₊ := Nat.le_floor (by exact_mod_cast hB); omega⟩
    have hNB : (N:ℝ) + 1 ≤ B := by
      have := Nat.floor_le (show 0 ≤ B by linarith); rw [hN] at this; exact_mod_cast this
    have hBN : B < (N:ℝ) + 2 := by
      have := Nat.lt_floor_add_one B; rw [hN] at this; push_cast at this; linarith
    have hmem : minimaxRisk (Measure.dirac g) B ≤
        maximalRMSRisk (Measure.dirac g) (pointMassFlips g N) :=
      sInf_le ⟨Unit, inferInstance, pointMassFlips g N, fun q =>
        (fresh_budget _ N _ q).trans (ENNReal.ofReal_le_ofReal hNB), rfl⟩
    refine hmem.trans (iSup_le fun q => ?_)
    apply HardBudget.rms_from_square _ _ _ _ (by rw [hmod']; positivity)
    have h := (fresh_moments N (1/(2*g*(N+1))) ((g - 1/2)/(2*g)) g q (signMean (Measure.dirac g) q.val)).2.2
    rw [pointMassFlips, h, hθ]
    apply ENNReal.ofReal_le_ofReal
    rw [hmod']
    have hp := q.property.2 g
    set p := q.val g
    set b := 1/2 + (2 * p - 1) * g
    have hmean : 1 / (2 * (g:ℝ) * (N + 1)) * ((N + 1) * b) + ((g:ℝ) - 1/2) / (2 * (g:ℝ)) - p = 0 := by
      simp only [b]; field_simp; ring
    rw [hmean]
    have hb : b * (1 - b) ≤ 1/4 := by nlinarith [sq_nonneg (b - 1/2)]
    have hb0 : 0 ≤ b * (1 - b) := by
      have h1 : 0 ≤ b := by
        simp only [b]; nlinarith [g.property.2]
      have h2 : b ≤ 1 := by
        simp only [b]; nlinarith [g.property.2]
      nlinarith
    have hsq : Real.sqrt B ^ 2 = B := Real.sq_sqrt (by linarith)
    have hN0 : (0:ℝ) < N + 1 := by positivity
    calc (0:ℝ) ^ 2 + (1 / (2 * (g:ℝ) * (N + 1)))^2 * (N + 1) * b * (1 - b)
        = b * (1 - b) / (4 * (g:ℝ)^2 * (N + 1)) := by field_simp; ring
      _ ≤ (1/4) / (4 * (g:ℝ)^2 * (N + 1)) := by gcongr
      _ ≤ (1 / ((g:ℝ) * Real.sqrt B) / 2)^2 := by
          have he : (1 / ((g:ℝ) * Real.sqrt B) / 2)^2 = 1 / (4 * (g:ℝ)^2 * B) := by
            rw [div_pow, div_pow, mul_pow, hsq]; ring
          rw [he, div_le_div_iff₀ (by positivity) (by positivity)]
          have h4 : B ≤ 4 * ((N:ℝ) + 1) := by linarith
          nlinarith [mul_le_mul_of_nonneg_left h4 (sq_nonneg (g:ℝ))]

end ThresholdHC.PaperStatements
