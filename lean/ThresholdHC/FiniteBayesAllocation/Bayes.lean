import ThresholdHC.FiniteBayesAllocation.Atoms
import ThresholdHC.FiniteBayesAllocation.Posterior

/-! The Bayes bounds for a deterministic eight-flip design at a valid atomic
case, from a kernel certificate `certify (scaleOf C) (run C p) = (lo, hi, true)`.

* Upper: the posterior-mean estimator of the design has uniform-prior Bayes
  squared error at most `hi / (10^20 K)`.
* Lower: every estimator whose policy is `stopAt 8 p` on every private seed,
  with any measurable output, has Bayes squared error at least `lo / (10^20 K)`.
  The output is clipped to `[0, 1/8]` (all targets lie there), read from the
  padded eight-prefix, and the posterior-variance bound is applied seed by seed. -/

noncomputable section
namespace ThresholdHC.FiniteBayesAllocation
open MeasureTheory
open scoped ENNReal
open ThresholdHC ThresholdHC.Tier3 ThresholdHC.Tier6 ThresholdHC.FiniteLawCertificates
open ThresholdHC.CriticalEntropy ThresholdHC.HardBudget

theorem mem_allWords {n : ℕ} (u : Fin n → Bool) : List.ofFn u ∈ allWords n := by
  induction n with
  | zero => simp [allWords]
  | succ n ih =>
    rw [List.ofFn_succ]
    simp only [allWords, List.mem_append, List.mem_map]
    cases h : u 0
    · exact Or.inl ⟨_, ih _, rfl⟩
    · exact Or.inr ⟨_, ih _, rfl⟩

theorem list_sum_cast_div {α : Type*} (L : List α) (f : α → ℕ) (P : ℝ) :
    (L.map fun a => (f a : ℝ) / P).sum = ((L.map f).sum : ℝ) / P := by
  induction L with
  | nil => simp
  | cons a L ih => simp [ih, add_div]

theorem sq_sub_le_one (x θ : ℝ) (hx : 0 ≤ x ∧ x ≤ 1/8) (hθ : 0 ≤ θ ∧ θ ≤ 1/8) :
    (x - θ)^2 ≤ 1 := by
  nlinarith [hx.1, hx.2, hθ.1, hθ.2]

/-- Scaled weight of an ordered word as a real number. -/
def wordReal {J K : ℕ} (C : Code J K) (p : List Bool → ℕ) (k : Fin K) (u : List Bool) : ℝ :=
  (wordNat C k (countsOf p u) : ℝ) / ((C.den : ℝ) * 32 ^ 8) ^ 8

theorem wordReal_nonneg {J K : ℕ} (C : Code J K) (p : List Bool → ℕ) (k : Fin K) (u : List Bool) :
    0 ≤ wordReal C p k u := by
  unfold wordReal
  positivity

/-- Under a design `stopAt 8 p` the observable word sum is a sum over the ordered words. -/
theorem design_word_sum {J K : ℕ} {d : Fin J → Gap} {m : Fin J → ℚ} {v : Fin K → Fin J → ℚ}
    {C : Code J K} (hc : CaseValid d m v C) [IsProbabilityMeasure (atomicMeasure d m)]
    (p : List Bool → ℕ) (hp : ∀ (u : Fin 8 → Bool) (t : Fin 8), flipLabel p u t < 8) {R : Type} [MeasurableSpace R]
    (A : AdaptiveEstimator R) (hpol : ∀ r, A.policy r = stopAt 8 p) (k : Fin K) (r : R)
    (g : Prefix 8 → ℝ) :
    ∑ w, seedWeight (atomicMeasure d m) A (atomSign d (v k)) r w * g w =
      ∑ u : Fin 8 → Bool, wordReal C p k (List.ofFn u) * g (fun t => some (u t)) := by
  simp only [seedWeight, hpol r]
  rw [sum_prefix_full]
  apply Finset.sum_congr rfl
  intro u _
  rw [word_weight hc p k u (hp u)]
  rfl

/-- Posterior-mean output read from the observed eight-prefix. -/
def postOut {J K : ℕ} (C : Code J K) (p : List Bool → ℕ) (w : Prefix 8) : ℝ :=
  postMean C (countsOf p (List.ofFn fun t => (w t).getD false))

/-- The design `stopAt 8 p` with its posterior-mean output. -/
def postEstimator {J K : ℕ} (C : Code J K) (p : List Bool → ℕ) : AdaptiveEstimator Unit where
  randomLaw := Measure.dirac ()
  probability := inferInstance
  policy := fun _ => stopAt 8 p
  policy_measurable := fun _ _ => measurableSet_eq_fun measurable_const measurable_const
  output := fun z => postOut C p (processPrefix 8 z.2)
  output_measurable := (measurable_of_countable (postOut C p)).comp
    (Measurable.of_eval fun i => (measurable_pi_apply i.val).comp measurable_snd)

theorem postEstimator_policy {J K : ℕ} (C : Code J K) (p : List Bool → ℕ) (r : Unit) :
    (postEstimator C p).policy r = stopAt 8 p := rfl

theorem postEstimator_cap {J K : ℕ} (C : Code J K) (p : List Bool → ℕ) :
    PathwiseCap (postEstimator C p) 8 :=
  stopAt_pathwise_cap (postEstimator C p) 8 (fun _ => p) (fun _ => rfl)

theorem bayesRisk_eq {R : Type} [MeasurableSpace R] {K : ℕ} (μ : Measure Gap) [IsProbabilityMeasure μ]
    (q : Fin K → SignLaw) (A : AdaptiveEstimator R) :
    bayesRisk μ q A =
      (∑ k, squaredRisk (experimentLaw μ A (q k)) (populationOutput A) (signMean μ (q k).val)) / K :=
  rfl

private theorem div_natCast_ofReal (x : ℝ) (K : ℕ) (hK : 0 < K) :
    ENNReal.ofReal x / (K : ℝ≥0∞) = ENNReal.ofReal (x / K) := by
  rw [ENNReal.ofReal_div_of_pos (by exact_mod_cast hK), ENNReal.ofReal_natCast]

/-- The posterior-mean estimator of a certified design. -/
theorem design_upper {J K : ℕ} {d : Fin J → Gap} {m : Fin J → ℚ} {v : Fin K → Fin J → ℚ}
    {C : Code J K} (hc : CaseValid d m v C) [IsProbabilityMeasure (atomicMeasure d m)]
    (hK : 0 < K) (p : List Bool → ℕ) (hp : ∀ (u : Fin 8 → Bool) (t : Fin 8), flipLabel p u t < 8) {lo hi : ℕ}
    (hcert : certify (scaleOf C) (run C p) = (lo, hi, true)) :
    bayesRisk (atomicMeasure d m) (fun k => atomSign d (v k)) (postEstimator C p) ≤
      ENNReal.ofReal (hi / (prec * K)) := by
  obtain ⟨-, hhi, hall⟩ := certify_spec hcert
  have hok (u : Fin 8 → Bool) : wordOK (scaleOf C) (statsOf C (countsOf p (List.ofFn u))) = true :=
    hall _ (List.mem_map_of_mem (mem_allWords u))
  let X (k : Fin K) (u : Fin 8 → Bool) : ℝ :=
    wordReal C p k (List.ofFn u) * (postMean C (countsOf p (List.ofFn u)) - (C.tt k : ℝ) / 16)^2
  have hrisk (k : Fin K) :
      squaredRisk (experimentLaw (atomicMeasure d m) (postEstimator C p) (atomSign d (v k)))
        (populationOutput (postEstimator C p)) (signMean (atomicMeasure d m) (atomSign d (v k)).val) =
        ENNReal.ofReal (∑ u, X k u) := by
    rw [prefix_output_risk _ _ _ _ 8 (postOut C p) (fun _ => rfl)]
    rw [show (postEstimator C p).randomLaw = Measure.dirac () from rfl, integral_dirac]
    rw [design_word_sum hc p hp (postEstimator C p) (fun _ => rfl) k (), atom_mean hc k]
    congr 1
  rw [bayesRisk_eq]
  simp_rw [hrisk]
  have hX (k : Fin K) : 0 ≤ ∑ u, X k u :=
    Finset.sum_nonneg fun u _ => mul_nonneg (wordReal_nonneg C p k _) (sq_nonneg _)
  rw [← ENNReal.ofReal_sum_of_nonneg (fun k _ => hX k), div_natCast_ofReal _ K hK]
  apply ENNReal.ofReal_le_ofReal
  have hsum : ∑ k, ∑ u, X k u ≤ (hi : ℝ) / prec := by
    rw [Finset.sum_comm]
    calc
      _ ≤ ∑ u : Fin 8 → Bool,
          ((upperTerm (scaleOf C) (statsOf C (countsOf p (List.ofFn u))) : ℕ) : ℝ) / prec := by
        apply Finset.sum_le_sum
        intro u _
        exact word_upper C _ (hok u) hc.den
      _ = (hi : ℝ) / prec := by
        rw [sum_allWords 8 (fun u => ((upperTerm (scaleOf C) (statsOf C (countsOf p u)) : ℕ) : ℝ) /
          (prec : ℝ)), list_sum_cast_div, ← hhi, run, List.map_map]
        rfl
  have hK' : (0 : ℝ) < K := by exact_mod_cast hK
  rw [← div_div]
  exact div_le_div_of_nonneg_right hsum hK'.le

/-- Every estimator with the certified design on every seed. -/
theorem design_lower {J K : ℕ} {d : Fin J → Gap} {m : Fin J → ℚ} {v : Fin K → Fin J → ℚ}
    {C : Code J K} (hc : CaseValid d m v C) [IsProbabilityMeasure (atomicMeasure d m)]
    (hK : 0 < K) (htt : ∀ k, C.tt k ≤ 2) (p : List Bool → ℕ) (hp : ∀ (u : Fin 8 → Bool) (t : Fin 8), flipLabel p u t < 8)
    {lo hi : ℕ} (hcert : certify (scaleOf C) (run C p) = (lo, hi, true))
    {R : Type} [MeasurableSpace R] (A : AdaptiveEstimator R) (hpol : ∀ r, A.policy r = stopAt 8 p) :
    ENNReal.ofReal (lo / (prec * K)) ≤
      bayesRisk (atomicMeasure d m) (fun k => atomSign d (v k)) A := by
  obtain ⟨hlo, -, hall⟩ := certify_spec hcert
  have hok (u : Fin 8 → Bool) : wordOK (scaleOf C) (statsOf C (countsOf p (List.ofFn u))) = true :=
    hall _ (List.mem_map_of_mem (mem_allWords u))
  have hcap : PathwiseCap A 8 := stopAt_pathwise_cap A 8 (fun _ => p) hpol
  let μ := atomicMeasure d m
  let θ (k : Fin K) : ℝ := (C.tt k : ℝ) / 16
  have hθ (k : Fin K) : 0 ≤ θ k ∧ θ k ≤ 1/8 := by
    have h2 : (C.tt k : ℝ) ≤ 2 := by exact_mod_cast htt k
    constructor
    · positivity
    · simp only [θ]; linarith
  let g (k : Fin K) (r : R) : ℝ := ∑ w : Prefix 8,
    seedWeight μ A (atomSign d (v k)) r w * (clippedOutput A (1/8) r w - θ k)^2
  have hg_nonneg (k : Fin K) (r : R) : 0 ≤ g k r :=
    Finset.sum_nonneg fun w _ =>
      mul_nonneg ((seedWeight_total μ A _ 8 r).1 w) (sq_nonneg _)
  have hg_le (k : Fin K) (r : R) : g k r ≤ 1 := by
    have htot := (seedWeight_total μ A (atomSign d (v k)) 8 r)
    calc
      g k r ≤ ∑ w : Prefix 8, seedWeight μ A (atomSign d (v k)) r w * 1 := by
        apply Finset.sum_le_sum
        intro w _
        apply mul_le_mul_of_nonneg_left _ (htot.1 w)
        exact sq_sub_le_one _ _ (clippedOutput_mem A (1/8) (by norm_num) r w) (hθ k)
      _ = 1 := by simp only [mul_one]; exact htot.2
  have hg_meas (k : Fin K) : Measurable (g k) :=
    Finset.measurable_sum _ fun w _ => (measurable_seedWeight μ A _ w).mul
      (((measurable_clippedOutput A (1/8) w).sub measurable_const).pow_const 2)
  have hg_int (k : Fin K) : Integrable (g k) A.randomLaw :=
    (integrable_const (1 : ℝ)).mono' (hg_meas k).aestronglyMeasurable
      (ae_of_all _ fun r => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hg_nonneg k r)]
        exact hg_le k r)
  have hrisk (k : Fin K) : ENNReal.ofReal (∫ r, g k r ∂A.randomLaw) ≤
      squaredRisk (experimentLaw μ A (atomSign d (v k))) (populationOutput A)
        (signMean μ (atomSign d (v k)).val) := by
    rw [atom_mean hc k]
    exact capped_risk_lower μ A 8 hcap (atomSign d (v k)) (1/8) (θ k) (hθ k)
  have hseed (r : R) : (lo : ℝ) / prec ≤ ∑ k, g k r := by
    have hw (k : Fin K) : g k r = ∑ u : Fin 8 → Bool, wordReal C p k (List.ofFn u) *
        (clippedOutput A (1/8) r (fun t => some (u t)) - θ k)^2 :=
      design_word_sum hc p hp A hpol k r (fun w => (clippedOutput A (1/8) r w - θ k)^2)
    simp_rw [hw]
    rw [Finset.sum_comm]
    calc
      (lo : ℝ) / prec = ∑ u : Fin 8 → Bool,
          ((lowerTerm (scaleOf C) (statsOf C (countsOf p (List.ofFn u))) : ℕ) : ℝ) / prec := by
        rw [sum_allWords 8 (fun u => ((lowerTerm (scaleOf C) (statsOf C (countsOf p u)) : ℕ) : ℝ) /
          (prec : ℝ)), list_sum_cast_div, ← hlo, run, List.map_map]
        rfl
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro u _
        exact word_lower C _ (hok u) hc.den _
  have hint : (lo : ℝ) / prec ≤ ∑ k, ∫ r, g k r ∂A.randomLaw := by
    rw [← integral_finsetSum _ (fun k _ => hg_int k)]
    have := integral_mono (integrable_const ((lo : ℝ) / prec))
      (integrable_finsetSum _ (fun k _ => hg_int k)) hseed
    simpa using this
  rw [bayesRisk_eq]
  have hK' : (0 : ℝ) < K := by exact_mod_cast hK
  rw [show ENNReal.ofReal ((lo : ℝ) / (prec * K)) = ENNReal.ofReal ((lo : ℝ) / prec) / K by
    rw [div_natCast_ofReal _ K hK, div_div]]
  apply ENNReal.div_le_div_right
  calc
    ENNReal.ofReal ((lo : ℝ) / prec) ≤ ENNReal.ofReal (∑ k, ∫ r, g k r ∂A.randomLaw) :=
      ENNReal.ofReal_le_ofReal hint
    _ = ∑ k, ENNReal.ofReal (∫ r, g k r ∂A.randomLaw) :=
      ENNReal.ofReal_sum_of_nonneg fun k _ => integral_nonneg (hg_nonneg k)
    _ ≤ _ := Finset.sum_le_sum fun k _ => hrisk k

end ThresholdHC.FiniteBayesAllocation
