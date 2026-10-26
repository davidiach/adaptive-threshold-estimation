import ThresholdHC.Uniform713.Common

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology

namespace ThresholdHC.Uniform713

/-- The independently sampled geometric level law. -/
def levelMeasure : Measure ℕ :=
  Measure.sum (fun l => ENNReal.ofReal (levelProb l) • Measure.dirac l)

@[simp] theorem levelMeasure_singleton (l : ℕ) :
    levelMeasure {l} = ENNReal.ofReal (levelProb l) :=
  Measure.sum_smul_dirac_singleton

@[simp] theorem levelMeasure_real_singleton (l : ℕ) :
    levelMeasure.real {l} = levelProb l := by
  rw [measureReal_def, levelMeasure_singleton, ENNReal.toReal_ofReal (levelProb_pos l).le]

instance levelMeasure_probability : IsProbabilityMeasure levelMeasure where
  measure_univ := by
    simp only [levelMeasure, Measure.sum_apply _ MeasurableSet.univ,
      Measure.smul_apply, Measure.dirac_apply' _ MeasurableSet.univ,
      Set.indicator_univ, Pi.one_apply, smul_eq_mul, mul_one]
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun l => (levelProb_pos l).le)
      hasSum_levelProb.summable, hasSum_levelProb.tsum_eq]
    norm_num

def samplingMeasure {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) : Measure (ℕ × Ω) :=
  levelMeasure.prod μ

instance samplingMeasure_probability {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] : IsProbabilityMeasure (samplingMeasure μ) := by
  unfold samplingMeasure
  infer_instance

theorem samplingMeasure_indep {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] :
    IndepFun (Prod.fst : ℕ × Ω → ℕ) Prod.snd (samplingMeasure μ) :=
  indepFun_prod (X := id) (Y := id) measurable_id measurable_id

def sampled {Ω : Type*} (f : ℕ → Ω → ℝ) (x : ℕ × Ω) : ℝ := f x.1 x.2

def estimator {Ω : Type*} (z : ℕ → Ω → ℝ) (x : ℕ × Ω) : ℝ :=
  increment (fun k => z k x.2) x.1 / levelProb x.1

theorem integrable_levelMeasure_iff (g : ℕ → ℝ) :
    Integrable g levelMeasure ↔ Summable (fun l => levelProb l * ‖g l‖) := by
  simp only [levelMeasure, integrable_sum_dirac_iff (fun _ => ENNReal.ofReal_ne_top),
    ENNReal.toReal_ofReal (levelProb_pos _).le]

theorem integral_levelMeasure (g : ℕ → ℝ) :
    ∫ l, g l ∂levelMeasure = ∑' l, levelProb l * g l := by
  simp only [levelMeasure, integral_sum_dirac (fun _ => ENNReal.ofReal_ne_top),
    ENNReal.toReal_ofReal (levelProb_pos _).le, smul_eq_mul]

theorem measurable_sampled {Ω : Type*} [MeasurableSpace Ω]
    {f : ℕ → Ω → ℝ} (hf : ∀ l, Measurable (f l)) : Measurable (sampled f) :=
  measurable_from_prod_countable_right hf

theorem integrable_sampled {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [SFinite μ] {f : ℕ → Ω → ℝ}
    (hm : ∀ l, Measurable (f l)) (hi : ∀ l, Integrable (f l) μ)
    (hs : Summable (fun l => levelProb l * ∫ ω, ‖f l ω‖ ∂μ)) :
    Integrable (sampled f) (samplingMeasure μ) := by
  apply (integrable_prod_iff (measurable_sampled hm).aestronglyMeasurable).2
  refine ⟨ae_of_all _ hi, ?_⟩
  apply (integrable_levelMeasure_iff _).2
  simpa only [sampled, Real.norm_eq_abs,
    abs_of_nonneg (integral_nonneg (fun _ => abs_nonneg _))] using hs

theorem integral_sampled {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [SFinite μ] {f : ℕ → Ω → ℝ}
    (hi : Integrable (sampled f) (samplingMeasure μ)) :
    ∫ x, sampled f x ∂samplingMeasure μ = ∑' l, levelProb l * ∫ ω, f l ω ∂μ := by
  rw [samplingMeasure, integral_prod _ hi, integral_levelMeasure]
  rfl

theorem measurable_increment {Ω : Type*} [MeasurableSpace Ω]
    {z : ℕ → Ω → ℝ} (hz : ∀ l, Measurable (z l)) (l : ℕ) :
    Measurable (fun ω => increment (fun k => z k ω) l) := by
  cases l with
  | zero => exact hz 0
  | succ l => exact (hz (l+1)).sub (hz l)

theorem integrable_increment {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {z : ℕ → Ω → ℝ} (hz : ∀ l, Integrable (z l) μ) (l : ℕ) :
    Integrable (fun ω => increment (fun k => z k ω) l) μ := by
  cases l with
  | zero => exact hz 0
  | succ l => exact (hz (l+1)).sub (hz l)

theorem measurable_estimator {Ω : Type*} [MeasurableSpace Ω]
    {z : ℕ → Ω → ℝ} (hz : ∀ l, Measurable (z l)) : Measurable (estimator z) := by
  apply measurable_from_prod_countable_right
  intro l
  simpa only [estimator] using (measurable_increment hz l).div_const (levelProb l)

/-- Square integrability follows from the sum of the actual increment second moments. -/
theorem estimator_memLp {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [SFinite μ] {z : ℕ → Ω → ℝ}
    (hz : ∀ l, Measurable (z l))
    (hi2 : ∀ l, Integrable (fun ω => (increment (fun k => z k ω) l)^2) μ)
    (hs : Summable (fun l => (∫ ω, (increment (fun k => z k ω) l)^2 ∂μ) / levelProb l)) :
    MemLp (estimator z) 2 (samplingMeasure μ) := by
  apply (memLp_two_iff_integrable_sq (measurable_estimator hz).aestronglyMeasurable).2
  change Integrable (sampled (fun l ω => (increment (fun k => z k ω) l / levelProb l)^2)) _
  apply integrable_sampled
  · intro l
    exact ((measurable_increment hz l).div_const _).pow_const _
  · intro l
    simpa only [div_pow] using (hi2 l).div_const ((levelProb l)^2)
  · convert hs using 1
    ext l
    simp only [Real.norm_eq_abs, abs_pow, sq_abs]
    simp only [div_pow, integral_div]
    field_simp [(levelProb_pos l).ne']

theorem estimator_second_moment {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [SFinite μ] {z : ℕ → Ω → ℝ}
    (hY : MemLp (estimator z) 2 (samplingMeasure μ)) :
    ∫ x, (estimator z x)^2 ∂samplingMeasure μ =
      ∑' l, (∫ ω, (increment (fun k => z k ω) l)^2 ∂μ) / levelProb l := by
  change ∫ x, sampled (fun l ω => (increment (fun k => z k ω) l / levelProb l)^2) x
    ∂samplingMeasure μ = _
  rw [integral_sampled hY.integrable_sq]
  congr 1
  ext l
  simp only [div_pow, integral_div]
  field_simp [(levelProb_pos l).ne']

theorem integral_estimator {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [SFinite μ] {z : ℕ → Ω → ℝ}
    (hY : Integrable (estimator z) (samplingMeasure μ)) :
    ∫ x, estimator z x ∂samplingMeasure μ =
      ∑' l, ∫ ω, increment (fun k => z k ω) l ∂μ := by
  change ∫ x, sampled (fun l ω => increment (fun k => z k ω) l / levelProb l) x
    ∂samplingMeasure μ = _
  rw [integral_sampled (f := fun l ω => increment (fun k => z k ω) l / levelProb l) hY]
  congr 1
  ext l
  rw [integral_div]
  field_simp [(levelProb_pos l).ne']

theorem summable_mean_increments {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [SFinite μ] {z : ℕ → Ω → ℝ}
    (hY : Integrable (estimator z) (samplingMeasure μ)) :
    Summable (fun l => ∫ ω, increment (fun k => z k ω) l ∂μ) := by
  have hg : Integrable (fun l => ∫ ω, estimator z (l,ω) ∂μ) levelMeasure :=
    hY.integral_prod_left
  have hs := (integrable_levelMeasure_iff _).1 hg
  have hsn : Summable (fun l => levelProb l * ∫ ω, estimator z (l,ω) ∂μ) :=
    hs.of_norm_bounded (fun l => by rw [norm_mul, Real.norm_of_nonneg (levelProb_pos l).le])
  convert hsn using 1
  ext l
  simp only [estimator, integral_div]
  field_simp [(levelProb_pos l).ne']

/-- Telescoping and convergence of the classifier means imply exact unbiasedness. -/
theorem estimator_unbiased {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [SFinite μ] {z : ℕ → Ω → ℝ} {a : ℝ}
    (hz : ∀ l, Integrable (z l) μ)
    (hY : Integrable (estimator z) (samplingMeasure μ))
    (hlim : Tendsto (fun l => ∫ ω, z l ω ∂μ) atTop (𝓝 a)) :
    ∫ x, estimator z x ∂samplingMeasure μ = a := by
  rw [integral_estimator hY]
  have hinc : ∀ l, (∫ ω, increment (fun k => z k ω) l ∂μ) =
      increment (fun k => ∫ ω, z k ω ∂μ) l := by
    intro l
    cases l with
    | zero => rfl
    | succ l => exact integral_sub (hz (l+1)) (hz l)
  have hs := (summable_mean_increments hY).hasSum.tendsto_sum_nat.comp
    (tendsto_add_atTop_nat 1)
  simp only [Function.comp_def, hinc, sum_increment] at hs
  simpa only [hinc] using tendsto_nhds_unique hs hlim

theorem integrable_binary {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsFiniteMeasure μ] {z : Ω → ℝ}
    (hz : Measurable z) (hb : ∀ ω, z ω = 0 ∨ z ω = 1) : Integrable z μ := by
  apply (integrable_const (1 : ℝ)).mono' hz.aestronglyMeasurable
  filter_upwards with ω
  rcases hb ω with h | h <;> simp [h]

/-- For binary decisions the L¹ error is precisely the probability of a wrong answer. -/
theorem integral_binary_error {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {z s : Ω → ℝ}
    (hz : Measurable z) (hs : Measurable s)
    (hbz : ∀ ω, z ω = 0 ∨ z ω = 1) (hbs : ∀ ω, s ω = 0 ∨ s ω = 1) :
    (∫ ω, |z ω - s ω| ∂μ) = μ.real {ω | z ω ≠ s ω} := by
  have heq : (fun ω => |z ω-s ω|) = {ω | z ω ≠ s ω}.indicator (fun _ => (1 : ℝ)) := by
    funext ω
    rcases hbz ω with hz0 | hz0 <;> rcases hbs ω with hs0 | hs0 <;>
      simp [hz0, hs0, Set.indicator]
  rw [heq]
  exact integral_indicator_one (measurableSet_eq_fun hz hs).compl

theorem abs_mean_error_le {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsFiniteMeasure μ] {z s : Ω → ℝ}
    (hz : Measurable z) (hs : Measurable s)
    (hbz : ∀ ω, z ω = 0 ∨ z ω = 1) (hbs : ∀ ω, s ω = 0 ∨ s ω = 1) :
    |(∫ ω, z ω ∂μ) - ∫ ω, s ω ∂μ| ≤ μ.real {ω | z ω ≠ s ω} := by
  rw [← integral_sub (integrable_binary hz hbz) (integrable_binary hs hbs)]
  exact abs_integral_le_integral_abs.trans_eq (integral_binary_error hz hs hbz hbs)

theorem tendsto_mean_of_binary_error {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsFiniteMeasure μ] {z : ℕ → Ω → ℝ} {s : Ω → ℝ}
    (hz : ∀ l, Measurable (z l)) (hs : Measurable s)
    (hbz : ∀ l ω, z l ω = 0 ∨ z l ω = 1) (hbs : ∀ ω, s ω = 0 ∨ s ω = 1)
    (herr : Tendsto (fun l => μ.real {ω | z l ω ≠ s ω}) atTop (𝓝 0)) :
    Tendsto (fun l => ∫ ω, z l ω ∂μ) atTop (𝓝 (∫ ω, s ω ∂μ)) := by
  apply tendsto_iff_norm_sub_tendsto_zero.2
  apply squeeze_zero (fun _ => norm_nonneg _) _ herr
  intro l
  exact abs_mean_error_le (hz l) hs (hbz l) hbs

end ThresholdHC.Uniform713
