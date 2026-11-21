import ThresholdHC.Tier6.HardPairModel

/-! Seed integrals of the thinning estimators. The seed is a pair of
independent arrays: uniforms on the unit interval and magnitudes with the gap
law. Index i is selected when its uniform falls below an acceptance
probability at its magnitude. The second moment of an affine statistic of the
selected values is computed in two stages: first over the uniforms at a fixed
magnitude array, then over the magnitudes. Each stage uses the exact
second-moment identity for a finite sum of independent bounded variables,
with independence of the coordinates of an infinite product measure. -/
noncomputable section
namespace ThresholdHC.OracleUpper
open MeasureTheory ProbabilityTheory
open ThresholdHC.Tier6

theorem integrable_of_abs_le {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsFiniteMeasure P] (f : Ω → ℝ) (hf : Measurable f) (C : ℝ) (hC : ∀ x, |f x| ≤ C) :
    Integrable f P :=
  (integrable_const C).mono' hf.aestronglyMeasurable
    (ae_of_all _ fun x => by rw [Real.norm_eq_abs]; exact hC x)

private theorem abs_sum_le_card (m : ℕ) (X : ℕ → ℝ) (C : ℝ) (hX : ∀ i, |X i| ≤ C) :
    |∑ i ∈ Finset.range m, X i| ≤ m * C := by
  calc
    _ ≤ ∑ i ∈ Finset.range m, |X i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i ∈ Finset.range m, C := Finset.sum_le_sum fun i _ => hX i
    _ = m * C := by simp

/-- Exact second moment of an affine function of a finite sum of independent
bounded variables. -/
theorem indep_square_integral {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ) (hX : ∀ i, Measurable (X i)) (C : ℝ)
    (hC : ∀ i ω, |X i ω| ≤ C) (hind : iIndepFun X P) (m : ℕ) (κ β : ℝ) :
    ∫ ω, (κ + β * ∑ i ∈ Finset.range m, X i ω)^2 ∂P =
      (κ + β * ∑ i ∈ Finset.range m, ∫ ω, X i ω ∂P)^2 +
        β^2 * ∑ i ∈ Finset.range m, (∫ ω, (X i ω)^2 ∂P - (∫ ω, X i ω ∂P)^2) := by
  have hL (i : ℕ) : MemLp (X i) 2 P := MemLp.of_bound (hX i).aestronglyMeasurable C
    (ae_of_all _ fun ω => by rw [Real.norm_eq_abs]; exact hC i ω)
  have hI (i : ℕ) : Integrable (X i) P := integrable_of_abs_le P _ (hX i) C (hC i)
  let S : Ω → ℝ := ∑ i ∈ Finset.range m, X i
  have hS (ω : Ω) : S ω = ∑ i ∈ Finset.range m, X i ω := Finset.sum_apply _ _ _
  have hSL : MemLp S 2 P := memLp_finsetSum' _ (fun i _ => hL i)
  have hSm : Measurable S := by
    rw [show S = fun ω => ∑ i ∈ Finset.range m, X i ω from funext hS]
    exact Finset.measurable_sum _ (fun i _ => hX i)
  let Y : Ω → ℝ := fun ω => κ + β * S ω
  have hYL : MemLp Y 2 P := (memLp_const κ).add (hSL.const_mul β)
  have hvarS : variance S P = ∑ i ∈ Finset.range m, variance (X i) P :=
    IndepFun.variance_sum (fun i _ => hL i) (fun i _ j _ hij => hind.indepFun hij)
  have hvarY : variance Y P = β^2 * variance S P := by
    have h1 := variance_const_add (μ := P) (X := fun ω => β * S ω)
      (hSm.const_mul β).aestronglyMeasurable κ
    have h2 := variance_const_mul β S P
    exact h1.trans h2
  have hEY : ∫ ω, Y ω ∂P = κ + β * ∑ i ∈ Finset.range m, ∫ ω, X i ω ∂P := by
    simp only [Y]
    rw [integral_add (integrable_const κ) ((hSL.integrable one_le_two).const_mul β),
      integral_const, integral_const_mul]
    simp only [hS]
    rw [integral_finsetSum _ (fun i _ => hI i)]
    simp
  have hY := variance_eq_sub hYL
  have hvar (i : ℕ) := variance_eq_sub (hL i)
  have hlhs : ∫ ω, (κ + β * ∑ i ∈ Finset.range m, X i ω)^2 ∂P = P[Y^2] := by
    congr 1
    funext ω
    simp only [Y, Pi.pow_apply, hS]
  rw [hlhs, ← hEY]
  have hsum : ∑ i ∈ Finset.range m, (∫ ω, (X i ω)^2 ∂P - (∫ ω, X i ω ∂P)^2) =
      ∑ i ∈ Finset.range m, variance (X i) P := by
    apply Finset.sum_congr rfl
    intro i _
    rw [hvar i]
    rfl
  rw [hsum, ← hvarS, ← hvarY, hY]
  ring

/-- Seeds of the thinning estimators. -/
abbrev ThinSeed := (ℕ → unitInterval) × (ℕ → Gap)

/-- Independent uniform variables on the unit interval. -/
def uniformLaw : Measure (ℕ → unitInterval) := Measure.infinitePi (fun _ => volume)

instance uniformLaw_probability : IsProbabilityMeasure uniformLaw := by
  unfold uniformLaw
  infer_instance

/-- Independent uniforms together with an iid magnitude array. -/
def thinSeedLaw (μ : Measure Gap) : Measure ThinSeed :=
  uniformLaw.prod (Measure.infinitePi (fun _ => μ))

instance thinSeedLaw_probability (μ : Measure Gap) [IsProbabilityMeasure μ] :
    IsProbabilityMeasure (thinSeedLaw μ) := by
  unfold thinSeedLaw
  infer_instance

/-- The value v when the uniform t falls at or below r, and zero otherwise. -/
def thinned (r v : ℝ) (t : unitInterval) : ℝ := if (t : ℝ) ≤ r then v else 0

theorem measurable_thinned (r v : ℝ) : Measurable (thinned r v) :=
  Measurable.ite (measurableSet_le measurable_subtype_coe measurable_const)
    measurable_const measurable_const

theorem abs_thinned_le (r v : ℝ) (t : unitInterval) : |thinned r v t| ≤ |v| := by
  unfold thinned
  split_ifs <;> simp

theorem thinned_sq (r v : ℝ) (t : unitInterval) : (thinned r v t)^2 = thinned r (v^2) t := by
  unfold thinned
  split_ifs <;> simp

theorem integral_thinned (r v : ℝ) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    ∫ t, thinned r v t ∂(volume : Measure unitInterval) = r * v := by
  have hset : {t : unitInterval | (t : ℝ) ≤ r} = Set.Iic ⟨r, hr0, hr1⟩ := by
    ext t
    simp only [Set.mem_ofPred_eq, Set.mem_Iic]
    exact Iff.rfl
  have he : thinned r v = Set.indicator {t : unitInterval | (t : ℝ) ≤ r} (fun _ => v) := by
    funext t
    simp only [thinned, Set.indicator, Set.mem_ofPred_eq]
  rw [he, integral_indicator_const v (measurableSet_le measurable_subtype_coe measurable_const),
    hset, Measure.real, unitInterval.volume_Iic, ENNReal.toReal_ofReal hr0, smul_eq_mul]

theorem integral_eval_infinitePi {X : Type} [MeasurableSpace X] (P : Measure X)
    [IsProbabilityMeasure P] (i : ℕ) (f : X → ℝ) (hf : Measurable f) :
    ∫ ω, f (ω i) ∂Measure.infinitePi (fun _ : ℕ => P) = ∫ x, f x ∂P := by
  have h := integral_map (μ := Measure.infinitePi (fun _ : ℕ => P)) (φ := fun ω => ω i)
    (measurable_pi_apply i).aemeasurable (f := f)
    (by rw [Measure.infinitePi_map_eval]; exact hf.aestronglyMeasurable)
  rw [Measure.infinitePi_map_eval] at h
  exact h.symm

private theorem sq_affine_bound (κ β : ℝ) (m : ℕ) (C : ℝ) (X : ℕ → ℝ) (hX : ∀ i, |X i| ≤ C) :
    |(κ + β * ∑ i ∈ Finset.range m, X i)^2| ≤ (|κ| + |β| * (m * C))^2 := by
  have h := abs_sum_le_card m X C hX
  have h1 : |κ + β * ∑ i ∈ Finset.range m, X i| ≤ |κ| + |β| * (m * C) := by
    refine (abs_add_le _ _).trans (add_le_add le_rfl ?_)
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left h (abs_nonneg β)
  rw [abs_of_nonneg (sq_nonneg _), ← sq_abs]
  exact pow_le_pow_left₀ (abs_nonneg _) h1 2

private theorem moment_bound (κ β : ℝ) (m : ℕ) (C : ℝ) (X W : ℕ → ℝ) (hX : ∀ i, |X i| ≤ C)
    (hW : ∀ i, |W i| ≤ C) :
    |(κ + β * ∑ i ∈ Finset.range m, X i)^2 + β^2 * ∑ i ∈ Finset.range m, W i| ≤
      (|κ| + |β| * (m * C))^2 + β^2 * (m * C) := by
  refine (abs_add_le _ _).trans (add_le_add (sq_affine_bound κ β m C X hX) ?_)
  rw [abs_mul, abs_of_nonneg (sq_nonneg β)]
  exact mul_le_mul_of_nonneg_left (abs_sum_le_card m W C hW) (sq_nonneg β)

private theorem measurable_moment {Ω : Type} [MeasurableSpace Ω] (κ β : ℝ) (m : ℕ)
    (X W : ℕ → Ω → ℝ) (hX : ∀ i, Measurable (X i)) (hW : ∀ i, Measurable (W i)) :
    Measurable (fun ω => (κ + β * ∑ i ∈ Finset.range m, X i ω)^2 +
      β^2 * ∑ i ∈ Finset.range m, W i ω) :=
  ((measurable_const.add (measurable_const.mul (Finset.measurable_sum _ fun i _ => hX i))).pow_const
    2).add (measurable_const.mul (Finset.measurable_sum _ fun i _ => hW i))

/-- Joint measurability of a thinned value read from a seed. -/
theorem measurable_seed_thinned (p f : Gap → ℝ) (hp : Measurable p) (hf : Measurable f) (i : ℕ) :
    Measurable (fun u : ThinSeed => thinned (p (u.2 i)) (f (u.2 i)) (u.1 i)) := by
  unfold thinned
  exact Measurable.ite (measurableSet_le
    (measurable_subtype_coe.comp ((measurable_pi_apply i).comp measurable_fst))
    (hp.comp ((measurable_pi_apply i).comp measurable_snd)))
    (hf.comp ((measurable_pi_apply i).comp measurable_snd)) measurable_const

/-- First stage: the uniforms at a fixed array of acceptance probabilities. -/
theorem uniform_moment (r v w : ℕ → ℝ) (hr : ∀ i, 0 ≤ r i ∧ r i ≤ 1) (C : ℝ)
    (hv : ∀ i, |v i| ≤ C) (hw : ∀ i, |w i| ≤ C) (m : ℕ) (κ β : ℝ) :
    ∫ U, ((κ + β * ∑ i ∈ Finset.range m, thinned (r i) (v i) (U i))^2 +
        β^2 * ∑ i ∈ Finset.range m, thinned (r i) (w i) (U i)) ∂uniformLaw =
      (κ + β * ∑ i ∈ Finset.range m, r i * v i)^2 +
        β^2 * ∑ i ∈ Finset.range m, (r i * (v i)^2 - (r i * v i)^2 + r i * w i) := by
  let X : ℕ → (ℕ → unitInterval) → ℝ := fun i U => thinned (r i) (v i) (U i)
  let W : ℕ → (ℕ → unitInterval) → ℝ := fun i U => thinned (r i) (w i) (U i)
  have hXm (i : ℕ) : Measurable (X i) := (measurable_thinned _ _).comp (measurable_pi_apply i)
  have hWm (i : ℕ) : Measurable (W i) := (measurable_thinned _ _).comp (measurable_pi_apply i)
  have hXb (i : ℕ) (U : ℕ → unitInterval) : |X i U| ≤ C := (abs_thinned_le _ _ _).trans (hv i)
  have hWb (i : ℕ) (U : ℕ → unitInterval) : |W i U| ≤ C := (abs_thinned_le _ _ _).trans (hw i)
  have hind : iIndepFun X uniformLaw :=
    iIndepFun_infinitePi (P := fun _ => volume) (X := fun i => thinned (r i) (v i))
      (fun i => measurable_thinned _ _)
  have hE (i : ℕ) (x : ℝ) : ∫ U, thinned (r i) x (U i) ∂uniformLaw = r i * x := by
    rw [uniformLaw, integral_eval_infinitePi volume i (thinned (r i) x) (measurable_thinned _ _),
      integral_thinned _ _ (hr i).1 (hr i).2]
  have hEX2 (i : ℕ) : ∫ U, (X i U)^2 ∂uniformLaw = r i * (v i)^2 := by
    simp only [X, thinned_sq]
    exact hE i _
  have hsqI : Integrable (fun U => (κ + β * ∑ i ∈ Finset.range m, X i U)^2) uniformLaw :=
    integrable_of_abs_le _ _
      ((measurable_const.add (measurable_const.mul
        (Finset.measurable_sum _ fun i _ => hXm i))).pow_const 2) _
      (fun U => sq_affine_bound κ β m C (fun i => X i U) (fun i => hXb i U))
  have hWI (i : ℕ) : Integrable (W i) uniformLaw := integrable_of_abs_le _ _ (hWm i) C (hWb i)
  change ∫ U, ((κ + β * ∑ i ∈ Finset.range m, X i U)^2 +
      β^2 * ∑ i ∈ Finset.range m, W i U) ∂uniformLaw = _
  rw [integral_add hsqI ((integrable_finsetSum _ (fun i _ => hWI i)).const_mul _),
    integral_const_mul, integral_finsetSum _ (fun i _ => hWI i),
    indep_square_integral uniformLaw X hXm C hXb hind m κ β]
  simp only [hEX2, X, W, hE]
  rw [Finset.sum_add_distrib]
  ring

/-- Second stage: the magnitude array. -/
theorem array_moment (μ : Measure Gap) [IsProbabilityMeasure μ] (Y Z : Gap → ℝ)
    (hY : Measurable Y) (hZ : Measurable Z) (C : ℝ) (hYb : ∀ d, |Y d| ≤ C)
    (hZb : ∀ d, |Z d| ≤ C) (m : ℕ) (κ β : ℝ) :
    ∫ a, ((κ + β * ∑ i ∈ Finset.range m, Y (a i))^2 +
        β^2 * ∑ i ∈ Finset.range m, Z (a i)) ∂Measure.infinitePi (fun _ => μ) =
      (κ + β * (m * ∫ d, Y d ∂μ))^2 +
        β^2 * (m * (∫ d, (Y d)^2 ∂μ - (∫ d, Y d ∂μ)^2 + ∫ d, Z d ∂μ)) := by
  let P := Measure.infinitePi (fun _ : ℕ => μ)
  let X : ℕ → (ℕ → Gap) → ℝ := fun i a => Y (a i)
  let W : ℕ → (ℕ → Gap) → ℝ := fun i a => Z (a i)
  have hXm (i : ℕ) : Measurable (X i) := hY.comp (measurable_pi_apply i)
  have hWm (i : ℕ) : Measurable (W i) := hZ.comp (measurable_pi_apply i)
  have hind : iIndepFun X P :=
    iIndepFun_infinitePi (P := fun _ => μ) (X := fun _ => Y) (fun _ => hY)
  have hsqI : Integrable (fun a => (κ + β * ∑ i ∈ Finset.range m, X i a)^2) P :=
    integrable_of_abs_le _ _
      ((measurable_const.add (measurable_const.mul
        (Finset.measurable_sum _ fun i _ => hXm i))).pow_const 2) _
      (fun a => sq_affine_bound κ β m C (fun i => X i a) (fun i => hYb _))
  have hWI (i : ℕ) : Integrable (W i) P := integrable_of_abs_le _ _ (hWm i) C (fun a => hZb _)
  change ∫ a, ((κ + β * ∑ i ∈ Finset.range m, X i a)^2 +
      β^2 * ∑ i ∈ Finset.range m, W i a) ∂P = _
  rw [integral_add hsqI ((integrable_finsetSum _ (fun i _ => hWI i)).const_mul _),
    integral_const_mul, integral_finsetSum _ (fun i _ => hWI i),
    indep_square_integral P X hXm C (fun i a => hYb _) hind m κ β]
  have hE (i : ℕ) (f : Gap → ℝ) (hf : Measurable f) : ∫ a, f (a i) ∂P = ∫ d, f d ∂μ :=
    integral_eval_infinitePi μ i f hf
  simp only [X, W, hE _ _ hY, hE _ _ hZ, hE _ _ (hY.pow_const 2), Finset.sum_const,
    Finset.card_range, nsmul_eq_mul]
  ring

/-- Exact second moment of the thinned statistic over the whole seed. -/
theorem seed_moment (μ : Measure Gap) [IsProbabilityMeasure μ] (p e : Gap → ℝ)
    (hp : Measurable p) (he : Measurable e) (hp01 : ∀ d, 0 ≤ p d ∧ p d ≤ 1)
    (heb : ∀ d, |e d| ≤ 1) (m : ℕ) (κ β : ℝ) :
    ∫ u, ((κ + β * ∑ i ∈ Finset.range m, thinned (p (u.2 i)) (e (u.2 i)) (u.1 i))^2 +
        β^2 * ∑ i ∈ Finset.range m, thinned (p (u.2 i)) (1 - (e (u.2 i))^2) (u.1 i))
        ∂thinSeedLaw μ =
      (κ + β * (m * ∫ d, p d * e d ∂μ))^2 +
        β^2 * (m * (∫ d, p d ∂μ - (∫ d, p d * e d ∂μ)^2)) := by
  have hw (d : Gap) : |1 - (e d)^2| ≤ 1 := by
    have h1 := heb d
    have h2 : (e d)^2 ≤ 1 := by rw [← sq_abs]; nlinarith [abs_nonneg (e d)]
    rw [abs_le]
    constructor <;> nlinarith [sq_nonneg (e d)]
  have hG : Integrable (fun u : ThinSeed =>
      (κ + β * ∑ i ∈ Finset.range m, thinned (p (u.2 i)) (e (u.2 i)) (u.1 i))^2 +
        β^2 * ∑ i ∈ Finset.range m, thinned (p (u.2 i)) (1 - (e (u.2 i))^2) (u.1 i))
      (thinSeedLaw μ) :=
    integrable_of_abs_le _ _ (measurable_moment κ β m _ _
      (fun i => measurable_seed_thinned p e hp he i)
      (fun i => measurable_seed_thinned p (fun d => 1 - (e d)^2) hp
        (measurable_const.sub (he.pow_const 2)) i)) _
      (fun u => moment_bound κ β m 1 _ _ (fun i => (abs_thinned_le _ _ _).trans (heb _))
        (fun i => (abs_thinned_le _ _ _).trans (hw _)))
  unfold thinSeedLaw
  rw [integral_prod_symm _ hG]
  have inner (a : ℕ → Gap) :
      ∫ U, ((κ + β * ∑ i ∈ Finset.range m, thinned (p (a i)) (e (a i)) (U i))^2 +
        β^2 * ∑ i ∈ Finset.range m, thinned (p (a i)) (1 - (e (a i))^2) (U i)) ∂uniformLaw =
      (κ + β * ∑ i ∈ Finset.range m, p (a i) * e (a i))^2 +
        β^2 * ∑ i ∈ Finset.range m, (p (a i) - (p (a i) * e (a i))^2) := by
    rw [uniform_moment (fun i => p (a i)) (fun i => e (a i)) (fun i => 1 - (e (a i))^2)
      (fun i => hp01 _) 1 (fun i => heb _) (fun i => hw _) m κ β]
    congr 2
    apply Finset.sum_congr rfl
    intro i _
    ring
  simp only [inner]
  have hpe : Measurable (fun d => p d * e d) := hp.mul he
  have hZ : Measurable (fun d => p d - (p d * e d)^2) := hp.sub (hpe.pow_const 2)
  have hpeb (d : Gap) : |p d * e d| ≤ 2 := by
    rw [abs_mul, abs_of_nonneg (hp01 d).1]
    nlinarith [hp01 d, heb d, abs_nonneg (e d)]
  have hZb (d : Gap) : |p d - (p d * e d)^2| ≤ 2 := by
    have h1 : |p d * e d| ≤ 1 := by
      rw [abs_mul, abs_of_nonneg (hp01 d).1]
      nlinarith [hp01 d, heb d, abs_nonneg (e d)]
    have h2 : (p d * e d)^2 ≤ 1 := by rw [← sq_abs]; nlinarith [abs_nonneg (p d * e d)]
    rw [abs_le]
    constructor <;> nlinarith [hp01 d, sq_nonneg (p d * e d)]
  rw [array_moment μ (fun d => p d * e d) (fun d => p d - (p d * e d)^2) hpe hZ 2 hpeb hZb m κ β]
  have hI1 : Integrable p μ := integrable_of_abs_le _ _ hp 1 (fun d => by
    rw [abs_of_nonneg (hp01 d).1]; exact (hp01 d).2)
  have hI2 : Integrable (fun d => (p d * e d)^2) μ := integrable_of_abs_le _ _ (hpe.pow_const 2) 4
    (fun d => by
      rw [abs_of_nonneg (sq_nonneg _), ← sq_abs]
      nlinarith [hpeb d, abs_nonneg (p d * e d)])
  rw [integral_sub hI1 hI2]
  ring

/-- First moment of a thinned sum over the whole seed. -/
theorem seed_linear (μ : Measure Gap) [IsProbabilityMeasure μ] (p f : Gap → ℝ)
    (hp : Measurable p) (hf : Measurable f) (hp01 : ∀ d, 0 ≤ p d ∧ p d ≤ 1) (C : ℝ)
    (hfb : ∀ d, |f d| ≤ C) (m : ℕ) :
    ∫ u, ∑ i ∈ Finset.range m, thinned (p (u.2 i)) (f (u.2 i)) (u.1 i) ∂thinSeedLaw μ =
      m * ∫ d, p d * f d ∂μ := by
  have hI (i : ℕ) : Integrable (fun u : ThinSeed => thinned (p (u.2 i)) (f (u.2 i)) (u.1 i))
      (thinSeedLaw μ) :=
    integrable_of_abs_le _ _ (measurable_seed_thinned p f hp hf i) C
      (fun u => (abs_thinned_le _ _ _).trans (hfb _))
  rw [integral_finsetSum _ (fun i _ => hI i)]
  have each (i : ℕ) : ∫ u, thinned (p (u.2 i)) (f (u.2 i)) (u.1 i) ∂thinSeedLaw μ =
      ∫ d, p d * f d ∂μ := by
    have hi := hI i
    unfold thinSeedLaw at hi ⊢
    rw [integral_prod_symm _ hi]
    have inner (a : ℕ → Gap) :
        ∫ U, thinned (p (a i)) (f (a i)) (U i) ∂uniformLaw = p (a i) * f (a i) := by
      rw [uniformLaw, integral_eval_infinitePi volume i _ (measurable_thinned _ _),
        integral_thinned _ _ (hp01 _).1 (hp01 _).2]
    simp only [inner]
    exact integral_eval_infinitePi μ i (fun d => p d * f d) (hp.mul hf)
  simp only [each, Finset.sum_const, Finset.card_range, nsmul_eq_mul]

end ThresholdHC.OracleUpper
