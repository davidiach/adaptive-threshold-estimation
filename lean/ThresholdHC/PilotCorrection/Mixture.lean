import ThresholdHC.PilotCorrection.Specification

/-! The parameter space and the mixture law of one coin.

`rarityPolytope π ρ` is compact, convex and contains `0`. For `q` in the box
`[0,1]^k`, `coinLaw π Pplus Pminus q` is a probability measure, square
integrable features stay square integrable, and integrals are affine in `q`.
Under `FixedFeatures`, `Var_q(Y - βZ) = A q - θ(q)^2 - 2βc(q) + vβ^2` on `Q`,
with `A` and `c` affine. -/

noncomputable section
namespace ThresholdHC.PilotCorrection
open MeasureTheory ProbabilityTheory
open scoped ENNReal

variable {k : ℕ}

theorem rarityPolytope_eq (π : Fin k → ℝ) (ρ : ℝ) :
    rarityPolytope π ρ = Set.Icc (0 : Fin k → ℝ) 1 ∩ {q | ∑ i, π i * q i ≤ ρ} := by
  ext q
  simp only [rarityPolytope, Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_Icc,
    Pi.le_def, Pi.zero_apply, Pi.one_apply]
  constructor
  · rintro ⟨hb, hs⟩
    exact ⟨⟨fun i => (hb i).1, fun i => (hb i).2⟩, hs⟩
  · rintro ⟨⟨h0, h1⟩, hs⟩
    exact ⟨fun i => ⟨h0 i, h1 i⟩, hs⟩

theorem continuous_sum_affine (a b : Fin k → ℝ) :
    Continuous (fun q : Fin k → ℝ => ∑ i, (a i * q i + b i)) :=
  continuous_finsetSum _ fun i _ =>
    (continuous_const.mul (continuous_apply i)).add continuous_const

theorem rarityPolytope_isCompact (π : Fin k → ℝ) (ρ : ℝ) :
    IsCompact (rarityPolytope π ρ) := by
  rw [rarityPolytope_eq]
  refine isCompact_Icc.inter_right (isClosed_le ?_ continuous_const)
  simpa using continuous_sum_affine π 0

theorem rarityPolytope_convex (π : Fin k → ℝ) (ρ : ℝ) :
    Convex ℝ (rarityPolytope π ρ) := by
  intro p hp q hq a b ha hb hab
  refine ⟨fun i => ?_, ?_⟩
  · have h1 := hp.1 i
    have h2 := hq.1 i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    constructor <;> nlinarith
  · have hs : ∑ i, π i * (a • p + b • q) i =
        a * ∑ i, π i * p i + b * ∑ i, π i * q i := by
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum,
        ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [hs]
    have h1 := mul_le_mul_of_nonneg_left hp.2 ha
    have h2 := mul_le_mul_of_nonneg_left hq.2 hb
    have h3 : a * ρ + b * ρ = ρ := by rw [← add_mul, hab, one_mul]
    linarith

theorem zero_mem_rarityPolytope (π : Fin k → ℝ) {ρ : ℝ} (hρ : 0 ≤ ρ) :
    (0 : Fin k → ℝ) ∈ rarityPolytope π ρ :=
  ⟨fun _ => ⟨le_rfl, zero_le_one⟩, by simpa using hρ⟩

/-- Affine sums are affine along segments. -/
theorem sum_affine_segment (a b p q : Fin k → ℝ) (t : ℝ) :
    ∑ i, (a i * (p + t • (q - p)) i + b i) =
      ∑ i, (a i * p i + b i) +
        t * (∑ i, (a i * q i + b i) - ∑ i, (a i * p i + b i)) := by
  rw [← Finset.sum_sub_distrib, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
  ring

theorem signMass_eq_sum_affine (π q : Fin k → ℝ) :
    signMass π q = ∑ i, (π i * q i + (0 : Fin k → ℝ) i) := by
  simp [signMass]

section Law

variable {Ω : Type*} [MeasurableSpace Ω] (π : Fin k → ℝ)
  (Pplus Pminus : Fin k → Measure Ω)

theorem coinLaw_isProbability [∀ i, IsProbabilityMeasure (Pplus i)]
    [∀ i, IsProbabilityMeasure (Pminus i)] (hπ : ∀ i, 0 ≤ π i) (hsum : ∑ i, π i = 1)
    {q : Fin k → ℝ} (hq : ∀ i, 0 ≤ q i ∧ q i ≤ 1) :
    IsProbabilityMeasure (coinLaw π Pplus Pminus q) := by
  constructor
  simp only [coinLaw, Measure.finsetSum_apply, Measure.add_apply, Measure.smul_apply,
    measure_univ, smul_eq_mul, mul_one]
  have h1 : ∀ i, ENNReal.ofReal (π i * q i) + ENNReal.ofReal (π i * (1 - q i)) =
      ENNReal.ofReal (π i) := by
    intro i
    rw [← ENNReal.ofReal_add (mul_nonneg (hπ i) (hq i).1)
      (mul_nonneg (hπ i) (by linarith [(hq i).2]))]
    congr 1
    ring
  simp only [h1]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => hπ i), hsum, ENNReal.ofReal_one]

theorem memLp_coinLaw {g : Ω → ℝ}
    (h : ∀ i, MemLp g 2 (Pplus i) ∧ MemLp g 2 (Pminus i)) (q : Fin k → ℝ) :
    MemLp g 2 (coinLaw π Pplus Pminus q) := by
  unfold coinLaw
  refine Finset.sum_induction _ (fun μ => MemLp g 2 μ) (fun _ _ ha hb => ha.add_measure hb)
    memLp_measure_zero fun i _ => ?_
  exact ((h i).1.smul_measure ENNReal.ofReal_ne_top).add_measure
    ((h i).2.smul_measure ENNReal.ofReal_ne_top)

theorem integrable_coinLaw {g : Ω → ℝ}
    (h : ∀ i, Integrable g (Pplus i) ∧ Integrable g (Pminus i)) (q : Fin k → ℝ) :
    Integrable g (coinLaw π Pplus Pminus q) := by
  unfold coinLaw
  refine integrable_finsetSum_measure.mpr fun i _ => ?_
  exact ((h i).1.smul_measure ENNReal.ofReal_ne_top).add_measure
    ((h i).2.smul_measure ENNReal.ofReal_ne_top)

/-- Integrals under the coin law are affine in `q` on the box. -/
theorem integral_coinLaw (hπ : ∀ i, 0 ≤ π i) {g : Ω → ℝ}
    (h : ∀ i, Integrable g (Pplus i) ∧ Integrable g (Pminus i))
    {q : Fin k → ℝ} (hq : ∀ i, 0 ≤ q i ∧ q i ≤ 1) :
    (∫ ω, g ω ∂coinLaw π Pplus Pminus q) =
      ∑ i, (π i * ((∫ ω, g ω ∂Pplus i) - ∫ ω, g ω ∂Pminus i) * q i +
        π i * ∫ ω, g ω ∂Pminus i) := by
  unfold coinLaw
  rw [integral_finsetSum_measure fun i _ =>
    ((h i).1.smul_measure ENNReal.ofReal_ne_top).add_measure
      ((h i).2.smul_measure ENNReal.ofReal_ne_top)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_add_measure ((h i).1.smul_measure ENNReal.ofReal_ne_top)
      ((h i).2.smul_measure ENNReal.ofReal_ne_top),
    integral_smul_measure, integral_smul_measure,
    ENNReal.toReal_ofReal (mul_nonneg (hπ i) (hq i).1),
    ENNReal.toReal_ofReal (mul_nonneg (hπ i) (by linarith [(hq i).2])), smul_eq_mul,
    smul_eq_mul]
  ring

end Law

section Features

variable {Ω : Type*} [MeasurableSpace Ω] {π : Fin k → ℝ} {ρ : ℝ}
  {Pplus Pminus : Fin k → Measure Ω} [∀ i, IsProbabilityMeasure (Pplus i)]
  [∀ i, IsProbabilityMeasure (Pminus i)] {Y Z : Ω → ℝ} {v : ℝ}

/-- The variance on `Q`: `Var_q(Y - βZ) = A q - θ(q)^2 - 2βc(q) + vβ^2`, where `A`
and `c` are the affine mixtures of the conditional moments of `Y ^ 2` and
`Y * Z`. -/
theorem variance_coinLaw (hF : FixedFeatures π ρ Pplus Pminus Y Z v)
    {q : Fin k → ℝ} (hq : q ∈ rarityPolytope π ρ) (β : ℝ) :
    variance (fun ω => Y ω - β * Z ω) (coinLaw π Pplus Pminus q) =
      ∑ i, (π i * ((∫ ω, Y ω ^ 2 ∂Pplus i) - ∫ ω, Y ω ^ 2 ∂Pminus i) * q i +
          π i * ∫ ω, Y ω ^ 2 ∂Pminus i) -
        signMass π q ^ 2 -
        2 * β * ∑ i, (π i * ((∫ ω, Y ω * Z ω ∂Pplus i) - ∫ ω, Y ω * Z ω ∂Pminus i) * q i +
          π i * ∫ ω, Y ω * Z ω ∂Pminus i) +
        v * β ^ 2 := by
  obtain ⟨hπ, hsum, _, _, _, hL, _, hmom⟩ := hF
  have hbox := hq.1
  have := coinLaw_isProbability π Pplus Pminus hπ hsum hbox
  obtain ⟨hY1, hZ0, hZ2⟩ := hmom q hq
  have hYm : MemLp Y 2 (coinLaw π Pplus Pminus q) :=
    memLp_coinLaw π Pplus Pminus (fun i => ⟨(hL i).1, (hL i).2.1⟩) q
  have hZm : MemLp Z 2 (coinLaw π Pplus Pminus q) :=
    memLp_coinLaw π Pplus Pminus (fun i => ⟨(hL i).2.2.1, (hL i).2.2.2⟩) q
  have hW : MemLp (fun ω => Y ω - β * Z ω) 2 (coinLaw π Pplus Pminus q) :=
    hYm.sub (hZm.const_mul β)
  have hYY : ∀ μ : Measure Ω, MemLp Y 2 μ → Integrable (fun ω => Y ω ^ 2) μ :=
    fun μ h => h.integrable_sq
  have hYZ : ∀ μ : Measure Ω, MemLp Y 2 μ → MemLp Z 2 μ →
      Integrable (fun ω => Y ω * Z ω) μ :=
    fun μ h1 h2 => h1.integrable_mul h2
  have hA := integral_coinLaw π Pplus Pminus hπ (g := fun ω => Y ω ^ 2)
    (fun i => ⟨hYY _ (hL i).1, hYY _ (hL i).2.1⟩) hbox
  have hC := integral_coinLaw π Pplus Pminus hπ (g := fun ω => Y ω * Z ω)
    (fun i => ⟨hYZ _ (hL i).1 (hL i).2.2.1, hYZ _ (hL i).2.1 (hL i).2.2.2⟩) hbox
  rw [variance_eq_sub hW]
  have hsq : (fun ω => Y ω - β * Z ω) ^ 2 =
      fun ω => (Y ω ^ 2 - 2 * β * (Y ω * Z ω)) + β ^ 2 * Z ω ^ 2 := by
    funext ω
    simp only [Pi.pow_apply]
    ring
  have hY2 : Integrable (fun ω => Y ω ^ 2) (coinLaw π Pplus Pminus q) := hYm.integrable_sq
  have hZ2' : Integrable (fun ω => Z ω ^ 2) (coinLaw π Pplus Pminus q) := hZm.integrable_sq
  have hYZ' : Integrable (fun ω => Y ω * Z ω) (coinLaw π Pplus Pminus q) :=
    hYm.integrable_mul hZm
  have hI2 : (∫ ω, ((fun ω => Y ω - β * Z ω) ^ 2) ω ∂coinLaw π Pplus Pminus q) =
      (∫ ω, Y ω ^ 2 ∂coinLaw π Pplus Pminus q) -
        2 * β * (∫ ω, Y ω * Z ω ∂coinLaw π Pplus Pminus q) +
        β ^ 2 * ∫ ω, Z ω ^ 2 ∂coinLaw π Pplus Pminus q := by
    have h1 : Integrable (fun ω => Y ω ^ 2 - 2 * β * (Y ω * Z ω))
        (coinLaw π Pplus Pminus q) := hY2.sub (hYZ'.const_mul _)
    have h2 : Integrable (fun ω => β ^ 2 * Z ω ^ 2) (coinLaw π Pplus Pminus q) :=
      hZ2'.const_mul _
    have h3 : Integrable (fun ω => 2 * β * (Y ω * Z ω)) (coinLaw π Pplus Pminus q) :=
      hYZ'.const_mul _
    rw [hsq]
    simp only
    rw [integral_add h1 h2, integral_sub hY2 h3, integral_const_mul, integral_const_mul]
  have hI1 : (∫ ω, (fun ω => Y ω - β * Z ω) ω ∂coinLaw π Pplus Pminus q) =
      signMass π q := by
    simp only
    rw [integral_sub (hYm.integrable (by norm_num))
      ((hZm.integrable (by norm_num)).const_mul _), integral_const_mul, hY1, hZ0]
    ring
  rw [hI2, hI1, hA, hC, hZ2]
  ring

end Features

end ThresholdHC.PilotCorrection
