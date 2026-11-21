import ThresholdHC.AffineComparison.Saddle
import ThresholdHC.AffineComparison.Moments
import ThresholdHC.CriticalEntropy.FiniteCentering
import ThresholdHC.CriticalEntropy.EventualAffinity

/-! The categorical product experiment: masses, exponential moments, the
log-moment `Λ x u = ∑ i, log E_x exp (u i (z i))` with its curvature, and
the product formula for the Hellinger affinity. -/

noncomputable section
open MeasureTheory Set
namespace ThresholdHC.AffineComparison
open ThresholdHC.CriticalEntropy

theorem categoricalLaw_apply {I : Type} [Fintype I] [MeasurableSpace I]
    (q : I → ℝ) (s : Set I) (hs : MeasurableSet s) :
    categoricalLaw q s = ∑ a, ENNReal.ofReal (q a)*s.indicator 1 a := by
  simp only [categoricalLaw,Measure.coe_finsetSum,Finset.sum_apply,Measure.smul_apply,
    smul_eq_mul,Measure.dirac_apply' _ hs]

theorem categoricalLaw_singleton {I : Type} [Fintype I] [MeasurableSpace I]
    [MeasurableSingletonClass I] (q : I → ℝ) (a : I) :
    categoricalLaw q {a} = ENNReal.ofReal (q a) := by
  classical
  rw [categoricalLaw_apply q {a} (measurableSet_singleton a),Finset.sum_eq_single a]
  · simp
  · intro b _ hb
    simp [hb]
  · simp

theorem categoricalLaw_univ {I : Type} [Fintype I] [MeasurableSpace I] (q : I → ℝ) :
    categoricalLaw q univ = ∑ a, ENNReal.ofReal (q a) := by
  rw [categoricalLaw_apply q univ MeasurableSet.univ]
  simp

instance categoricalLaw_isFiniteMeasure {I : Type} [Fintype I] [MeasurableSpace I]
    (q : I → ℝ) : IsFiniteMeasure (categoricalLaw q) :=
  ⟨by
    rw [categoricalLaw_univ]
    exact ENNReal.sum_lt_top.mpr (fun a _ => ENNReal.ofReal_lt_top)⟩

instance categoricalProductLaw_isFiniteMeasure {k : ℕ} {I : Fin k → Type}
    [∀ i, Fintype (I i)] [∀ i, MeasurableSpace (I i)] (q : ∀ i, I i → ℝ) :
    IsFiniteMeasure (categoricalProductLaw q) := by
  unfold categoricalProductLaw
  infer_instance

theorem categoricalLaw_isProbabilityMeasure {I : Type} [Fintype I] [MeasurableSpace I]
    (q : I → ℝ) (hq : ∀ a, 0 ≤ q a) (hs : ∑ a, q a = 1) :
    IsProbabilityMeasure (categoricalLaw q) :=
  ⟨by rw [categoricalLaw_univ,← ENNReal.ofReal_sum_of_nonneg (fun a _ => hq a),hs,
    ENNReal.ofReal_one]⟩

theorem categoricalProductLaw_isProbabilityMeasure {k : ℕ} {I : Fin k → Type}
    [∀ i, Fintype (I i)] [∀ i, MeasurableSpace (I i)] (q : ∀ i, I i → ℝ)
    (hq : ∀ i a, 0 ≤ q i a) (hs : ∀ i, ∑ a, q i a = 1) :
    IsProbabilityMeasure (categoricalProductLaw q) := by
  have : ∀ i, IsProbabilityMeasure (categoricalLaw (q i)) :=
    fun i => categoricalLaw_isProbabilityMeasure (q i) (hq i) (hs i)
  unfold categoricalProductLaw
  infer_instance

theorem categoricalLaw_real_singleton {I : Type} [Fintype I] [MeasurableSpace I]
    [MeasurableSingletonClass I] (q : I → ℝ) (a : I) (hq : 0 ≤ q a) :
    (categoricalLaw q).real {a} = q a := by
  rw [measureReal_def,categoricalLaw_singleton,ENNReal.toReal_ofReal hq]

theorem categoricalProductLaw_real_singleton {k : ℕ} {I : Fin k → Type}
    [∀ i, Fintype (I i)] [∀ i, MeasurableSpace (I i)] [∀ i, MeasurableSingletonClass (I i)]
    (q : ∀ i, I i → ℝ) (hq : ∀ i a, 0 ≤ q i a) (z : ∀ i, I i) :
    (categoricalProductLaw q).real {z} = ∏ i, q i (z i) := by
  rw [measureReal_def,categoricalProductLaw,Measure.pi_singleton,ENNReal.toReal_prod]
  apply Finset.prod_congr rfl
  intro i _
  rw [categoricalLaw_singleton,ENNReal.toReal_ofReal (hq i (z i))]

/-- The product affinity factorizes over the coordinates. -/
theorem categoricalProductLaw_affinity {k : ℕ} {I : Fin k → Type}
    [∀ i, Fintype (I i)] [∀ i, MeasurableSpace (I i)] [∀ i, MeasurableSingletonClass (I i)]
    (q q' : ∀ i, I i → ℝ) (hq : ∀ i a, 0 ≤ q i a) (hq' : ∀ i a, 0 ≤ q' i a) :
    (hellingerAffinity (categoricalProductLaw q) (categoricalProductLaw q')).toReal =
      ∏ i, realFiniteAffinity (q i) (q' i) := by
  rw [hellingerAffinity_finite_real]
  unfold realFiniteAffinity
  simp_rw [categoricalProductLaw_real_singleton q hq,categoricalProductLaw_real_singleton q' hq']
  rw [Finset.prod_univ_sum,Fintype.piFinset_univ]
  apply Finset.sum_congr rfl
  intro z _
  rw [← Finset.prod_mul_distrib,Real.sqrt_prod _ (fun i _ => mul_nonneg (hq i _) (hq' i _))]

/-- The log-moment of an additive score: `Λ x u = ∑ i, log ∑ a, p i x a exp (u i a)`. -/
def categoricalLogMoment {E : Type} {k : ℕ} {I : Fin k → Type} [∀ i, Fintype (I i)]
    (p : ∀ i, E → I i → ℝ) (x : E) (u : ∀ i, I i → ℝ) : ℝ :=
  ∑ i, Real.log (finitePartition (p i x) (u i))

/-- Exponential moments of additive scores under the product law. -/
theorem categorical_exp_integral {k : ℕ} {I : Fin k → Type}
    [∀ i, Fintype (I i)] [∀ i, MeasurableSpace (I i)] [∀ i, MeasurableSingletonClass (I i)]
    [∀ i, Nonempty (I i)]
    (q : ∀ i, I i → ℝ) (hq : ∀ i a, 0 < q i a) (b : ℝ) (w : ∀ i, I i → ℝ) :
    (∫ z, Real.exp (b+∑ i, w i (z i)) ∂(categoricalProductLaw q)) =
      Real.exp (b+∑ i, Real.log (finitePartition (q i) (w i))) := by
  have he : (fun z : ∀ i, I i => Real.exp (b+∑ i, w i (z i))) =
      (fun z => Real.exp b*∏ i, Real.exp (w i (z i))) := by
    funext z
    rw [Real.exp_add,Real.exp_sum]
  rw [he,integral_const_mul,categoricalProductLaw,
    integral_fintype_prod_eq_prod (fun i t => Real.exp (w i t)),Real.exp_add]
  congr 1
  rw [Real.exp_sum]
  apply Finset.prod_congr rfl
  intro i _
  rw [finite_integral_exp,Real.exp_log (finitePartition_pos _ _ (hq i))]
  congr 1
  funext a
  exact categoricalLaw_real_singleton (q i) a (hq i a).le

section Curvature

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {k : ℕ} {I : Fin k → Type} [∀ i, Fintype (I i)] [∀ i, Nonempty (I i)]

theorem categoricalLogMoment_parameter_continuousOn (X : Set E)
    (p : ∀ i, E →ᵃ[ℝ] (I i → ℝ)) (hpc : ∀ i, Continuous (p i))
    (hp : ∀ x ∈ X, ∀ i a, 0 < p i x a) (u : ∀ i, I i → ℝ) :
    ContinuousOn (fun x => categoricalLogMoment (fun i => p i) x u) X := by
  unfold categoricalLogMoment
  apply continuousOn_finsetSum
  intro i _
  exact (finitePartition_continuous.comp ((hpc i).prodMk continuous_const)).continuousOn.log
    (fun x hx => (finitePartition_pos _ _ (hp x hx i)).ne')

theorem categoricalLogMoment_parameter_concaveOn (X : Set E) (hXv : Convex ℝ X)
    (p : ∀ i, E →ᵃ[ℝ] (I i → ℝ))
    (hp : ∀ x ∈ X, ∀ i a, 0 < p i x a) (u : ∀ i, I i → ℝ) :
    ConcaveOn ℝ X (fun x => categoricalLogMoment (fun i => p i) x u) := by
  unfold categoricalLogMoment
  apply concaveOn_finset_sum hXv
  intro i _
  exact ((finiteLogPartition_population_concave (u i)).comp_affineMap (p i)).subset
    (fun x hx => hp x hx i) hXv

theorem categoricalLogMoment_score_continuous
    (p : ∀ i, E →ᵃ[ℝ] (I i → ℝ)) (x : E) (hx : ∀ i a, 0 < p i x a) :
    Continuous (categoricalLogMoment (fun i => p i) x) := by
  unfold categoricalLogMoment
  apply continuous_finsetSum
  intro i _
  exact (finitePartition_continuous.comp (continuous_const.prodMk (continuous_apply i))).log
    (fun u => (finitePartition_pos _ _ (hx i)).ne')

theorem categoricalLogMoment_score_convexOn
    (p : ∀ i, E →ᵃ[ℝ] (I i → ℝ)) (x : E) (hx : ∀ i a, 0 < p i x a) :
    ConvexOn ℝ univ (categoricalLogMoment (fun i => p i) x) := by
  unfold categoricalLogMoment
  apply convexOn_finset_sum convex_univ
  intro i _
  have h := (finiteLogPartition_convex (p i x) (hx i)).comp_linearMap
    (LinearMap.proj (R := ℝ) (φ := fun i => I i → ℝ) i)
  rw [preimage_univ] at h
  exact h

theorem categoricalLogMoment_diagonal
    (p : ∀ i, E →ᵃ[ℝ] (I i → ℝ)) (x : E) (hx : ∀ i a, 0 < p i x a)
    (hs : ∀ i, ∑ a, p i x a = 1) (w : ∀ i, I i → ℝ) :
    0 ≤ categoricalLogMoment (fun i => p i) x w+categoricalLogMoment (fun i => p i) x (-w) := by
  unfold categoricalLogMoment
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_nonneg
  intro i _
  have hl := finite_log_partition_lower (p i x) (p i x) (w i) (hx i) (hx i)
  rw [realFiniteAffinity_self (p i x) (fun a => (hx i a).le) (hs i),Real.log_one,
    mul_zero] at hl
  change 0 ≤ Real.log (finitePartition (p i x) (w i))+
    Real.log (finitePartition (p i x) (-(w i)))
  linarith

theorem categoricalLogMoment_attained
    (p : ∀ i, E →ᵃ[ℝ] (I i → ℝ)) (x y : E)
    (hx : ∀ i a, 0 < p i x a) (hy : ∀ i a, 0 < p i y a) :
    ∃ v : ∀ i, I i → ℝ,
      categoricalLogMoment (fun i => p i) x (-v)+categoricalLogMoment (fun i => p i) y v =
        2*Real.log (∏ i, realFiniteAffinity (p i x) (p i y)) := by
  choose v hv using fun i => finite_log_partition_attained (p i x) (p i y) (hx i) (hy i)
  refine ⟨v,?_⟩
  unfold categoricalLogMoment
  rw [← Finset.sum_add_distrib,
    Real.log_prod (fun i _ => (realFiniteAffinity_pos _ _ (hx i) (hy i)).ne'),Finset.mul_sum]
  exact Finset.sum_congr rfl (fun i _ => hv i)

end Curvature

end ThresholdHC.AffineComparison
