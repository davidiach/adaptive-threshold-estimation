import ThresholdHC.CriticalEntropy.FiniteGeometryModel

noncomputable section
open MeasureTheory Set
open scoped ENNReal RealInnerProductSpace Topology
namespace ThresholdHC.CriticalEntropy

theorem sqrt_product_scale (a x y : ℝ) (ha : 0 ≤ a) (hx : 0 ≤ x) :
    Real.sqrt (a*x)*Real.sqrt (a*y) = a*Real.sqrt (x*y) := by
  rw [Real.sqrt_mul ha,Real.sqrt_mul ha,Real.sqrt_mul hx]
  calc
    _ = (Real.sqrt a)^2*(Real.sqrt x*Real.sqrt y) := by ring
    _ = _ := by rw [Real.sq_sqrt ha]

theorem sqrt_product_mix (a b x y u v : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hx : 0 ≤ x) (hy : 0 ≤ y) (hu : 0 ≤ u) (hv : 0 ≤ v) :
    a*Real.sqrt (x*y)+b*Real.sqrt (u*v) ≤
      Real.sqrt ((a*x+b*u)*(a*y+b*v)) := by
  let f : Fin 2 → ℝ := ![a*x,b*u]
  let g : Fin 2 → ℝ := ![a*y,b*v]
  have hf : ∀ i, 0 ≤ f i := by intro i; fin_cases i <;> simp [f] <;> positivity
  have hg : ∀ i, 0 ≤ g i := by intro i; fin_cases i <;> simp [g] <;> positivity
  have h := Real.sum_sqrt_mul_sqrt_le Finset.univ hf hg
  simp only [Fin.sum_univ_two, f,g,Matrix.cons_val_zero,Matrix.cons_val_one] at h
  rw [sqrt_product_scale a x y ha hx,sqrt_product_scale b u v hb hu,
    ← Real.sqrt_mul (by positivity : 0 ≤ a*x+b*u)] at h
  exact h

theorem realFiniteAffinity_continuous {I : Type} [Fintype I] :
    Continuous (fun z : (I → ℝ) × (I → ℝ) => realFiniteAffinity z.1 z.2) := by
  unfold realFiniteAffinity
  fun_prop

theorem realFiniteAffinity_concave {I : Type} [Fintype I] :
    ConcaveOn ℝ {z : (I → ℝ) × (I → ℝ) | (∀ i, 0 ≤ z.1 i) ∧ (∀ i, 0 ≤ z.2 i)}
      (fun z => realFiniteAffinity z.1 z.2) := by
  constructor
  · intro x hx y hy a b ha hb hab
    constructor <;> intro i <;> simp only [Prod.fst_add,Prod.snd_add,Prod.smul_fst,Prod.smul_snd,
      Pi.add_apply,Pi.smul_apply,smul_eq_mul]
    · exact add_nonneg (mul_nonneg ha (hx.1 i)) (mul_nonneg hb (hy.1 i))
    · exact add_nonneg (mul_nonneg ha (hx.2 i)) (mul_nonneg hb (hy.2 i))
  · intro x hx y hy a b ha hb hab
    simp only [realFiniteAffinity,Prod.fst_add,Prod.snd_add,Prod.smul_fst,Prod.smul_snd,
      Pi.add_apply,Pi.smul_apply,smul_eq_mul,Finset.mul_sum,← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro i hi
    exact sqrt_product_mix a b _ _ _ _ ha hb (hx.1 i) (hx.2 i) (hy.1 i) (hy.2 i)

theorem realFiniteAffinity_le_one {I : Type} [Fintype I] (p q : I → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hq : ∀ i, 0 ≤ q i) (hsp : ∑ i, p i = 1) (hsq : ∑ i, q i = 1) :
    realFiniteAffinity p q ≤ 1 := by
  calc
    _ = ∑ i, Real.sqrt (p i)*Real.sqrt (q i) := by
      apply Finset.sum_congr rfl
      intro i hi
      exact Real.sqrt_mul (hp i) _
    _ ≤ Real.sqrt (∑ i, p i)*Real.sqrt (∑ i, q i) :=
      Real.sum_sqrt_mul_sqrt_le Finset.univ hp hq
    _ = 1 := by rw [hsp,hsq]; norm_num

theorem realFiniteDistance_convex {I : Type} [Fintype I] :
    ConvexOn ℝ {z : (I → ℝ) × (I → ℝ) | (∀ i, 0 ≤ z.1 i) ∧ (∀ i, 0 ≤ z.2 i)}
      (fun z => 1-realFiniteAffinity z.1 z.2) := by
  refine ⟨(realFiniteAffinity_concave (I := I)).1,?_⟩
  intro x hx y hy a b ha hb hab
  have h := (realFiniteAffinity_concave (I := I)).2 hx hy ha hb hab
  simp only [smul_eq_mul] at h ⊢
  nlinarith

theorem finiteAffinity_toReal {I : Type} [Fintype I] (p q : I → ℝ≥0∞)
    (hp : ∀ i, p i ≠ ∞) (hq : ∀ i, q i ≠ ∞) :
    (finiteAffinity p q).toReal = realFiniteAffinity (fun i => (p i).toReal) (fun i => (q i).toReal) := by
  unfold finiteAffinity realFiniteAffinity
  rw [ENNReal.toReal_sum (fun i hi => ENNReal.rpow_ne_top_of_nonneg (by norm_num)
    (ENNReal.mul_ne_top (hp i) (hq i)))]
  apply Finset.sum_congr rfl
  intro i hi
  rw [← ENNReal.toReal_rpow,ENNReal.toReal_mul,Real.sqrt_eq_rpow]

end ThresholdHC.CriticalEntropy
