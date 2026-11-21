import ThresholdHC.CriticalEntropy.FiniteRiskAnalytic

/-! An abstract uniform saddle and its centering, for a log-moment `Λ x u`
that is concave in the parameter `x` and convex in the score `u`. This is the
argument of `finite_repeated_uniform_saddle` and `finite_saddle_centering`
with the repeated categorical log-partition replaced by an arbitrary `Λ`. -/

noncomputable section
open Set
namespace ThresholdHC.AffineComparison
open ThresholdHC.CriticalEntropy

/-- The two-point objective `ell x - ell y + a (Λ x (-u/a) + Λ y (u/a) + 2 log 2)`. -/
def pairObjective {E F : Type*} [AddCommGroup F] [Module ℝ F]
    (Λ : E → F → ℝ) (ell : E → ℝ) (x y : E) (u : F) (a : ℝ) : ℝ :=
  ell x-ell y+a*(Λ x (-(a⁻¹ • u))+Λ y (a⁻¹ • u)+2*Real.log 2)

theorem perspective_convexOn {F : Type*} [AddCommGroup F] [Module ℝ F]
    (f : F → ℝ) (hf : ConvexOn ℝ univ f) :
    ConvexOn ℝ {z : F × ℝ | 0 < z.2} (fun z => z.2*f (z.2⁻¹ • z.1)) := by
  refine ⟨(convex_Ioi (0 : ℝ)).linear_preimage (LinearMap.snd ℝ F ℝ),?_⟩
  intro x hx y hy a b ha hb hab
  have hx' : 0 < x.2 := hx
  have hy' : 0 < y.2 := hy
  have hc : 0 < a*x.2+b*y.2 := by
    rcases eq_or_lt_of_le ha with rfl | ha'
    · have hb' : b = 1 := by linarith
      simp [hb',hy']
    · exact add_pos_of_pos_of_nonneg (mul_pos ha' hx') (mul_nonneg hb hy'.le)
  have hsum : a*x.2/(a*x.2+b*y.2)+b*y.2/(a*x.2+b*y.2) = 1 := by
    rw [← add_div]
    exact div_self hc.ne'
  have h := hf.2 (x := x.2⁻¹ • x.1) (y := y.2⁻¹ • y.1)
    (mem_univ _) (mem_univ _) (div_nonneg (mul_nonneg ha hx'.le) hc.le)
    (div_nonneg (mul_nonneg hb hy'.le) hc.le) hsum
  have he : (a*x.2/(a*x.2+b*y.2)) • (x.2⁻¹ • x.1)+(b*y.2/(a*x.2+b*y.2)) • (y.2⁻¹ • y.1) =
      (a*x.2+b*y.2)⁻¹ • (a • x.1+b • y.1) := by
    rw [smul_smul,smul_smul,smul_add,smul_smul,smul_smul]
    congr 2
    · field_simp
    · field_simp
  rw [he] at h
  have hh := mul_le_mul_of_nonneg_left h hc.le
  simp only [Prod.fst_add,Prod.snd_add,Prod.smul_fst,Prod.smul_snd,smul_eq_mul]
  calc
    _ ≤ (a*x.2+b*y.2)*((a*x.2/(a*x.2+b*y.2))*f (x.2⁻¹ • x.1)+
        (b*y.2/(a*x.2+b*y.2))*f (y.2⁻¹ • y.1)) := by simpa only [smul_eq_mul] using hh
    _ = _ := by field_simp

theorem concaveOn_finset_sum {E ι : Type*} [AddCommGroup E] [Module ℝ E]
    {s : Set E} (hs : Convex ℝ s) (t : Finset ι) (f : ι → E → ℝ)
    (h : ∀ i ∈ t, ConcaveOn ℝ s (f i)) :
    ConcaveOn ℝ s (fun x => ∑ i ∈ t, f i x) := by
  refine ⟨hs,?_⟩
  intro x hx y hy a b ha hb hab
  simp only [smul_eq_mul,Finset.mul_sum,← Finset.sum_add_distrib]
  exact Finset.sum_le_sum (fun i hi => (h i hi).2 hx hy ha hb hab)

theorem convexOn_finset_sum {E ι : Type*} [AddCommGroup E] [Module ℝ E]
    {s : Set E} (hs : Convex ℝ s) (t : Finset ι) (f : ι → E → ℝ)
    (h : ∀ i ∈ t, ConvexOn ℝ s (f i)) :
    ConvexOn ℝ s (fun x => ∑ i ∈ t, f i x) := by
  refine ⟨hs,?_⟩
  intro x hx y hy a b ha hb hab
  simp only [smul_eq_mul,Finset.mul_sum,← Finset.sum_add_distrib]
  exact Finset.sum_le_sum (fun i hi => (h i hi).2 hx hy ha hb hab)

theorem pairObjective_pointwise {E F : Type*} [AddCommGroup F] [Module ℝ F]
    (Λ : E → F → ℝ) (ell : E → ℝ) (x y : E) (t : ℝ) (v : F)
    (hv : 0 ≤ Λ x (-v)+Λ y v+2*Real.log 2 → ell x-ell y < t) :
    ∃ (u : F) (a : ℝ), 0 < a ∧ pairObjective Λ ell x y u a < t := by
  obtain ⟨a,ha,hat⟩ := exists_positive_scale_lt (ell x-ell y) _ t hv
  refine ⟨a • v,a,ha,?_⟩
  have hs : a⁻¹ • (a • v) = v := by rw [smul_smul,inv_mul_cancel₀ ha.ne',one_smul]
  unfold pairObjective
  rw [hs]
  exact hat

theorem pairObjective_parameter_geometry {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [AddCommGroup F] [Module ℝ F]
    (X : Set E) (hXv : Convex ℝ X) (Λ : E → F → ℝ) (ell : E →ᵃ[ℝ] ℝ)
    (helc : Continuous ell)
    (hxc : ∀ u, ContinuousOn (fun x => Λ x u) X)
    (hxv : ∀ u, ConcaveOn ℝ X (fun x => Λ x u))
    (u : F) (a : ℝ) (ha : 0 < a) :
    ContinuousOn (fun z : E × E => pairObjective Λ ell z.1 z.2 u a) (X ×ˢ X) ∧
    ConcaveOn ℝ (X ×ˢ X) (fun z : E × E => pairObjective Λ ell z.1 z.2 u a) := by
  have h1c : ContinuousOn (fun z : E × E => Λ z.1 (-(a⁻¹ • u))) (X ×ˢ X) :=
    (hxc (-(a⁻¹ • u))).comp continuousOn_fst (fun z hz => hz.1)
  have h2c : ContinuousOn (fun z : E × E => Λ z.2 (a⁻¹ • u)) (X ×ˢ X) :=
    (hxc (a⁻¹ • u)).comp continuousOn_snd (fun z hz => hz.2)
  constructor
  · exact ((helc.comp continuous_fst).sub (helc.comp continuous_snd)).continuousOn.add
      (((h1c.add h2c).add continuousOn_const).const_smul a)
  · let d := ell.comp (LinearMap.fst ℝ E E).toAffineMap -
      ell.comp (LinearMap.snd ℝ E E).toAffineMap
    have h1 : ConcaveOn ℝ (X ×ˢ X) (fun z : E × E => Λ z.1 (-(a⁻¹ • u))) :=
      ((hxv (-(a⁻¹ • u))).comp_linearMap (LinearMap.fst ℝ E E)).subset
        (fun z hz => hz.1) (hXv.prod hXv)
    have h2 : ConcaveOn ℝ (X ×ˢ X) (fun z : E × E => Λ z.2 (a⁻¹ • u)) :=
      ((hxv (a⁻¹ • u)).comp_linearMap (LinearMap.snd ℝ E E)).subset
        (fun z hz => hz.2) (hXv.prod hXv)
    have hd : ConcaveOn ℝ (X ×ˢ X) (fun z : E × E => ell z.1-ell z.2) :=
      ((concaveOn_id (𝕜 := ℝ) (convex_univ : Convex ℝ (univ : Set ℝ))).comp_affineMap d).subset
        (fun _ _ => mem_univ _) (hXv.prod hXv)
    exact hd.add (ConcaveOn.smul ha.le ((h1.add h2).add_const (2*Real.log 2)))

theorem pairObjective_score_continuous {E F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (Λ : E → F → ℝ) (ell : E → ℝ) (x y : E)
    (hx : Continuous (Λ x)) (hy : Continuous (Λ y)) :
    ContinuousOn (fun z : F × ℝ => pairObjective Λ ell x y z.1 z.2) {z | 0 < z.2} := by
  have hs : ContinuousOn (fun z : F × ℝ => z.2⁻¹ • z.1) {z | 0 < z.2} :=
    (continuous_snd.continuousOn.inv₀ (fun z hz => (ne_of_gt hz))).smul
      continuous_fst.continuousOn
  have hm : ContinuousOn (fun z : F × ℝ => Λ x (-(z.2⁻¹ • z.1))) {z | 0 < z.2} :=
    hx.comp_continuousOn hs.neg
  have hp : ContinuousOn (fun z : F × ℝ => Λ y (z.2⁻¹ • z.1)) {z | 0 < z.2} :=
    hy.comp_continuousOn hs
  exact continuousOn_const.add (continuous_snd.continuousOn.mul
    ((hm.add hp).add continuousOn_const))

theorem pairObjective_score_convex {E F : Type*} [AddCommGroup F] [Module ℝ F]
    (Λ : E → F → ℝ) (ell : E → ℝ) (x y : E)
    (hx : ConvexOn ℝ univ (Λ x)) (hy : ConvexOn ℝ univ (Λ y)) :
    ConvexOn ℝ {z : F × ℝ | 0 < z.2} (fun z => pairObjective Λ ell x y z.1 z.2) := by
  have hxn : ConvexOn ℝ univ (fun w => Λ x (-w)) := by
    have h := hx.comp_linearMap (-LinearMap.id)
    rw [preimage_univ] at h
    exact h
  have hneg := perspective_convexOn (fun w => Λ x (-w)) hxn
  have hpos := perspective_convexOn (Λ y) hy
  have hlin : ConvexOn ℝ {z : F × ℝ | 0 < z.2} (fun z => ell x-ell y+2*Real.log 2*z.2) := by
    refine ⟨hpos.1,?_⟩
    intro p hp q hq a b ha hb hab
    simp only [Prod.snd_add,Prod.smul_snd,smul_eq_mul]
    nlinarith [congrArg (fun t : ℝ => t*(ell x-ell y)) hab]
  have he : (fun z : F × ℝ => pairObjective Λ ell x y z.1 z.2) =
      (fun z => z.2*Λ x (-(z.2⁻¹ • z.1))) + (fun z => z.2*Λ y (z.2⁻¹ • z.1)) +
        (fun z => ell x-ell y+2*Real.log 2*z.2) := by
    funext z
    simp only [pairObjective,Pi.add_apply]
    ring
  rw [he]
  exact (hneg.add hpos).add hlin

/-- Sion's theorem turns pointwise certificates into one uniform certificate. -/
theorem abstract_uniform_saddle {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (X : Set E) (hXn : X.Nonempty) (hXc : IsCompact X) (hXv : Convex ℝ X)
    (Λ : E → F → ℝ) (ell : E →ᵃ[ℝ] ℝ) (helc : Continuous ell)
    (hxc : ∀ u, ContinuousOn (fun x => Λ x u) X)
    (hxv : ∀ u, ConcaveOn ℝ X (fun x => Λ x u))
    (huc : ∀ x ∈ X, Continuous (Λ x))
    (huv : ∀ x ∈ X, ConvexOn ℝ univ (Λ x))
    (t : ℝ)
    (hpt : ∀ x ∈ X, ∀ y ∈ X, ∃ v : F,
      0 ≤ Λ x (-v)+Λ y v+2*Real.log 2 → ell x-ell y < t) :
    ∃ (u : F) (a : ℝ), 0 < a ∧ ∀ x ∈ X, ∀ y ∈ X, pairObjective Λ ell x y u a < t := by
  obtain ⟨z,hz,hu⟩ := convex_concave_uniform_strict (X ×ˢ X)
    {z : F × ℝ | 0 < z.2} (hXn.prod hXn) (hXc.prod hXc) (hXv.prod hXv)
    ((convex_Ioi (0 : ℝ)).linear_preimage (LinearMap.snd ℝ F ℝ))
    (fun xy z => pairObjective Λ ell xy.1 xy.2 z.1 z.2)
    (fun z hz => (pairObjective_parameter_geometry X hXv Λ ell helc hxc hxv z.1 z.2 hz).1)
    (fun z hz => (pairObjective_parameter_geometry X hXv Λ ell helc hxc hxv z.1 z.2 hz).2)
    (fun xy hxy => pairObjective_score_continuous Λ ell xy.1 xy.2
      (huc xy.1 hxy.1) (huc xy.2 hxy.2))
    (fun xy hxy => pairObjective_score_convex Λ ell xy.1 xy.2
      (huv xy.1 hxy.1) (huv xy.2 hxy.2)) t
    (by
      intro xy hxy
      obtain ⟨v,hv⟩ := hpt xy.1 hxy.1 xy.2 hxy.2
      obtain ⟨u,a,ha,hu⟩ := pairObjective_pointwise Λ ell xy.1 xy.2 t v hv
      exact ⟨(u,a),ha,hu⟩)
  exact ⟨z.1,z.2,hz,fun x hx y hy => hu (x,y) ⟨hx,hy⟩⟩

/-- Center a uniform certificate using attained maxima on the compact set. -/
theorem abstract_saddle_centering {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [AddCommGroup F] [Module ℝ F]
    (X : Set E) (hXn : X.Nonempty) (hXc : IsCompact X)
    (Λ : E → F → ℝ) (ell : E →ᵃ[ℝ] ℝ) (helc : Continuous ell)
    (hxc : ∀ u, ContinuousOn (fun x => Λ x u) X)
    (hdiag : ∀ x ∈ X, ∀ w, 0 ≤ Λ x w+Λ x (-w))
    (R : ℝ) (u : F) (a : ℝ) (ha : 0 < a)
    (hcert : ∀ x ∈ X, ∀ y ∈ X, pairObjective Λ ell x y u a < 2*R) :
    a ≤ R/Real.log 2 ∧ ∃ c : ℝ, ∀ x ∈ X,
      (c-ell x)/a+Λ x (a⁻¹ • u) ≤ R/a-Real.log 2 ∧
      (ell x-c)/a+Λ x (-(a⁻¹ • u)) ≤ R/a-Real.log 2 := by
  obtain ⟨x₀,hx₀⟩ := hXn
  have hd0 := hdiag x₀ hx₀ (a⁻¹ • u)
  have hc0 := hcert x₀ hx₀ x₀ hx₀
  unfold pairObjective at hc0
  rw [sub_self,zero_add] at hc0
  have has : a*Real.log 2 < R := by nlinarith
  refine ⟨(le_div_iff₀ (Real.log_pos (by norm_num : (1 : ℝ) < 2))).mpr has.le,?_⟩
  let U : E → ℝ := fun x => ell x+a*Λ x (-(a⁻¹ • u))
  let V : E → ℝ := fun x => -ell x+a*Λ x (a⁻¹ • u)
  have hUc : ContinuousOn U X :=
    helc.continuousOn.add ((hxc (-(a⁻¹ • u))).const_smul a)
  have hVc : ContinuousOn V X :=
    helc.neg.continuousOn.add ((hxc (a⁻¹ • u)).const_smul a)
  obtain ⟨xU,hxU,hU⟩ := hXc.exists_isMaxOn ⟨x₀,hx₀⟩ hUc
  obtain ⟨xV,hxV,hV⟩ := hXc.exists_isMaxOn ⟨x₀,hx₀⟩ hVc
  have huv : U xU+V xV+2*a*Real.log 2 < 2*R := by
    have h := hcert xU hxU xV hxV
    unfold pairObjective at h
    dsimp only [U,V]
    nlinarith
  let c := (U xU-V xV)/2
  refine ⟨c,?_⟩
  intro x hx
  have hu : U x ≤ U xU := hU hx
  have hv : V x ≤ V xV := hV hx
  have hrawP : c-ell x+a*Λ x (a⁻¹ • u) ≤ R-a*Real.log 2 := by
    dsimp only [V,c] at hv ⊢
    linarith
  have hrawM : ell x-c+a*Λ x (-(a⁻¹ • u)) ≤ R-a*Real.log 2 := by
    dsimp only [U,c] at hu ⊢
    linarith
  constructor
  · calc
      _ = (c-ell x+a*Λ x (a⁻¹ • u))/a := by field_simp
      _ ≤ (R-a*Real.log 2)/a := div_le_div_of_nonneg_right hrawP ha.le
      _ = _ := by field_simp
  · calc
      _ = (ell x-c+a*Λ x (-(a⁻¹ • u)))/a := by field_simp
      _ ≤ (R-a*Real.log 2)/a := div_le_div_of_nonneg_right hrawM ha.le
      _ = _ := by field_simp

/-- The abstract additive certificate: one score `u`, one scale `a` and one
centering constant `c` with both uniform exponential-moment bounds. -/
theorem abstract_additive_certificate {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (X : Set E) (hXn : X.Nonempty) (hXc : IsCompact X) (hXv : Convex ℝ X)
    (Λ : E → F → ℝ) (ell : E →ᵃ[ℝ] ℝ) (helc : Continuous ell)
    (hxc : ∀ u, ContinuousOn (fun x => Λ x u) X)
    (hxv : ∀ u, ConcaveOn ℝ X (fun x => Λ x u))
    (huc : ∀ x ∈ X, Continuous (Λ x))
    (huv : ∀ x ∈ X, ConvexOn ℝ univ (Λ x))
    (hdiag : ∀ x ∈ X, ∀ w, 0 ≤ Λ x w+Λ x (-w))
    (R : ℝ)
    (hpt : ∀ x ∈ X, ∀ y ∈ X, ∃ v : F,
      0 ≤ Λ x (-v)+Λ y v+2*Real.log 2 → ell x-ell y < 2*R) :
    ∃ (u : F) (a c : ℝ), 0 < a ∧ a ≤ R/Real.log 2 ∧ ∀ x ∈ X,
      (c-ell x)/a+Λ x (a⁻¹ • u) ≤ R/a-Real.log 2 ∧
      (ell x-c)/a+Λ x (-(a⁻¹ • u)) ≤ R/a-Real.log 2 := by
  obtain ⟨u,a,ha,hcert⟩ := abstract_uniform_saddle X hXn hXc hXv Λ ell helc
    hxc hxv huc huv (2*R) hpt
  obtain ⟨haR,c,hc⟩ := abstract_saddle_centering X hXn hXc Λ ell helc hxc hdiag R u a ha hcert
  exact ⟨u,a,c,ha,haR,hc⟩

end ThresholdHC.AffineComparison
