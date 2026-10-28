import ThresholdHC.CriticalEntropy.FiniteRiskAnalytic

noncomputable section
open Set
namespace ThresholdHC.CriticalEntropy

theorem finiteRepeatedObjective_population_geometry {E I : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [Fintype I] [Nonempty I]
    (X : Set E) (hX : Convex ℝ X) (p : E →ᵃ[ℝ] (I → ℝ)) (ell : E →ᵃ[ℝ] ℝ)
    (hpc : Continuous p) (helc : Continuous ell) (hp : ∀ x ∈ X, ∀ i, 0 < p x i)
    (n : ℕ) (u : I → ℝ) (a : ℝ) (ha : 0 < a) :
    ContinuousOn (fun z : E × E => finiteRepeatedObjective (p z.1) (p z.2)
      (ell z.1-ell z.2) n u a) (X ×ˢ X) ∧
    ConcaveOn ℝ (X ×ˢ X) (fun z : E × E => finiteRepeatedObjective (p z.1) (p z.2)
      (ell z.1-ell z.2) n u a) := by
  have h1c : Continuous (fun z : E × E => finitePartition (p z.1) (fun i => -u i/a)) :=
    finitePartition_continuous.comp ((hpc.comp continuous_fst).prodMk continuous_const)
  have h2c : Continuous (fun z : E × E => finitePartition (p z.2) (fun i => u i/a)) :=
    finitePartition_continuous.comp ((hpc.comp continuous_snd).prodMk continuous_const)
  have h1l : ContinuousOn (fun z : E × E =>
      Real.log (finitePartition (p z.1) (fun i => -u i/a))) (X ×ˢ X) :=
    h1c.continuousOn.log (fun z hz =>
    (finitePartition_pos (p z.1) _ (hp z.1 hz.1)).ne')
  have h2l : ContinuousOn (fun z : E × E =>
      Real.log (finitePartition (p z.2) (fun i => u i/a))) (X ×ˢ X) :=
    h2c.continuousOn.log (fun z hz =>
    (finitePartition_pos (p z.2) _ (hp z.2 hz.2)).ne')
  constructor
  · exact ((helc.comp continuous_fst).sub (helc.comp continuous_snd)).continuousOn.add
      (((h1l.const_mul (n : ℝ)).add (h2l.const_mul (n : ℝ))).add_const
        (2*Real.log 2) |>.const_mul a)
  · let p1 := p.comp (LinearMap.fst ℝ E E).toAffineMap
    let p2 := p.comp (LinearMap.snd ℝ E E).toAffineMap
    let d := ell.comp (LinearMap.fst ℝ E E).toAffineMap -
      ell.comp (LinearMap.snd ℝ E E).toAffineMap
    have h1 : ConcaveOn ℝ (X ×ˢ X)
        (fun z : E × E => Real.log (finitePartition (p z.1) (fun i => -u i/a))) :=
      ((finiteLogPartition_population_concave (fun i => -u i/a)).comp_affineMap p1).subset
        (fun z hz => hp z.1 hz.1) (hX.prod hX)
    have h2 : ConcaveOn ℝ (X ×ˢ X)
        (fun z : E × E => Real.log (finitePartition (p z.2) (fun i => u i/a))) :=
      ((finiteLogPartition_population_concave (fun i => u i/a)).comp_affineMap p2).subset
        (fun z hz => hp z.2 hz.2) (hX.prod hX)
    have hd : ConcaveOn ℝ (X ×ˢ X) (fun z : E × E => ell z.1-ell z.2) :=
      ((concaveOn_id (𝕜 := ℝ) (convex_univ : Convex ℝ (univ : Set ℝ))).comp_affineMap d).subset
        (fun _ _ => mem_univ _) (hX.prod hX)
    exact hd.add (ConcaveOn.smul ha.le (((ConcaveOn.smul (Nat.cast_nonneg n) h1).add
      (ConcaveOn.smul (Nat.cast_nonneg n) h2)).add_const (2*Real.log 2)))

theorem finiteRepeatedObjective_score_continuous {I : Type} [Fintype I] [Nonempty I]
    (p q : I → ℝ) (hp : ∀ i, 0 < p i) (hq : ∀ i, 0 < q i) (d : ℝ) (n : ℕ) :
    ContinuousOn (fun z : (I → ℝ) × ℝ => finiteRepeatedObjective p q d n z.1 z.2)
      {z | 0 < z.2} := by
  have hplus : ContinuousOn (fun z : (I → ℝ) × ℝ => fun i => z.1 i/z.2) {z | 0 < z.2} := by
    apply continuousOn_pi.mpr
    intro i
    exact ((continuous_apply i).comp continuous_fst).continuousOn.div continuous_snd.continuousOn
      (fun z hz => hz.ne')
  have hminus : ContinuousOn (fun z : (I → ℝ) × ℝ => fun i => -z.1 i/z.2) {z | 0 < z.2} := by
    apply continuousOn_pi.mpr
    intro i
    exact ((continuous_apply i).comp continuous_fst).neg.continuousOn.div continuous_snd.continuousOn
      (fun z hz => hz.ne')
  have hm := (finitePartition_continuous.comp_continuousOn
    (continuousOn_const.prodMk hminus)).log (fun z hz => (finitePartition_pos p _ hp).ne')
  have hp' := (finitePartition_continuous.comp_continuousOn
    (continuousOn_const.prodMk hplus)).log (fun z hz => (finitePartition_pos q _ hq).ne')
  exact continuousOn_const.add (continuous_snd.continuousOn.mul
    (((hm.const_mul (n : ℝ)).add (hp'.const_mul (n : ℝ))).add_const (2*Real.log 2)))

/-- Affinity controls a single score and positive scale uniformly over the
compact convex finite experiment. Its curvature assumptions are derived. -/
theorem finite_repeated_uniform_saddle {E I : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [Fintype I] [Nonempty I]
    (X : Set E) (hXn : X.Nonempty) (hXc : IsCompact X) (hXv : Convex ℝ X)
    (p : E →ᵃ[ℝ] (I → ℝ)) (ell : E →ᵃ[ℝ] ℝ)
    (hpc : Continuous p) (helc : Continuous ell) (hp : ∀ x ∈ X, ∀ i, 0 < p x i)
    (n : ℕ) (t : ℝ)
    (hsep : ∀ x ∈ X, ∀ y ∈ X, 1/2 ≤ (realFiniteAffinity (p x) (p y))^n → ell x-ell y < t) :
    ∃ (u : I → ℝ) (a : ℝ), 0 < a ∧ ∀ x ∈ X, ∀ y ∈ X,
      finiteRepeatedObjective (p x) (p y) (ell x-ell y) n u a < t := by
  obtain ⟨z,hz,hu⟩ := convex_concave_uniform_strict (X ×ˢ X)
    {z : (I → ℝ) × ℝ | 0 < z.2} (hXn.prod hXn) (hXc.prod hXc) (hXv.prod hXv)
    ((convex_Ioi (0 : ℝ)).linear_preimage (LinearMap.snd ℝ (I → ℝ) ℝ))
    (fun xy z => finiteRepeatedObjective (p xy.1) (p xy.2) (ell xy.1-ell xy.2) n z.1 z.2)
    (fun z hz => (finiteRepeatedObjective_population_geometry X hXv p ell hpc helc hp n z.1 z.2 hz).1)
    (fun z hz => (finiteRepeatedObjective_population_geometry X hXv p ell hpc helc hp n z.1 z.2 hz).2)
    (fun xy hxy => finiteRepeatedObjective_score_continuous _ _ (hp xy.1 hxy.1) (hp xy.2 hxy.2) _ n)
    (fun xy hxy => finiteRepeatedObjective_convex _ _ (hp xy.1 hxy.1) (hp xy.2 hxy.2) _ n) t
    (by
      intro xy hxy
      obtain ⟨u,a,ha,hu⟩ := finiteRepeatedObjective_pointwise _ _
        (hp xy.1 hxy.1) (hp xy.2 hxy.2) _ t n (hsep xy.1 hxy.1 xy.2 hxy.2)
      exact ⟨(u,a),ha,hu⟩)
  exact ⟨z.1,z.2,hz,fun x hx y hy => hu (x,y) ⟨hx,hy⟩⟩

end ThresholdHC.CriticalEntropy
