import ThresholdHC.CriticalEntropy.FiniteRiskModel
import ThresholdHC.CriticalEntropy.FiniteGeometry

noncomputable section
open Set
namespace ThresholdHC.CriticalEntropy

theorem finitePartition_pos {I : Type} [Fintype I] [Nonempty I]
    (p u : I → ℝ) (hp : ∀ i, 0 < p i) : 0 < finitePartition p u := by
  apply Finset.sum_pos
  · intro i hi
    exact mul_pos (hp i) (Real.exp_pos _)
  · exact Finset.univ_nonempty

theorem realFiniteAffinity_pos {I : Type} [Fintype I] [Nonempty I]
    (p q : I → ℝ) (hp : ∀ i, 0 < p i) (hq : ∀ i, 0 < q i) :
    0 < realFiniteAffinity p q := by
  apply Finset.sum_pos
  · intro i hi
    exact Real.sqrt_pos.mpr (mul_pos (hp i) (hq i))
  · exact Finset.univ_nonempty

theorem affinity_le_tilted_partition {I : Type} [Fintype I]
    (p q u : I → ℝ) (hp : ∀ i, 0 ≤ p i) (hq : ∀ i, 0 ≤ q i) :
    realFiniteAffinity p q ≤
      Real.sqrt (finitePartition p (-u))*Real.sqrt (finitePartition q u) := by
  have he : realFiniteAffinity p q =
      ∑ i, Real.sqrt (p i*Real.exp (-u i))*Real.sqrt (q i*Real.exp (u i)) := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [← Real.sqrt_mul (mul_nonneg (hp i) (Real.exp_nonneg _)),mul_mul_mul_comm,
      ← Real.exp_add,neg_add_cancel,Real.exp_zero,mul_one]
  rw [he]
  exact Real.sum_sqrt_mul_sqrt_le Finset.univ
    (fun i => mul_nonneg (hp i) (Real.exp_nonneg _))
    (fun i => mul_nonneg (hq i) (Real.exp_nonneg _))

theorem finite_log_partition_lower {I : Type} [Fintype I] [Nonempty I]
    (p q u : I → ℝ) (hp : ∀ i, 0 < p i) (hq : ∀ i, 0 < q i) :
    2*Real.log (realFiniteAffinity p q) ≤
      Real.log (finitePartition p (-u))+Real.log (finitePartition q u) := by
  have hpz := finitePartition_pos p (-u) hp
  have hqz := finitePartition_pos q u hq
  have h := Real.log_le_log (realFiniteAffinity_pos p q hp hq)
    (affinity_le_tilted_partition p q u (fun i => (hp i).le) (fun i => (hq i).le))
  rw [Real.log_mul (Real.sqrt_pos.mpr hpz).ne' (Real.sqrt_pos.mpr hqz).ne',
    Real.log_sqrt hpz.le,Real.log_sqrt hqz.le] at h
  linarith

theorem finite_log_partition_attained {I : Type} [Fintype I] [Nonempty I]
    (p q : I → ℝ) (hp : ∀ i, 0 < p i) (hq : ∀ i, 0 < q i) :
    ∃ u : I → ℝ, Real.log (finitePartition p (-u))+Real.log (finitePartition q u) =
      2*Real.log (realFiniteAffinity p q) := by
  let u : I → ℝ := fun i => Real.log (Real.sqrt (p i)/Real.sqrt (q i))
  have hqu (i : I) : q i*Real.exp (u i) = Real.sqrt (p i*q i) := by
    have hsqp := Real.sq_sqrt (hp i).le
    have hsqq := Real.sq_sqrt (hq i).le
    have hqp := Real.sqrt_pos.mpr (hq i)
    dsimp only [u]
    rw [Real.exp_log (div_pos (Real.sqrt_pos.mpr (hp i)) hqp),Real.sqrt_mul (hp i).le]
    field_simp [hqp.ne']
    rw [hsqq]
    ring
  have hpu (i : I) : p i*Real.exp (-u i) = Real.sqrt (p i*q i) := by
    have hsqp := Real.sq_sqrt (hp i).le
    have hpp := Real.sqrt_pos.mpr (hp i)
    have hqp := Real.sqrt_pos.mpr (hq i)
    dsimp only [u]
    rw [Real.exp_neg,Real.exp_log (div_pos hpp hqp),inv_div,Real.sqrt_mul (hp i).le]
    field_simp [hpp.ne']
    rw [hsqp]
  have heq : finitePartition q u = realFiniteAffinity p q := by
    exact Finset.sum_congr rfl (fun i hi => hqu i)
  have hep : finitePartition p (-u) = realFiniteAffinity p q := by
    exact Finset.sum_congr rfl (fun i hi => hpu i)
  refine ⟨u,?_⟩
  rw [heq,hep]
  ring

theorem finitePartition_shift {I : Type} [Fintype I]
    (p u : I → ℝ) (c : ℝ) :
    finitePartition p (fun i => u i-c) = finitePartition p u / Real.exp c := by
  simp only [finitePartition,Real.exp_sub,mul_div_assoc,Finset.sum_div]

theorem finitePartition_convex {I : Type} [Fintype I]
    (p : I → ℝ) (hp : ∀ i, 0 ≤ p i) :
    ConvexOn ℝ univ (finitePartition p) := by
  refine ⟨convex_univ,?_⟩
  intro u hu v hv a b ha hb hab
  simp only [finitePartition,Pi.add_apply,Pi.smul_apply,smul_eq_mul]
  calc
    _ ≤ ∑ i, p i*(a*Real.exp (u i)+b*Real.exp (v i)) := by
      apply Finset.sum_le_sum
      intro i hi
      exact mul_le_mul_of_nonneg_left
        (convexOn_exp.2 (mem_univ _) (mem_univ _) ha hb hab) (hp i)
    _ = _ := by
      simp only [Finset.mul_sum,← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i hi
      ring

theorem finiteLogPartition_convex {I : Type} [Fintype I] [Nonempty I]
    (p : I → ℝ) (hp : ∀ i, 0 < p i) :
    ConvexOn ℝ univ (fun u => Real.log (finitePartition p u)) := by
  refine ⟨convex_univ,?_⟩
  intro u hu v hv a b ha hb hab
  let nu : I → ℝ := fun i => u i-Real.log (finitePartition p u)
  let nv : I → ℝ := fun i => v i-Real.log (finitePartition p v)
  have hnu : finitePartition p nu = 1 := by
    rw [finitePartition_shift,Real.exp_log (finitePartition_pos p u hp)]
    exact div_self (finitePartition_pos p u hp).ne'
  have hnv : finitePartition p nv = 1 := by
    rw [finitePartition_shift,Real.exp_log (finitePartition_pos p v hp)]
    exact div_self (finitePartition_pos p v hp).ne'
  have h := (finitePartition_convex p (fun i => (hp i).le)).2
    (x := nu) (y := nv) (mem_univ _) (mem_univ _) ha hb hab
  rw [hnu,hnv] at h
  simp only [smul_eq_mul,mul_one,hab] at h
  have he : a • nu+b • nv = (fun i => (a • u+b • v) i-
      (a*Real.log (finitePartition p u)+b*Real.log (finitePartition p v))) := by
    funext i
    simp only [nu,nv,Pi.add_apply,Pi.smul_apply,smul_eq_mul]
    ring
  rw [he,finitePartition_shift] at h
  simp only [smul_eq_mul]
  apply (Real.log_le_iff_le_exp (finitePartition_pos p _ hp)).mpr
  exact (div_le_iff₀ (Real.exp_pos _)).mp h |>.trans_eq (one_mul _)

theorem positiveVectors_convex {I : Type} : Convex ℝ {p : I → ℝ | ∀ i, 0 < p i} := by
  have h := convex_pi (𝕜 := ℝ) (s := (univ : Set I)) (fun i hi => convex_Ioi (0 : ℝ))
  simpa only [Set.pi,mem_univ,forall_true_left,mem_Ioi] using h

theorem finiteLogPartition_population_concave {I : Type} [Fintype I] [Nonempty I]
    (u : I → ℝ) :
    ConcaveOn ℝ {p : I → ℝ | ∀ i, 0 < p i} (fun p => Real.log (finitePartition p u)) := by
  have h := strictConcaveOn_log_Ioi.concaveOn.comp_linearMap (finitePartitionLinear u)
  exact h.subset (fun p hp => finitePartition_pos p u hp) positiveVectors_convex

theorem finitePartition_continuous {I : Type} [Fintype I] :
    Continuous (fun z : (I → ℝ) × (I → ℝ) => finitePartition z.1 z.2) := by
  unfold finitePartition
  fun_prop

theorem finiteLogPartition_continuousOn {I : Type} [Fintype I] [Nonempty I] :
    ContinuousOn (fun z : (I → ℝ) × (I → ℝ) => Real.log (finitePartition z.1 z.2))
      {z | ∀ i, 0 < z.1 i} := by
  exact finitePartition_continuous.continuousOn.log
    (fun z hz => (finitePartition_pos z.1 z.2 hz).ne')

theorem finitePerspective_convex {I : Type} (f : (I → ℝ) → ℝ)
    (hf : ConvexOn ℝ univ f) :
    ConvexOn ℝ {z : (I → ℝ) × ℝ | 0 < z.2}
      (fun z => z.2*f (fun i => z.1 i/z.2)) := by
  refine ⟨(convex_Ioi (0 : ℝ)).linear_preimage (LinearMap.snd ℝ (I → ℝ) ℝ),?_⟩
  intro x hx y hy a b ha hb hab
  have hx' : 0 < x.2 := hx
  have hy' : 0 < y.2 := hy
  let c := a*x.2+b*y.2
  have hc : 0 < c := by
    dsimp [c]
    rcases eq_or_lt_of_le ha with rfl | ha'
    · have hb' : b = 1 := by linarith
      simp [hb',hy']
    · exact add_pos_of_pos_of_nonneg (mul_pos ha' hx') (mul_nonneg hb hy'.le)
  have hsum : a*x.2/c+b*y.2/c = 1 := by
    rw [← add_div]
    exact div_self hc.ne'
  have h := hf.2 (x := fun i => x.1 i/x.2) (y := fun i => y.1 i/y.2)
    (mem_univ _) (mem_univ _) (div_nonneg (mul_nonneg ha hx'.le) hc.le)
    (div_nonneg (mul_nonneg hb hy'.le) hc.le) hsum
  have he : (a*x.2/c) • (fun i => x.1 i/x.2)+(b*y.2/c) • (fun i => y.1 i/y.2) =
      (fun i => (a*x.1 i+b*y.1 i)/c) := by
    funext i
    simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul]
    field_simp
  rw [he] at h
  have hh := mul_le_mul_of_nonneg_left h hc.le
  simp only [smul_eq_mul] at hh ⊢
  change c*f (fun i => (a*x.1 i+b*y.1 i)/c) ≤ _
  convert hh using 1
  field_simp

theorem convex_concave_uniform_strict {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (X : Set E) (Y : Set F) (hXn : X.Nonempty) (hXc : IsCompact X)
    (hXv : Convex ℝ X) (hYv : Convex ℝ Y) (f : E → F → ℝ)
    (hxc : ∀ y ∈ Y, ContinuousOn (fun x => f x y) X)
    (hxv : ∀ y ∈ Y, ConcaveOn ℝ X (fun x => f x y))
    (hyc : ∀ x ∈ X, ContinuousOn (f x) Y)
    (hyv : ∀ x ∈ X, ConvexOn ℝ Y (f x))
    (t : ℝ) (ht : ∀ x ∈ X, ∃ y ∈ Y, f x y < t) :
    ∃ y ∈ Y, ∀ x ∈ X, f x y < t := by
  have hdisj : Disjoint X (⋂ y ∈ Y, (fun x => -f x y) ⁻¹' Iic (-t)) := by
    rw [Set.disjoint_left]
    intro x hx hall
    obtain ⟨y,hy,hylt⟩ := ht x hx
    have h := Set.mem_iInter.mp (Set.mem_iInter.mp hall y) hy
    change -f x y ≤ -t at h
    linarith
  obtain ⟨s,hs⟩ := (LowerSemicontinuousOn.disjoint_biInter_preimage_Iic_iff_exists_finset
    hXc (fun y hy => (hxc y hy).neg.lowerSemicontinuousOn)).mp hdisj
  have hs' (x) (hx : x ∈ X) : ∃ y ∈ Subtype.val '' (s : Set Y), -t < -f x y := by
    obtain ⟨i,hi,hi'⟩ := hs x hx
    exact ⟨i.val,⟨i,hi,rfl⟩,hi'⟩
  obtain ⟨y,hy,h⟩ := Sion.exists_lt_iInf_of_lt_iInf_of_finite hXn hXc
    (fun y hy => (hxc y hy).neg.lowerSemicontinuousOn)
    (fun y hy => (hxv y hy).neg.quasiconvexOn) hYv
    (fun x hx => (hyc x hx).neg.upperSemicontinuousOn)
    (fun x hx => (hyv x hx).neg.quasiconcaveOn) hXv
    (toFinite _) (Subtype.coe_image_subset Y ↑s) hs'
  refine ⟨y,hy,?_⟩
  intro x hx
  have h' := h x hx
  change -t < -f x y at h'
  linarith

theorem exists_positive_scale_lt (d c t : ℝ) (hc : 0 ≤ c → d < t) :
    ∃ a : ℝ, 0 < a ∧ d+a*c < t := by
  by_cases hc0 : 0 ≤ c
  · have hd := hc hc0
    refine ⟨(t-d)/(2*(c+1)),div_pos (sub_pos.mpr hd) (by positivity),?_⟩
    have hden : 0 < 2*(c+1) := by positivity
    have hmul : (t-d)/(2*(c+1))*c < t-d := by
      rw [div_mul_eq_mul_div]
      apply (div_lt_iff₀ hden).mpr
      nlinarith
    linarith
  · have hcneg : c < 0 := lt_of_not_ge hc0
    refine ⟨(|t-d|+1)/(-c),div_pos (by positivity) (by linarith),?_⟩
    have he : ((|t-d|+1)/(-c))*c = -(|t-d|+1) := by field_simp [hcneg.ne]
    rw [he]
    have hh := neg_le_abs (t-d)
    linarith

theorem finiteRepeatedObjective_pointwise {I : Type} [Fintype I] [Nonempty I]
    (p q : I → ℝ) (hp : ∀ i, 0 < p i) (hq : ∀ i, 0 < q i)
    (d t : ℝ) (n : ℕ)
    (hdt : 1/2 ≤ (realFiniteAffinity p q)^n → d < t) :
    ∃ (u : I → ℝ) (a : ℝ), 0 < a ∧ finiteRepeatedObjective p q d n u a < t := by
  obtain ⟨v,hv⟩ := finite_log_partition_attained p q hp hq
  have haff := realFiniteAffinity_pos p q hp hq
  have hc : 0 ≤ 2*((n : ℝ)*Real.log (realFiniteAffinity p q)+Real.log 2) → d < t := by
    intro h
    apply hdt
    have he : Real.log ((realFiniteAffinity p q)^n*2) =
        (n : ℝ)*Real.log (realFiniteAffinity p q)+Real.log 2 := by
      rw [Real.log_mul (pow_pos haff n).ne' (by norm_num),Real.log_pow]
    have hl : 0 ≤ Real.log ((realFiniteAffinity p q)^n*2) := by rw [he]; linarith
    have hb : 1 ≤ (realFiniteAffinity p q)^n*2 :=
      (Real.log_nonneg_iff (by positivity)).mp hl
    linarith
  obtain ⟨a,ha,hat⟩ := exists_positive_scale_lt d _ t hc
  refine ⟨a • v,a,ha,?_⟩
  have hplus : (fun i => (a • v) i/a) = v := by
    funext i
    simp [ha.ne']
  have hminus : (fun i => -(a • v) i/a) = -v := by
    funext i
    simp only [Pi.smul_apply,Pi.neg_apply,smul_eq_mul]
    field_simp [ha.ne']
  unfold finiteRepeatedObjective
  rw [hplus,hminus]
  calc
    _ = d+a*(2*((n : ℝ)*Real.log (realFiniteAffinity p q)+Real.log 2)) := by
      have hscaled := congrArg (fun x : ℝ => d+a*((n : ℝ)*x+2*Real.log 2)) hv
      convert hscaled using 1 <;> ring
    _ < t := hat

theorem finiteRepeatedObjective_convex {I : Type} [Fintype I] [Nonempty I]
    (p q : I → ℝ) (hp : ∀ i, 0 < p i) (hq : ∀ i, 0 < q i) (d : ℝ) (n : ℕ) :
    ConvexOn ℝ {z : (I → ℝ) × ℝ | 0 < z.2}
      (fun z => finiteRepeatedObjective p q d n z.1 z.2) := by
  let L : ((I → ℝ) × ℝ) →ₗ[ℝ] ((I → ℝ) × ℝ) :=
    { toFun := fun z => (-z.1,z.2)
      map_add' := by intro x y; apply Prod.ext <;> simp [add_comm]
      map_smul' := by intro c x; apply Prod.ext <;> simp }
  have hpos := finitePerspective_convex (fun u => Real.log (finitePartition q u))
    (finiteLogPartition_convex q hq)
  have hneg : ConvexOn ℝ {z : (I → ℝ) × ℝ | 0 < z.2}
      (fun z => z.2*Real.log (finitePartition p (fun i => -z.1 i/z.2))) := by
    exact (finitePerspective_convex (fun u => Real.log (finitePartition p u))
      (finiteLogPartition_convex p hp)).comp_linearMap L
  have hcore := ConvexOn.smul (Nat.cast_nonneg n : (0 : ℝ) ≤ n) (hneg.add hpos)
  have hlin : ConvexOn ℝ {z : (I → ℝ) × ℝ | 0 < z.2}
      (fun z => d+2*Real.log 2*z.2) := by
    refine ⟨hpos.1,?_⟩
    intro x hx y hy a b ha hb hab
    change d+2*Real.log 2*(a*x.2+b*y.2) ≤
      a*(d+2*Real.log 2*x.2)+b*(d+2*Real.log 2*y.2)
    nlinarith [congrArg (fun t : ℝ => t*d) hab]
  have he : (fun z : (I → ℝ) × ℝ => finiteRepeatedObjective p q d n z.1 z.2) =
      (fun z => (n : ℝ)*(z.2*Real.log (finitePartition p (fun i => -z.1 i/z.2))+
        z.2*Real.log (finitePartition q (fun i => z.1 i/z.2)))) +
        (fun z => d+2*Real.log 2*z.2) := by
    funext z
    simp only [finiteRepeatedObjective,Pi.add_apply]
    ring
  rw [he]
  exact hcore.add hlin

end ThresholdHC.CriticalEntropy
