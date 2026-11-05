import ThresholdHC.Tier6.HardPairModel

noncomputable section
open MeasureTheory
open scoped Polynomial Topology
namespace ThresholdHC.LawAdaptation
open ThresholdHC.Tier6

/-- The sign-neutral moment observed by a prefix of length twice its index. -/
def evenMoment (μ : Measure Gap) (k : ℕ) : ℝ :=
  ∫ d, (2*(d:ℝ))^(2*k) ∂μ

private theorem compact_integrable (μ : Measure unitInterval) [IsFiniteMeasure μ]
    (f : C(unitInterval, ℝ)) : Integrable f μ :=
  f.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace f)

private theorem continuous_compact_integral (μ : Measure unitInterval)
    [IsProbabilityMeasure μ] :
    Continuous (fun f : C(unitInterval, ℝ) => ∫ x, f x ∂μ) := by
  apply LipschitzWith.continuous (K := 1)
  apply LipschitzWith.of_dist_le_mul
  intro f g
  simp only [NNReal.coe_one, one_mul, Real.dist_eq]
  rw [← integral_sub (compact_integrable μ f) (compact_integrable μ g)]
  have h := norm_integral_le_of_norm_le_const (μ := μ)
    (C := ‖f-g‖) (f := fun x => f x-g x)
    (Filter.Eventually.of_forall (fun x => (f-g).norm_coe_le_norm x))
  simpa only [Real.norm_eq_abs, probReal_univ, mul_one, dist_eq_norm] using h

/-- Probability measures on the compact unit interval are determined by moments. -/
theorem unitInterval_eq_of_moments (μ ν : Measure unitInterval)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (h : ∀ k : ℕ, ∫ x, (x:ℝ)^k ∂μ = ∫ x, (x:ℝ)^k ∂ν) : μ = ν := by
  have hp (p : Polynomial ℝ) :
      ∫ x : unitInterval, p.eval (x:ℝ) ∂μ =
        ∫ x : unitInterval, p.eval (x:ℝ) ∂ν := by
    induction p using Polynomial.induction_on' with
    | add p q hp hq =>
      have hi (σ : Measure unitInterval) [IsProbabilityMeasure σ] (p : Polynomial ℝ) :
          Integrable (fun x : unitInterval => p.eval (x:ℝ)) σ :=
        compact_integrable σ (p.toContinuousMapOn (Set.Icc (0:ℝ) 1))
      simp only [Polynomial.eval_add, integral_add (hi μ p) (hi μ q),
        integral_add (hi ν p) (hi ν q), hp, hq]
    | monomial n a =>
      simp only [Polynomial.eval_monomial, integral_const_mul, h n]
  have hs : (polynomialFunctions (Set.Icc (0:ℝ) 1) : Set C(unitInterval,ℝ)) ⊆
      {f | (∫ x, f x ∂μ) = ∫ x, f x ∂ν} := by
    intro f hf
    rw [polynomialFunctions_coe] at hf
    obtain ⟨p,rfl⟩ := hf
    exact hp p
  have hc := closure_minimal hs (isClosed_eq
    (continuous_compact_integral μ) (continuous_compact_integral ν))
  have hd : closure (polynomialFunctions (Set.Icc (0:ℝ) 1) : Set C(unitInterval,ℝ)) =
      Set.univ := by
    rw [← Subalgebra.topologicalClosure_coe, polynomialFunctions.topologicalClosure]
    rfl
  apply ext_of_forall_integral_eq_of_IsFiniteMeasure
  intro f
  exact hc (hd ▸ Set.mem_univ (f.toContinuousMap))

/-- Embed a positive gap into the compact moment domain. -/
def squaredGap (d : Gap) : unitInterval :=
  ⟨(2*(d:ℝ))^2, by
    have hd := d.property
    constructor
    · positivity
    · nlinarith [sq_nonneg (2*(d:ℝ)-1)]⟩

theorem measurable_squaredGap : Measurable squaredGap :=
  ((measurable_const.mul measurable_subtype_coe).pow_const 2).subtype_mk

theorem squaredGap_injective : Function.Injective squaredGap := by
  intro d e h
  have he := congrArg Subtype.val h
  change (2*(d:ℝ))^2 = (2*(e:ℝ))^2 at he
  apply Subtype.ext
  have hd := d.property.1
  have he' := e.property.1
  nlinarith [sq_nonneg ((d:ℝ)-(e:ℝ))]

/-- All positive even moments determine the original gap law. -/
theorem gapLaw_eq_of_evenMoments (μ ν : Measure Gap)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (h : ∀ k : ℕ, 0 < k → evenMoment μ k = evenMoment ν k) : μ = ν := by
  let : StandardBorelSpace Gap := (measurableSet_Ioc :
    MeasurableSet (Set.Ioc (0:ℝ) (1/2))).standardBorel
  have hemb : MeasurableEmbedding squaredGap :=
    measurable_squaredGap.measurableEmbedding squaredGap_injective
  apply hemb.map_injective
  apply unitInterval_eq_of_moments
  intro k
  have hm : Measurable (fun x : unitInterval => (x:ℝ)^k) :=
    measurable_subtype_coe.pow_const k
  rw [integral_map measurable_squaredGap.aemeasurable hm.aestronglyMeasurable,
    integral_map measurable_squaredGap.aemeasurable hm.aestronglyMeasurable]
  by_cases hk : k = 0
  · simp [hk]
  · simpa only [squaredGap, ← pow_mul, evenMoment] using h k (Nat.pos_of_ne_zero hk)

/-- Distinct positive-gap laws have a differing observable even moment. -/
theorem exists_separating_moment (μ ν : Measure Gap)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (hne : μ ≠ ν) :
    ∃ k : ℕ, 0 < k ∧ evenMoment μ k ≠ evenMoment ν k := by
  by_contra h
  push Not at h
  exact hne (gapLaw_eq_of_evenMoments μ ν h)

/-- A finite family has one finite signature length and one positive separation. -/
theorem finite_moment_separation {ι : Type*} [Fintype ι] [Nonempty ι]
    (laws : ι → Measure Gap) [∀ i, IsProbabilityMeasure (laws i)]
    (hinj : Function.Injective laws) :
    ∃ m : ℕ, 0 < m ∧ ∃ η : ℝ, 0 < η ∧
      ∀ i j, i ≠ j → ∃ k : Fin m,
        η ≤ |evenMoment (laws i) (k.val+1) - evenMoment (laws j) (k.val+1)| := by
  classical
  have hex (p : ι × ι) : ∃ k : ℕ, 0 < k ∧
      (p.1 ≠ p.2 → evenMoment (laws p.1) k ≠ evenMoment (laws p.2) k) := by
    by_cases hp : p.1 = p.2
    · exact ⟨1, by omega, fun h => (h hp).elim⟩
    · obtain ⟨k,hk,hd⟩ := exists_separating_moment (laws p.1) (laws p.2)
        (fun h => hp (hinj h))
      exact ⟨k,hk,fun _ => hd⟩
  choose k hk hd using hex
  let sep (p : ι × ι) := if p.1 = p.2 then (1:ℝ) else
    |evenMoment (laws p.1) (k p) - evenMoment (laws p.2) (k p)|
  have hp (p : ι × ι) : 0 < sep p := by
    dsimp only [sep]
    split_ifs with h
    · norm_num
    · exact abs_pos.mpr (sub_ne_zero.mpr (hd p h))
  let m := Finset.univ.sup k + 1
  let η := Finset.univ.inf' (Finset.univ_nonempty : (Finset.univ : Finset (ι × ι)).Nonempty) sep
  refine ⟨m, by dsimp [m]; omega, η, (Finset.lt_inf'_iff _).mpr (fun p _ => hp p), ?_⟩
  intro i j hij
  have hkm : k (i,j) < m := Nat.lt_succ_of_le (Finset.le_sup (Finset.mem_univ (i,j)))
  have hpos := hk (i,j)
  refine ⟨⟨k (i,j)-1, by omega⟩, ?_⟩
  have hindex : k (i,j)-1+1 = k (i,j) := by omega
  have hbound := Finset.inf'_le (s := Finset.univ) sep (Finset.mem_univ (i,j))
  simpa only [hindex, sep, ite_eq_right hij] using hbound


end ThresholdHC.LawAdaptation

