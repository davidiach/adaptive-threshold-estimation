import ThresholdHC.CriticalEntropy.FinitePopulation
import ThresholdHC.CriticalEntropy.SeedAdaptation
import ThresholdHC.Tier4.FiniteDensity

noncomputable section
open MeasureTheory InformationTheory
open scoped ENNReal
namespace ThresholdHC.ConfidenceTransfer
open ThresholdHC.CriticalEntropy

/-- On a common finite support, taking the real logarithm at zero costs no mass. -/
theorem finite_weight_kl {Z : Type} [MeasurableSpace Z] [Fintype Z] [MeasurableSingletonClass Z]
    (p q : Z → ℝ) (hp : ∀ z, 0 ≤ p z) (hq : ∀ z, 0 ≤ q z)
    (sp : ∑ z, p z = 1) (sq : ∑ z, q z = 1) (hc : ∀ z, q z = 0 → p z = 0) :
    klDiv (finiteWeightMeasure p) (finiteWeightMeasure q) =
      ENNReal.ofReal (∑ z, p z * Real.log (p z / q z)) := by
  let P := finiteWeightMeasure p
  let Q := finiteWeightMeasure q
  let : IsProbabilityMeasure P := finiteWeightMeasure_probability p hp sp
  let : IsProbabilityMeasure Q := finiteWeightMeasure_probability q hq sq
  let r := fun z => p z/q z
  have hr (z) : 0 ≤ r z := div_nonneg (hp _) (hq _)
  have hd : Q.withDensity (fun z => ENNReal.ofReal (r z)) = P := by
    apply Measure.ext_of_singleton
    intro z
    rw [withDensity_apply _ (measurableSet_singleton z),lintegral_singleton]
    change ENNReal.ofReal (p z / q z) * finiteWeightMeasure q {z} = finiteWeightMeasure p {z}
    simp only [finiteWeightMeasure_singleton]
    rw [← ENNReal.ofReal_mul (div_nonneg (hp _) (hq _))]
    by_cases h : q z = 0
    · simp [h,hc z h]
    · rw [div_mul_cancel₀ _ h]
  rw [Tier4.klDiv_of_finite_likelihood P Q id measurable_id r hr hd]
  congr 1
  rw [integral_fintype Integrable.of_finite]
  simp only [P,finiteWeightMeasure_real_singleton p hp,smul_eq_mul,id_eq,r]

theorem finite_weight_gibbs {Z : Type} [Fintype Z]
    (p q : Z → ℝ) (hp : ∀ z, 0 ≤ p z) (hq : ∀ z, 0 ≤ q z)
    (sp : ∑ z, p z = 1) (sq : ∑ z, q z = 1) (hc : ∀ z, q z = 0 → p z = 0) :
    0 ≤ ∑ z, p z * Real.log (p z / q z) := by
  calc
    0 = ∑ z, (p z - q z) := by rw [Finset.sum_sub_distrib, sp, sq, sub_self]
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro z _
      by_cases hz : p z = 0
      · simpa [hz] using hq z
      have hq' := mt (hc z) hz
      have h := Real.one_sub_inv_le_log_of_pos
        (div_pos (lt_of_le_of_ne (hp z) (Ne.symm hz)) (lt_of_le_of_ne (hq z) (Ne.symm hq')))
      have h' := mul_le_mul_of_nonneg_left h (hp z)
      rwa [mul_sub, mul_one, inv_div, ← mul_div_assoc, mul_div_cancel_left₀ _ hz] at h'

/-- The log likelihood ratio at a reference-positive leaf is additive over slots. -/
private theorem hybrid_leaf_log {I : Type} [Fintype I] [DecidableEq I]
    (a : ℝ) (p q : I → ℝ) (hs : ∀ i, q i = 0 → p i = 0) :
    let ref := a * ∏ i, p i
    ref * Real.log (ref / (a * ∏ i, q i)) =
      ∑ i, ref * Real.log (ref / (a * ∏ j, if j=i then q j else p j)) := by
  dsimp only
  by_cases h : a * ∏ i, p i = 0
  · simp [h]
  obtain ⟨ha,hp⟩ := mul_ne_zero_iff.mp h
  have hp' (i : I) : p i ≠ 0 := (Finset.prod_ne_zero_iff.mp hp) i (Finset.mem_univ i)
  have hq' (i : I) : q i ≠ 0 := mt (hs i) (hp' i)
  have hlog (v : I → ℝ) (hv : ∀ i, v i ≠ 0) :
      Real.log ((a * ∏ i, p i)/(a * ∏ i, v i)) = ∑ i, (Real.log (p i)-Real.log (v i)) := by
    have hv' : ∏ i, v i ≠ 0 := Finset.prod_ne_zero_iff.mpr fun i _ => hv i
    rw [Real.log_div h (mul_ne_zero ha hv'),Real.log_mul ha hp,Real.log_mul ha hv',
      Real.log_prod (fun i _ => hp' i),Real.log_prod (fun i _ => hv i), Finset.sum_sub_distrib]
    ring
  have hsingle (i : I) : Real.log ((a * ∏ j, p j)/(a * ∏ j, if j=i then q j else p j)) =
      Real.log (p i)-Real.log (q i) := by
    rw [hlog (fun j => if j=i then q j else p j) (fun j => by split <;> first | exact hq' _ | exact hp' _)]
    simp only [apply_ite Real.log]
    simp_rw [sub_ite,sub_self]
    simp
  rw [hlog q hq',Finset.mul_sum]
  simp_rw [hsingle]

/-- Switching all slots has KL equal to the sum for switching one slot at a time
while keeping all other slots at the same reference law. The common multiplier
may be zero on inconsistent transcripts. -/
private theorem factor_kl_sum {I Z : Type} [Fintype I] [DecidableEq I] [Fintype Z]
    [MeasurableSpace Z] [MeasurableSingletonClass Z]
    (a : Z → ℝ) (p q : I → Z → ℝ) (P Q : Z → ℝ) (H : I → Z → ℝ)
    (hP : ∀ z, P z = a z*∏ i, p i z) (hQ : ∀ z, Q z = a z*∏ i, q i z)
    (hH : ∀ i z, H i z = a z*∏ j, if j=i then q j z else p j z)
    (hs : ∀ i z, q i z = 0 → p i z = 0)
    (pn : (∀ z, 0 ≤ P z) ∧ ∑ z, P z = 1) (qn : (∀ z, 0 ≤ Q z) ∧ ∑ z, Q z = 1)
    (hn : ∀ i, (∀ z, 0 ≤ H i z) ∧ ∑ z, H i z = 1) :
    klDiv (finiteWeightMeasure P) (finiteWeightMeasure Q) =
      ∑ i, klDiv (finiteWeightMeasure P) (finiteWeightMeasure (H i)) := by
  classical
  have supp (R : Z → ℝ) (r : I → Z → ℝ) (hr : ∀ z, R z = a z*∏ i, r i z)
      (hsr : ∀ i z, r i z = 0 → p i z = 0) : ∀ z, R z = 0 → P z = 0 := by
    intro z hz
    rw [hr] at hz
    rw [hP]
    rcases mul_eq_zero.mp hz with h|h
    · simp [h]
    obtain ⟨i,hi,hzero⟩ := Finset.prod_eq_zero_iff.mp h
    rw [Finset.prod_eq_zero hi (hsr i z hzero), mul_zero]
  have hqs := supp Q q hQ hs
  have hhs (i) := supp (H i) (fun j z => if j=i then q j z else p j z) (hH i)
    (fun j z => by split <;> first | exact hs j z | exact id)
  rw [finite_weight_kl P Q pn.1 qn.1 pn.2 qn.2 hqs]
  simp_rw [fun i => finite_weight_kl P (H i) pn.1 (hn i).1 pn.2 (hn i).2 (hhs i)]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => finite_weight_gibbs P (H i)
    pn.1 (hn i).1 pn.2 (hn i).2 (hhs i)), Finset.sum_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro z _
  simp only [hP,hQ,hH]
  exact hybrid_leaf_log (a z) (fun i => p i z) (fun i => q i z) (fun i => hs i z)

local instance : MeasurableSpace (Option Bool) := ⊤
local instance : MeasurableSingletonClass (Option Bool) := ⟨fun _ => trivial⟩

/-- Factorization of KL for a fixed finite adaptive decision tree with common local support.
The policy can revisit its coins and interleave their flips. -/
theorem population_hybrid_kl {D : Type} [MeasurableSpace D] {m n : ℕ}
    (μ : Measure D) [IsProbabilityMeasure μ] (pol : List Bool → Option (Fin m))
    (d q r : D → ℝ) (hdm : Measurable d) (hqm : Measurable q) (hrm : Measurable r)
    (hd : ∀ x, 0 ≤ d x ∧ d x ≤ 1/2) (hq : ∀ x, 0 ≤ q x ∧ q x ≤ 1)
    (hr : ∀ x, 0 ≤ r x ∧ r x ≤ 1)
    (hs : ∀ (i : Fin m) (w : Fin n → Option Bool),
      populationCoinMass μ pol d r w i = 0 → populationCoinMass μ pol d q w i = 0) :
    let W := fun u => finiteWeightMeasure (finitePopulationWeight (n := n) μ pol d u)
    klDiv (W (fun _ => q)) (W (fun _ => r)) =
      ∑ i : Fin m, klDiv (W (fun _ => q)) (W (fun j => if j=i then r else q)) := by
  apply factor_kl_sum (ThresholdHC.Proofs.pathValidity pol)
    (fun i w => populationCoinMass μ pol d q w i) (fun i w => populationCoinMass μ pol d r w i)
  · exact finite_population_factor μ pol d _
  · exact finite_population_factor μ pol d _
  · intro i w
    rw [finite_population_factor]
    congr 1
    apply Finset.prod_congr rfl
    intro j _
    by_cases hj : j=i <;> simp [hj,populationCoinMass]
  · exact hs
  · exact finite_population_total μ pol d _ hdm (fun _ => hqm) hd (fun _ => hq)
  · exact finite_population_total μ pol d _ hdm (fun _ => hrm) hd (fun _ => hr)
  · intro i
    exact finite_population_total μ pol d _ hdm (fun j => by split <;> assumption) hd
      (fun j x => by split <;> first | exact hq x | exact hr x)

/-- Affineness holds for the mass of an individual persistent coin's word. -/
theorem quarter_coin_mass {D : Type} [MeasurableSpace D] {m n : ℕ}
    (μ : Measure D) [IsProbabilityMeasure μ] (pol : List Bool → Option (Fin m))
    (d q r : D → ℝ) (hdm : Measurable d) (hqm : Measurable q) (hrm : Measurable r)
    (hd : ∀ x, 0 ≤ d x ∧ d x ≤ 1/2) (hq : ∀ x, 0 ≤ q x ∧ q x ≤ 1)
    (hr : ∀ x, 0 ≤ r x ∧ r x ≤ 1) (w : Fin n → Option Bool) (i : Fin m) :
    populationCoinMass μ pol d (fun x => (3*q x+r x)/4) w i =
      (3*populationCoinMass μ pol d q w i + populationCoinMass μ pol d r w i)/4 := by
  unfold populationCoinMass
  have hiq := population_coin_integrable μ pol d q hdm hqm hd hq w i
  have hir := population_coin_integrable μ pol d r hdm hrm hd hr w i
  rw [← integral_const_mul, ← integral_add (hiq.const_mul 3) hir, ← integral_div]
  apply integral_congr_ae
  exact ae_of_all _ fun x => by ring

/-- Equation (6) for the genuine finite population. Smoothing applies to the
prior of each coin, before the full adaptive transcript law is formed. -/
theorem quarter_population_hybrid_kl {D : Type} [MeasurableSpace D] {m n : ℕ}
    (μ : Measure D) [IsProbabilityMeasure μ] (pol : List Bool → Option (Fin m))
    (d q r : D → ℝ) (hdm : Measurable d) (hqm : Measurable q) (hrm : Measurable r)
    (hd : ∀ x, 0 ≤ d x ∧ d x ≤ 1/2) (hq : ∀ x, 0 ≤ q x ∧ q x ≤ 1)
    (hr : ∀ x, 0 ≤ r x ∧ r x ≤ 1) :
    let q₀ := fun x => (3*q x+r x)/4
    let q₁ := fun x => (3*r x+q x)/4
    let W := fun u => finiteWeightMeasure (finitePopulationWeight (n := n) μ pol d u)
    klDiv (W (fun _ => q₀)) (W (fun _ => q₁)) =
      ∑ i : Fin m, klDiv (W (fun _ => q₀)) (W (fun j => if j=i then q₁ else q₀)) := by
  apply population_hybrid_kl μ pol d _ _ hdm
  · fun_prop
  · fun_prop
  · exact hd
  · intro x; constructor <;> linarith [(hq x).1,(hq x).2,(hr x).1,(hr x).2]
  · intro x; constructor <;> linarith [(hq x).1,(hq x).2,(hr x).1,(hr x).2]
  · intro i w hz
    rw [quarter_coin_mass μ pol d r q hdm hrm hqm hd hr hq] at hz
    rw [quarter_coin_mass μ pol d q r hdm hqm hrm hd hq hr]
    have hq' : 0 ≤ populationCoinMass μ pol d q w i := integral_nonneg
      fun x => (population_coin_integrand_bounds pol w i _ _ (hd x) (hq x)).1
    have hr' : 0 ≤ populationCoinMass μ pol d r w i := integral_nonneg
      fun x => (population_coin_integrand_bounds pol w i _ _ (hd x) (hr x)).1
    linarith

end ThresholdHC.ConfidenceTransfer
