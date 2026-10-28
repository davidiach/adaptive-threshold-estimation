import ThresholdHC.CriticalEntropy.CriticalCommonPair
import ThresholdHC.Tier5.FiniteEnvironment

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace ThresholdHC.CriticalEntropy
open ThresholdHC.Proofs

/-- Integrate the existing finite adaptive transcript law over iid magnitudes.
Coin-specific sign priors allow the hybrid experiments used in the transfer. -/
def finitePopulationWeight {D : Type} [MeasurableSpace D] {m n : ℕ}
    (μ : Measure D) (pol : List Bool → Option (Fin m)) (d : D → ℝ)
    (q : Fin m → D → ℝ) (w : Fin n → Option Bool) : ℝ :=
  ∫ x : Fin m → D, ThresholdHC.transcriptLaw pol (fun i => d (x i))
    (fun i => q i (x i)) w ∂Measure.pi (fun _ => μ)

theorem finite_population_factor {D : Type} [MeasurableSpace D] {m n : ℕ}
    (μ : Measure D) [SigmaFinite μ] (pol : List Bool → Option (Fin m)) (d : D → ℝ)
    (q : Fin m → D → ℝ) (w : Fin n → Option Bool) :
    finitePopulationWeight μ pol d q w = pathValidity pol w *
      ∏ i, ∫ x, q i x*coinLike pol w i (1/2+d x) +
        (1-q i x)*coinLike pol w i (1/2-d x) ∂μ := by
  unfold finitePopulationWeight
  simp_rw [transcriptLaw_factor]
  rw [integral_const_mul]
  congr 1
  exact integral_fintype_prod_eq_prod (fun i x => q i x*coinLike pol w i (1/2+d x) +
    (1-q i x)*coinLike pol w i (1/2-d x))

theorem finite_population_total {D : Type} [MeasurableSpace D] {m n : ℕ}
    (μ : Measure D) [IsProbabilityMeasure μ] (pol : List Bool → Option (Fin m)) (d : D → ℝ)
    (q : Fin m → D → ℝ) (hdm : Measurable d) (hqm : ∀ i, Measurable (q i))
    (hd : ∀ x, 0 ≤ d x ∧ d x ≤ 1/2) (hq : ∀ i x, 0 ≤ q i x ∧ q i x ≤ 1) :
    (∀ w : Fin n → Option Bool, 0 ≤ finitePopulationWeight μ pol d q w) ∧
      (∑ w : Fin n → Option Bool, finitePopulationWeight μ pol d q w) = 1 := by
  classical
  let η := Measure.pi (fun _ : Fin m => μ)
  let F (w : Fin n → Option Bool) (x : Fin m → D) :=
    ThresholdHC.transcriptLaw pol (fun i => d (x i)) (fun i => q i (x i)) w
  have htotal (x : Fin m → D) := ThresholdHC.Proofs.transcript_law_total m n pol
    (fun i => d (x i)) (fun i => q i (x i)) (fun i => hd _) (fun i => hq i _)
  have hP : ThresholdHC.Tier3.MeasurablePolicy (fun _ : Fin m → D => pol) := by
    intro xs a
    by_cases h : pol xs = a <;> simp [h]
  have hfm (w : Fin n → Option Bool) : Measurable (F w) :=
    ThresholdHC.Tier5.measurable_variable_transcriptLaw (fun _ : Fin m → D => pol) hP
      (fun x i => d (x i)) (fun x i => q i (x i))
      (fun i => hdm.comp (measurable_pi_apply i)) (fun i => (hqm i).comp (measurable_pi_apply i)) w
  have hfi (w : Fin n → Option Bool) : Integrable (F w) η := by
    apply Integrable.of_bound (hfm w).aestronglyMeasurable 1
    apply ae_of_all
    intro x
    rw [Real.norm_eq_abs,abs_of_nonneg ((htotal x).1 w)]
    calc
      _ ≤ ∑ v : Fin n → Option Bool, F v x :=
        Finset.single_le_sum (fun v hv => (htotal x).1 v) (Finset.mem_univ w)
      _ = 1 := (htotal x).2
  constructor
  · intro w
    exact integral_nonneg (fun x => (htotal x).1 w)
  · change (∑ w, ∫ x, F w x ∂η) = 1
    rw [← integral_finsetSum _ (fun w hw => hfi w)]
    have he (x : Fin m → D) : (∑ w, F w x) = 1 := (htotal x).2
    simp_rw [he]
    simp [η]

def populationCoinMass {D : Type} [MeasurableSpace D] {m n : ℕ}
    (μ : Measure D) (pol : List Bool → Option (Fin m)) (d q : D → ℝ)
    (w : Fin n → Option Bool) (i : Fin m) : ℝ :=
  ∫ x, q x*coinLike pol w i (1/2+d x)+(1-q x)*coinLike pol w i (1/2-d x) ∂μ

theorem coinLike_le_one {m n : ℕ} (pol : List Bool → Option (Fin m))
    (w : Fin n → Option Bool) (i : Fin m) (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) :
    coinLike pol w i p ≤ 1 := by
  classical
  unfold coinLike
  apply Finset.prod_le_one₀
  · intro t ht
    split_ifs
    · cases h : w t with
      | none => simp [obsProb]
      | some b => cases b <;> simp [obsProb] <;> linarith
    · norm_num
  · intro t ht
    split_ifs
    · cases h : w t with
      | none => simp [obsProb]
      | some b => cases b <;> simp [obsProb] <;> linarith
    · norm_num

theorem continuous_coinLike {m n : ℕ} (pol : List Bool → Option (Fin m))
    (w : Fin n → Option Bool) (i : Fin m) : Continuous (coinLike pol w i) := by
  classical
  unfold coinLike
  apply continuous_finsetProd
  intro t ht
  by_cases hi : pol (ThresholdHC.histBefore w t) = some i
  · simp only [hi,ite_true]
    cases h : w t with
    | none => simp only [obsProb]; fun_prop
    | some b => cases b <;> simp only [obsProb] <;> fun_prop
  · simp only [hi,ite_false]
    exact continuous_const

theorem population_coin_integrand_bounds {m n : ℕ}
    (pol : List Bool → Option (Fin m)) (w : Fin n → Option Bool) (i : Fin m)
    (d q : ℝ) (hd : 0 ≤ d ∧ d ≤ 1/2) (hq : 0 ≤ q ∧ q ≤ 1) :
    q*coinLike pol w i (1/2+d)+(1-q)*coinLike pol w i (1/2-d) ∈ Icc 0 1 := by
  have hp₀ : 0 ≤ 1/2-d := by linarith
  have hp₁ : 0 ≤ 1/2+d := by linarith
  have hp₀' : 1/2-d ≤ 1 := by linarith
  have hp₁' : 1/2+d ≤ 1 := by linarith
  have h₀ := coinLike_nonneg pol w i hp₀ hp₀'
  have h₁ := coinLike_nonneg pol w i hp₁ hp₁'
  have h₀' := coinLike_le_one pol w i _ hp₀ hp₀'
  have h₁' := coinLike_le_one pol w i _ hp₁ hp₁'
  constructor
  · exact add_nonneg (mul_nonneg hq.1 h₁) (mul_nonneg (by linarith) h₀)
  · nlinarith [mul_nonneg hq.1 (sub_nonneg.mpr h₁'),
      mul_nonneg (sub_nonneg.mpr hq.2) (sub_nonneg.mpr h₀')]

theorem population_coin_integrable {D : Type} [MeasurableSpace D] {m n : ℕ}
    (μ : Measure D) [IsProbabilityMeasure μ] (pol : List Bool → Option (Fin m)) (d q : D → ℝ)
    (hdm : Measurable d) (hqm : Measurable q)
    (hd : ∀ x, 0 ≤ d x ∧ d x ≤ 1/2) (hq : ∀ x, 0 ≤ q x ∧ q x ≤ 1)
    (w : Fin n → Option Bool) (i : Fin m) :
    Integrable (fun x => q x*coinLike pol w i (1/2+d x)+
      (1-q x)*coinLike pol w i (1/2-d x)) μ := by
  have hm : Measurable (fun x => q x*coinLike pol w i (1/2+d x)+
      (1-q x)*coinLike pol w i (1/2-d x)) :=
    (hqm.mul ((continuous_coinLike pol w i).measurable.comp (measurable_const.add hdm))).add
      ((measurable_const.sub hqm).mul
        ((continuous_coinLike pol w i).measurable.comp (measurable_const.sub hdm)))
  apply Integrable.of_bound hm.aestronglyMeasurable 1
  apply ae_of_all
  intro x
  have hb := population_coin_integrand_bounds pol w i _ _ (hd x) (hq x)
  rw [Real.norm_eq_abs,abs_of_nonneg hb.1]
  exact hb.2

theorem populationCoinMass_midpoint {D : Type} [MeasurableSpace D] {m n : ℕ}
    (μ : Measure D) [IsProbabilityMeasure μ] (pol : List Bool → Option (Fin m)) (d q r : D → ℝ)
    (hdm : Measurable d) (hqm : Measurable q) (hrm : Measurable r)
    (hd : ∀ x, 0 ≤ d x ∧ d x ≤ 1/2)
    (hq : ∀ x, 0 ≤ q x ∧ q x ≤ 1) (hr : ∀ x, 0 ≤ r x ∧ r x ≤ 1)
    (w : Fin n → Option Bool) (i : Fin m) :
    populationCoinMass μ pol d (fun x => (q x+r x)/2) w i =
      (populationCoinMass μ pol d q w i+populationCoinMass μ pol d r w i)/2 := by
  unfold populationCoinMass
  have hiq := population_coin_integrable μ pol d q hdm hqm hd hq w i
  have hir := population_coin_integrable μ pol d r hdm hrm hd hr w i
  rw [← integral_add hiq hir,← integral_div]
  apply integral_congr_ae
  exact ae_of_all _ (fun x => by ring)

end ThresholdHC.CriticalEntropy

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace ThresholdHC.CriticalEntropy

theorem product_defect_le_sum {I : Type*} [DecidableEq I]
    (m c : I → ℝ) (hc : ∀ i, 0 ≤ c i) (hcm : ∀ i, c i ≤ m i) (s : Finset I) :
    (∏ i ∈ s, m i)-(∏ i ∈ s, c i) ≤
      ∑ i ∈ s, (m i-c i)*(∏ j ∈ s.erase i, m j) := by
  have hm (i) : 0 ≤ m i := (hc i).trans (hcm i)
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    have hsum : 0 ≤ ∑ i ∈ s, (m i-c i)*(∏ j ∈ s.erase i, m j) :=
      Finset.sum_nonneg (fun i hi => mul_nonneg (sub_nonneg.mpr (hcm i))
        (Finset.prod_nonneg (fun j hj => hm j)))
    rw [Finset.prod_insert ha,Finset.prod_insert ha]
    calc
      _ = (m a-c a)*(∏ i ∈ s, m i)+c a*((∏ i ∈ s, m i)-(∏ i ∈ s, c i)) := by ring
      _ ≤ (m a-c a)*(∏ i ∈ s, m i)+c a*(∑ i ∈ s, (m i-c i)*(∏ j ∈ s.erase i, m j)) :=
        add_le_add_right (mul_le_mul_of_nonneg_left ih (hc a)) _
      _ ≤ (m a-c a)*(∏ i ∈ s, m i)+m a*(∑ i ∈ s, (m i-c i)*(∏ j ∈ s.erase i, m j)) :=
        add_le_add_right (mul_le_mul_of_nonneg_right (hcm a) hsum) _
      _ = _ := by
        rw [Finset.sum_insert ha,Finset.erase_insert ha,Finset.mul_sum]
        congr 1
        apply Finset.sum_congr rfl
        intro i hi
        have hai : a ≠ i := fun he => ha (he.symm ▸ hi)
        rw [Finset.erase_insert_of_ne hai,
          Finset.prod_insert (fun h => ha (Finset.mem_of_mem_erase h))]
        ring

theorem sqrt_product_common_factor (p q a : ℝ) (ha : 0 ≤ a) :
    Real.sqrt ((p*a)*(q*a)) = a*Real.sqrt (p*q) := by
  rw [show (p*a)*(q*a) = a^2*(p*q) by ring,
    Real.sqrt_mul (sq_nonneg a),Real.sqrt_sq ha]

theorem sqrt_product_le_midpoint (p q : ℝ) (hp : 0 ≤ p) (hq : 0 ≤ q) :
    Real.sqrt (p*q) ≤ (p+q)/2 := by
  nlinarith [Real.sq_sqrt (mul_nonneg hp hq),Real.sqrt_nonneg (p*q),sq_nonneg (p-q)]

/-- The algebraic finite-leaf decomposition. Its application to an adaptive
experiment still requires the actual leaf factorization and hybrid laws. -/
theorem finite_midpoint_hybrid_decomposition {I Z : Type} [Fintype I] [Fintype Z] [DecidableEq I]
    (p q : I → Z → ℝ) (hp : ∀ i z, 0 ≤ p i z) (hq : ∀ i z, 0 ≤ q i z)
    (hnorm : (∑ z, ∏ i, (p i z+q i z)/2) = 1) :
    1-realFiniteAffinity (fun z => ∏ i, p i z) (fun z => ∏ i, q i z) ≤
      ∑ i, (1-realFiniteAffinity
        (fun z => p i z*(∏ j ∈ Finset.univ.erase i, (p j z+q j z)/2))
        (fun z => q i z*(∏ j ∈ Finset.univ.erase i, (p j z+q j z)/2))) := by
  classical
  let m (i : I) (z : Z) := (p i z+q i z)/2
  let c (i : I) (z : Z) := Real.sqrt (p i z*q i z)
  have hm (i z) : 0 ≤ m i z := div_nonneg (add_nonneg (hp i z) (hq i z)) (by norm_num)
  have hc (i z) : 0 ≤ c i z := Real.sqrt_nonneg _
  have hcm (i z) : c i z ≤ m i z := sqrt_product_le_midpoint _ _ (hp i z) (hq i z)
  have hprod (z) : Real.sqrt ((∏ i, p i z)*(∏ i, q i z)) = ∏ i, c i z := by
    rw [← Finset.prod_mul_distrib,Real.sqrt_prod _ (fun i hi => mul_nonneg (hp i z) (hq i z))]
  have hhyb (i z) :
      Real.sqrt ((p i z*(∏ j ∈ Finset.univ.erase i, m j z))*
        (q i z*(∏ j ∈ Finset.univ.erase i, m j z))) =
      c i z*(∏ j ∈ Finset.univ.erase i, m j z) := by
    rw [sqrt_product_common_factor _ _ _ (Finset.prod_nonneg (fun j hj => hm j z)),mul_comm]
  have hpoint (z) := product_defect_le_sum (fun i => m i z) (fun i => c i z)
    (fun i => hc i z) (fun i => hcm i z) Finset.univ
  have hnorm' : (∑ z, ∏ i, m i z) = 1 := hnorm
  calc
    _ = ∑ z, ((∏ i, m i z)-(∏ i, c i z)) := by
      simp only [realFiniteAffinity]
      simp_rw [hprod]
      rw [Finset.sum_sub_distrib,hnorm']
    _ ≤ ∑ z, ∑ i, (m i z-c i z)*(∏ j ∈ Finset.univ.erase i, m j z) :=
      Finset.sum_le_sum (fun z hz => hpoint z)
    _ = _ := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i hi
      simp only [sub_mul,Finset.sum_sub_distrib]
      have he (z) : m i z*(∏ j ∈ Finset.univ.erase i, m j z) = ∏ j, m j z :=
        Finset.mul_prod_erase Finset.univ (fun j => m j z) (Finset.mem_univ i)
      simp_rw [he]
      rw [hnorm']
      congr 1
      unfold realFiniteAffinity
      apply Finset.sum_congr rfl
      intro z hz
      exact (hhyb i z).symm

theorem finite_weighted_midpoint_hybrid_decomposition {I Z : Type}
    [Fintype I] [Fintype Z] [DecidableEq I]
    (a : Z → ℝ) (ha : ∀ z, 0 ≤ a z)
    (p q : I → Z → ℝ) (hp : ∀ i z, 0 ≤ p i z) (hq : ∀ i z, 0 ≤ q i z)
    (hnorm : (∑ z, a z*(∏ i, (p i z+q i z)/2)) = 1) :
    1-realFiniteAffinity (fun z => a z*(∏ i, p i z)) (fun z => a z*(∏ i, q i z)) ≤
      ∑ i, (1-realFiniteAffinity
        (fun z => a z*p i z*(∏ j ∈ Finset.univ.erase i, (p j z+q j z)/2))
        (fun z => a z*q i z*(∏ j ∈ Finset.univ.erase i, (p j z+q j z)/2))) := by
  classical
  let m (i : I) (z : Z) := (p i z+q i z)/2
  let c (i : I) (z : Z) := Real.sqrt (p i z*q i z)
  have hm (i z) : 0 ≤ m i z := div_nonneg (add_nonneg (hp i z) (hq i z)) (by norm_num)
  have hc (i z) : 0 ≤ c i z := Real.sqrt_nonneg _
  have hcm (i z) : c i z ≤ m i z := sqrt_product_le_midpoint _ _ (hp i z) (hq i z)
  have hprod (z) : Real.sqrt ((a z*(∏ i, p i z))*(a z*(∏ i, q i z))) =
      a z*(∏ i, c i z) := by
    rw [show (a z*(∏ i, p i z))*(a z*(∏ i, q i z)) =
      ((∏ i, p i z)*a z)*((∏ i, q i z)*a z) by ring,
      sqrt_product_common_factor _ _ _ (ha z),← Finset.prod_mul_distrib,
      Real.sqrt_prod _ (fun i hi => mul_nonneg (hp i z) (hq i z))]
  have hhyb (i z) :
      Real.sqrt ((a z*p i z*(∏ j ∈ Finset.univ.erase i, m j z))*
        (a z*q i z*(∏ j ∈ Finset.univ.erase i, m j z))) =
      a z*c i z*(∏ j ∈ Finset.univ.erase i, m j z) := by
    have hM := Finset.prod_nonneg (fun j hj => hm j z) (s := Finset.univ.erase i)
    rw [show (a z*p i z*(∏ j ∈ Finset.univ.erase i, m j z))*
        (a z*q i z*(∏ j ∈ Finset.univ.erase i, m j z)) =
        (p i z*(a z*(∏ j ∈ Finset.univ.erase i, m j z)))*
        (q i z*(a z*(∏ j ∈ Finset.univ.erase i, m j z))) by ring,
      sqrt_product_common_factor _ _ _ (mul_nonneg (ha z) hM)]
    dsimp only [c]
    ring
  have hpoint (z) := mul_le_mul_of_nonneg_left
    (product_defect_le_sum (fun i => m i z) (fun i => c i z)
      (fun i => hc i z) (fun i => hcm i z) Finset.univ) (ha z)
  have hnorm' : (∑ z, a z*(∏ i, m i z)) = 1 := hnorm
  calc
    _ = ∑ z, a z*((∏ i, m i z)-(∏ i, c i z)) := by
      simp only [realFiniteAffinity]
      simp_rw [hprod]
      rw [show (∑ z, a z*((∏ i, m i z)-(∏ i, c i z))) =
        (∑ z, a z*(∏ i, m i z))-(∑ z, a z*(∏ i, c i z)) by
          simp only [mul_sub,Finset.sum_sub_distrib],hnorm']
    _ ≤ ∑ z, a z*(∑ i, (m i z-c i z)*(∏ j ∈ Finset.univ.erase i, m j z)) :=
      Finset.sum_le_sum (fun z hz => hpoint z)
    _ = _ := by
      simp only [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i hi
      have he (z) : a z*((m i z-c i z)*(∏ j ∈ Finset.univ.erase i, m j z)) =
          a z*(∏ j, m j z)-a z*c i z*(∏ j ∈ Finset.univ.erase i, m j z) := by
        rw [← Finset.mul_prod_erase Finset.univ (fun j => m j z) (Finset.mem_univ i)]
        ring
      simp_rw [he]
      rw [Finset.sum_sub_distrib,hnorm']
      congr 1
      unfold realFiniteAffinity
      apply Finset.sum_congr rfl
      intro z hz
      exact (hhyb i z).symm

end ThresholdHC.CriticalEntropy
namespace ThresholdHC.CriticalEntropy
open MeasureTheory ProbabilityTheory Set ThresholdHC.Proofs

/-- Hellinger decomposition for the existing finite adaptive experiment after
integrating iid magnitudes. The policy may revisit and interleave its coins. -/
theorem finite_population_hybrid_decomposition {D : Type} [MeasurableSpace D] {m n : ℕ}
    (μ : Measure D) [IsProbabilityMeasure μ] (pol : List Bool → Option (Fin m)) (d q r : D → ℝ)
    (hdm : Measurable d) (hqm : Measurable q) (hrm : Measurable r)
    (hd : ∀ x, 0 ≤ d x ∧ d x ≤ 1/2)
    (hq : ∀ x, 0 ≤ q x ∧ q x ≤ 1) (hr : ∀ x, 0 ≤ r x ∧ r x ≤ 1) :
    1-realFiniteAffinity (finitePopulationWeight (n := n) μ pol d (fun _ => q))
      (finitePopulationWeight μ pol d (fun _ => r)) ≤
    ∑ i : Fin m, (1-realFiniteAffinity
      (finitePopulationWeight (n := n) μ pol d (fun j => if j=i then q else fun x => (q x+r x)/2))
      (finitePopulationWeight μ pol d (fun j => if j=i then r else fun x => (q x+r x)/2))) := by
  classical
  let mid : D → ℝ := fun x => (q x+r x)/2
  let a (w : Fin n → Option Bool) := pathValidity pol w
  let p (i : Fin m) (w : Fin n → Option Bool) := populationCoinMass μ pol d q w i
  let s (i : Fin m) (w : Fin n → Option Bool) := populationCoinMass μ pol d r w i
  have hmidm : Measurable mid := (hqm.add hrm).div_const 2
  have hmid (x) : 0 ≤ mid x ∧ mid x ≤ 1 := by
    dsimp only [mid]
    constructor <;> linarith [(hq x).1,(hq x).2,(hr x).1,(hr x).2]
  have hmass (i : Fin m) (w : Fin n → Option Bool) :
      populationCoinMass μ pol d mid w i = (p i w+s i w)/2 :=
    populationCoinMass_midpoint μ pol d q r hdm hqm hrm hd hq hr w i
  have hp (i w) : 0 ≤ p i w := integral_nonneg
    (fun x => (population_coin_integrand_bounds pol w i _ _ (hd x) (hq x)).1)
  have hs (i w) : 0 ≤ s i w := integral_nonneg
    (fun x => (population_coin_integrand_bounds pol w i _ _ (hd x) (hr x)).1)
  have hfactor (u : Fin m → D → ℝ) (w : Fin n → Option Bool) :
      finitePopulationWeight μ pol d u w = a w*(∏ i, populationCoinMass μ pol d (u i) w i) :=
    finite_population_factor μ pol d u w
  have hnorm : (∑ w, a w*(∏ i, (p i w+s i w)/2)) = 1 := by
    have h := (finite_population_total (n := n) μ pol d (fun _ => mid)
      hdm (fun _ => hmidm) hd (fun _ => hmid)).2
    simpa only [hfactor,hmass] using h
  have hP : finitePopulationWeight (n := n) μ pol d (fun _ => q) =
      fun w => a w*(∏ i, p i w) := funext (hfactor _)
  have hQ : finitePopulationWeight (n := n) μ pol d (fun _ => r) =
      fun w => a w*(∏ i, s i w) := funext (hfactor _)
  have hhybrid (u : D → ℝ) (i : Fin m) :
      finitePopulationWeight (n := n) μ pol d (fun j => if j=i then u else mid) =
      fun w => a w*populationCoinMass μ pol d u w i*
        (∏ j ∈ Finset.univ.erase i, (p j w+s j w)/2) := by
    funext w
    rw [hfactor,← Finset.mul_prod_erase Finset.univ
      (fun j => populationCoinMass μ pol d (if j=i then u else mid) w j) (Finset.mem_univ i)]
    simp only [ite_true]
    rw [← mul_assoc]
    congr 1
    apply Finset.prod_congr rfl
    intro j hj
    rw [if_neg (Finset.mem_erase.mp hj).1,hmass]
  rw [hP,hQ]
  change 1-realFiniteAffinity (fun w => a w*(∏ i, p i w)) (fun w => a w*(∏ i, s i w)) ≤
    ∑ i : Fin m, (1-realFiniteAffinity
      (finitePopulationWeight μ pol d (fun j => if j=i then q else mid))
      (finitePopulationWeight μ pol d (fun j => if j=i then r else mid)))
  simp_rw [hhybrid]
  exact finite_weighted_midpoint_hybrid_decomposition a (fun w => pathValidity_nonneg pol w)
    p s hp hs hnorm

end ThresholdHC.CriticalEntropy
