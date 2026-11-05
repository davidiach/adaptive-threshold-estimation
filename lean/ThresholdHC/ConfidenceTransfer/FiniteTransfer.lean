import ThresholdHC.ConfidenceTransfer.Hybrid
import ThresholdHC.ConfidenceTransfer.Quarter
import ThresholdHC.CriticalEntropy.PopulationTransfer

noncomputable section
open MeasureTheory InformationTheory
open scoped ENNReal NNReal
namespace ThresholdHC.ConfidenceTransfer
open ThresholdHC.CriticalEntropy

local instance : MeasurableSpace (Option Bool) := ⊤
local instance : MeasurableSingletonClass (Option Bool) := ⟨fun _ => trivial⟩

/-- Apply a quarter mixture to a single physical slot, conditional on the fixed
laws of all the other slots. -/
private theorem one_slot_quarter {D : Type} [MeasurableSpace D] {m n : ℕ}
    (μ : Measure D) [IsProbabilityMeasure μ] (pol : List Bool → Option (Fin m))
    (d q r s : D → ℝ) (hdm : Measurable d) (hqm : Measurable q) (hrm : Measurable r)
    (hsm : Measurable s) (hd : ∀ x, 0 ≤ d x ∧ d x ≤ 1/2)
    (hq : ∀ x, 0 ≤ q x ∧ q x ≤ 1) (hr : ∀ x, 0 ≤ r x ∧ r x ≤ 1)
    (hs : ∀ x, 0 ≤ s x ∧ s x ≤ 1) (i : Fin m) :
    let H := fun u => finiteWeightMeasure (finitePopulationWeight (n := n) μ pol d
      (fun j => if j=i then u else s))
    H (fun x => (3*q x+r x)/4) = quarterMix (H q) (H r) := by
  classical
  let v (u : D → ℝ) (w : Fin n → Option Bool) :=
    finitePopulationWeight μ pol d (fun j => if j=i then u else s) w
  have hnon (u : D → ℝ) (hu : Measurable u) (hU : ∀ x, 0 ≤ u x ∧ u x ≤ 1) (w) :
      0 ≤ v u w := (finite_population_total μ pol d _ hdm
        (fun j => by split <;> assumption) hd (fun j x => by split <;> first | exact hU x | exact hs x)).1 w
  have fac (u : D → ℝ) (w : Fin n → Option Bool) :
      v u w = ThresholdHC.Proofs.pathValidity pol w * populationCoinMass μ pol d u w i *
        ∏ j ∈ Finset.univ.erase i, populationCoinMass μ pol d s w j := by
    change finitePopulationWeight μ pol d (fun j => if j=i then u else s) w = _
    rw [finite_population_factor]
    change ThresholdHC.Proofs.pathValidity pol w * (∏ j, populationCoinMass μ pol d
      (if j=i then u else s) w j) = _
    rw [← Finset.mul_prod_erase Finset.univ
      (fun j => populationCoinMass μ pol d (if j=i then u else s) w j) (Finset.mem_univ i)]
    simp only [ite_true]
    rw [← mul_assoc]
    congr 1
    apply Finset.prod_congr rfl
    intro j hj
    rw [ite_eq_right (Finset.mem_erase.mp hj).1]
  apply Measure.ext_of_singleton
  intro w
  change finiteWeightMeasure (v _) {w} = quarterMix (finiteWeightMeasure (v q)) (finiteWeightMeasure (v r)) {w}
  rw [quarterMix,Measure.add_apply,Measure.smul_apply,Measure.smul_apply]
  simp only [finiteWeightMeasure_singleton, ENNReal.smul_def,smul_eq_mul]
  have hh : v (fun x => (3*q x+r x)/4) w = 3/4 * v q w + 1/4 * v r w := by
    simp only [fac,quarter_coin_mass μ pol d q r hdm hqm hrm hd hq hr]
    ring
  rw [hh,ENNReal.ofReal_add (mul_nonneg (by norm_num) (hnon q hqm hq w))
    (mul_nonneg (by norm_num) (hnon r hrm hr w)),ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 3/4),
    ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 1/4)]
  norm_num [ENNReal.ofReal_div_of_pos]

/-- Mixture of two conditional sign probabilities for one coin. -/
def quarterPrior {D : Type} (q r : D → unitInterval) (x : D) : unitInterval :=
  ⟨(3*(q x : ℝ)+(r x : ℝ))/4, by
    constructor <;> linarith [(q x).property.1,(q x).property.2,(r x).property.1,(r x).property.2]⟩

theorem measurable_quarterPrior {D : Type} [MeasurableSpace D] (q r : D → unitInterval)
    (hq : Measurable q) (hr : Measurable r) : Measurable (quarterPrior q r) := by
  unfold quarterPrior
  fun_prop


/-- Charge local Hellinger loss to the actual reference population of the finite hybrid. -/
theorem finite_reference_work_kl {D : Type} [MeasurableSpace D] {m n : ℕ}
    (μ : Measure D) [IsProbabilityMeasure μ] (p₀ p₁ q r : D → unitInterval)
    (h₀ : Measurable p₀) (h₁ : Measurable p₁) (hq : Measurable q) (hr : Measurable r)
    (d : D → ℝ) (hdm : Measurable d) (hd : ∀ x, 0 ≤ d x ∧ d x ≤ 1/2)
    (h₀d : ∀ᵐ x ∂μ, (p₀ x : ℝ) = 1/2-d x) (h₁d : ∀ᵐ x ∂μ, (p₁ x : ℝ) = 1/2+d x)
    (pol : List Bool → Option (Fin m)) (κ : ℝ) (hκ : 0 ≤ κ)
    (hbound : let ν := Measure.pi (fun _ : Fin m =>
        parameterTapeLaw (populationParameterLaw μ p₀ p₁ (quarterPrior q r)))
      ∀ i : Fin m, 1-(hellingerAffinity
        (cappedTranscriptLaw μ ν p₀ p₁ q (localSimulationProcedure i n pol) n)
        (cappedTranscriptLaw μ ν p₀ p₁ r (localSimulationProcedure i n pol) n)).toReal ≤
        κ*(populationExpectedWork μ ν p₀ p₁ (quarterPrior q r) (localSimulationProcedure i n pol)).toReal) :
    let W := fun u => finiteWeightMeasure (finitePopulationWeight (n := n) μ pol d u)
    klDiv (W (fun _ x => (quarterPrior q r x : ℝ))) (W (fun _ x => (quarterPrior r q x : ℝ))) ≤
      ENNReal.ofReal ((8/3)*κ*(finitePopulationExpectedWork μ p₀ p₁ (quarterPrior q r) pol n).toReal) := by
  classical
  let s := quarterPrior q r
  let t := quarterPrior r q
  have hs : Measurable s := measurable_quarterPrior q r hq hr
  let : IsProbabilityMeasure (populationParameterLaw μ p₀ p₁ s) :=
    populationParameterLaw_probability μ p₀ p₁ s h₀ h₁ hs
  let ν := Measure.pi (fun _ : Fin m => parameterTapeLaw (populationParameterLaw μ p₀ p₁ s))
  let W := fun (u : Fin m → D → ℝ) => finiteWeightMeasure (finitePopulationWeight (n := n) μ pol d u)
  let V := fun (i : Fin m) (u : D → unitInterval) =>
    finitePopulationWeight (n := n) μ pol d (fun j x => if j=i then (u x : ℝ) else (s x : ℝ))
  let H := fun i u => finiteWeightMeasure (V i u)
  have veq (i : Fin m) (u : D → unitInterval) :
      (fun j x => if j=i then (u x : ℝ) else (s x : ℝ)) =
        (fun j => if j=i then (fun x => (u x : ℝ)) else fun x => (s x : ℝ)) := by
    funext j x; split <;> simp_all
  have hmix (i) (u v : D → unitInterval) (hu : Measurable u) (hv : Measurable v) :
      H i (quarterPrior u v) = quarterMix (H i u) (H i v) := by
    simp only [H,V,veq]
    exact one_slot_quarter μ pol d _ _ _ hdm (measurable_subtype_coe.comp hu)
      (measurable_subtype_coe.comp hv) (measurable_subtype_coe.comp hs) hd
      (fun x => (u x).property) (fun x => (v x).property) (fun x => (s x).property) i
  have htotal (i) (u : D → unitInterval) (hu : Measurable u) :
      (∀ w, 0 ≤ V i u w) ∧ ∑ w, V i u w = 1 := by
    refine finite_population_total μ pol d _ hdm ?_ hd ?_
    · intro j; by_cases h : j=i <;> simp only [h,ite_true,ite_false]
      all_goals exact measurable_subtype_coe.comp (by assumption)
    · intro j x; split <;> first | exact (u x).property | exact (s x).property
  let work (i : Fin m) := populationExpectedWork μ ν p₀ p₁ s (localSimulationProcedure i n pol)
  have step (i : Fin m) : klDiv (H i s) (H i t) ≤ ENNReal.ofReal ((8/3)*κ*(work i).toReal) := by
    let : IsProbabilityMeasure (H i q) := finiteWeightMeasure_probability _ (htotal i q hq).1 (htotal i q hq).2
    let : IsProbabilityMeasure (H i r) := finiteWeightMeasure_probability _ (htotal i r hr).1 (htotal i r hr).2
    rw [hmix i q r hq hr,hmix i r q hr hq]
    apply (quarter_smoothing (H i q) (H i r)).trans
    apply ENNReal.ofReal_le_ofReal
    have hA := localSimulation_affinity_le μ p₀ p₁ q r s h₀ h₁ hq hr hs d hdm hd h₀d h₁d pol i (n := n)
    have hK := (sub_le_sub_left hA 1).trans (hbound i)
    change 1 - realFiniteAffinity (V i q) (V i r) ≤ _ at hK
    change 8/3 * (1 - (hellingerAffinity (finiteWeightMeasure (V i q)) (finiteWeightMeasure (V i r))).toReal) ≤ _
    rw [finiteWeightMeasure_affinity _ _ (htotal i q hq).1 (htotal i r hr).1]
    exact mul_le_mul_of_nonneg_left hK (by norm_num : (0:ℝ) ≤ 8/3) |>.trans_eq (by ring)
  have hhy := quarter_population_hybrid_kl μ pol d (fun x => (q x : ℝ)) (fun x => (r x : ℝ))
    hdm (measurable_subtype_coe.comp hq) (measurable_subtype_coe.comp hr) hd
    (fun x => (q x).property) (fun x => (r x).property) (n := n)
  change klDiv (W (fun _ x => (s x : ℝ))) (W (fun _ x => (t x : ℝ))) ≤ _
  change klDiv (W (fun _ x => (s x : ℝ))) (W (fun _ x => (t x : ℝ))) =
    ∑ i : Fin m, klDiv (W (fun _ x => (s x : ℝ))) (W (fun j => if j=i then
      (fun x => (t x : ℝ)) else fun x => (s x : ℝ))) at hhy
  rw [hhy]
  calc
    _ = ∑ i : Fin m, klDiv (H i s) (H i t) := by
      apply Finset.sum_congr rfl
      intro i _
      simp only [H,V,veq,ite_self]
      rfl
    _ ≤ ∑ i : Fin m, ENNReal.ofReal ((8/3)*κ*(work i).toReal) := Finset.sum_le_sum fun i _ => step i
    _ = _ := by
      rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => by positivity),← Finset.mul_sum]
      congr 2
      exact population_localSimulation_total_work_real μ p₀ p₁ s h₀ h₁ hs pol

theorem null_local_work_comparison {D R E : Type} [MeasurableSpace D] [MeasurableSpace R] [MeasurableSpace E]
    (μ : Measure D) [IsProbabilityMeasure μ] (ν : Measure R) [IsProbabilityMeasure ν]
    (p₀ p₁ q r : D → unitInterval) (h₀ : Measurable p₀) (h₁ : Measurable p₁)
    (hq : Measurable q) (hr : Measurable r) (hqhalf : ∀ x, (q x : ℝ) ≤ 1/2)
    (hrhalf : ∀ x, (r x : ℝ) ≤ 1/2) (A : StoppedProcedure R E) (n : ℕ) (hn : ∀ z, A.stop z ≤ n) :
    (populationExpectedWork μ ν p₀ p₁ (fun _ => 0) A).toReal ≤
      2*(populationExpectedWork μ ν p₀ p₁ (quarterPrior q r) A).toReal := by
  let s := quarterPrior q r
  have hs := measurable_quarterPrior q r hq hr
  have hhalf (x) : (s x : ℝ) ≤ 1/2 := by
    change (3*(q x : ℝ)+(r x : ℝ))/4 ≤ 1/2
    linarith [hqhalf x,hrhalf x]
  have hW := null_work_le_twice_population_work μ ν p₀ p₁ s h₀ h₁ hs hhalf A
  have hfin : populationExpectedWork μ ν p₀ p₁ s A ≠ ∞ := ne_top_of_le_ne_top (by simp)
    (population_capped_work_le μ ν p₀ p₁ s A n hn)
  have h := ENNReal.toReal_mono (ENNReal.mul_ne_top (by norm_num) hfin) hW
  simpa only [ENNReal.toReal_mul,ENNReal.toReal_ofNat] using h

theorem finite_null_work_kl {D : Type} [MeasurableSpace D] {m n : ℕ}
    (μ : Measure D) [IsProbabilityMeasure μ] (p₀ p₁ q r : D → unitInterval)
    (h₀ : Measurable p₀) (h₁ : Measurable p₁) (hq : Measurable q) (hr : Measurable r)
    (hqhalf : ∀ x, (q x : ℝ) ≤ 1/2) (hrhalf : ∀ x, (r x : ℝ) ≤ 1/2)
    (d : D → ℝ) (hdm : Measurable d) (hd : ∀ x, 0 ≤ d x ∧ d x ≤ 1/2)
    (h₀d : ∀ᵐ x ∂μ, (p₀ x : ℝ) = 1/2-d x) (h₁d : ∀ᵐ x ∂μ, (p₁ x : ℝ) = 1/2+d x)
    (pol : List Bool → Option (Fin m)) (κ : ℝ) (hκ : 0 ≤ κ)
    (hbound : let ν := Measure.pi (fun _ : Fin m =>
        parameterTapeLaw (populationParameterLaw μ p₀ p₁ (quarterPrior q r)))
      ∀ i : Fin m, 1-(hellingerAffinity
        (cappedTranscriptLaw μ ν p₀ p₁ q (localSimulationProcedure i n pol) n)
        (cappedTranscriptLaw μ ν p₀ p₁ r (localSimulationProcedure i n pol) n)).toReal ≤
        κ*(populationExpectedWork μ ν p₀ p₁ (fun _ => 0) (localSimulationProcedure i n pol)).toReal) :
    let W := fun u => finiteWeightMeasure (finitePopulationWeight (n := n) μ pol d u)
    klDiv (W (fun _ x => (quarterPrior q r x : ℝ))) (W (fun _ x => (quarterPrior r q x : ℝ))) ≤
      ENNReal.ofReal ((16/3)*κ*(finitePopulationExpectedWork μ p₀ p₁ (quarterPrior q r) pol n).toReal) := by
  let s := quarterPrior q r
  let _ := populationParameterLaw_probability μ p₀ p₁ s h₀ h₁ (measurable_quarterPrior _ _ hq hr)
  let ν := Measure.pi (fun _ : Fin m => parameterTapeLaw (populationParameterLaw μ p₀ p₁ s))
  have h := finite_reference_work_kl μ p₀ p₁ q r h₀ h₁ hq hr d hdm hd h₀d h₁d pol (2*κ)
    (by positivity) (n := n) (fun i => (hbound i).trans (by
      have hc := null_local_work_comparison μ ν p₀ p₁ q r h₀ h₁ hq hr hqhalf hrhalf
        (localSimulationProcedure i n pol) n (localSimulationProcedure_capped i n pol)
      nlinarith only [mul_le_mul_of_nonneg_left hc hκ]))
  rw [show (16/3:ℝ)*κ = (8/3)*(2*κ) by ring]
  exact h

end ThresholdHC.ConfidenceTransfer
