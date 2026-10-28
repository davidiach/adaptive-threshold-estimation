import ThresholdHC.CriticalEntropy.UniformCoin
import Mathlib.Probability.Distributions.Geometric

noncomputable section
namespace ThresholdHC.BlindUpper
open MeasureTheory ProbabilityTheory ThresholdHC.CriticalEntropy
open scoped ENNReal

/-- Number of failures before the first success; infinite if no mark appears. -/
def firstSuccess (ω : ℕ → Bool) : ℕ∞ := by
  classical
  exact if h : ∃ n, ω n = true then (Nat.find h : ℕ∞) else ⊤

theorem firstSuccess_eq (ω : ℕ → Bool) (n : ℕ) :
    firstSuccess ω = n ↔ ω n = true ∧ ∀ i < n, ω i = false := by
  classical
  unfold firstSuccess
  split_ifs with h
  · simp [Nat.find_eq_iff]
  · simp only [ENat.top_ne_natCast,false_iff]
    intro hn
    exact h ⟨n,hn.1⟩

theorem measurable_firstSuccess : Measurable firstSuccess := by
  apply ENat.measurable_iff.mpr
  intro n
  have h := (measurableSet_eq_fun (measurable_pi_apply n) (measurable_const (a := true))).inter
    (MeasurableSet.iInter (fun i : ℕ => MeasurableSet.iInter (fun _ : i < n =>
      measurableSet_eq_fun (measurable_pi_apply i) (measurable_const (a := false)))))
  convert h using 1
  ext ω
  simp [firstSuccess_eq]

def firstSuccessWord (n : ℕ) (i : Fin (n+1)) : Bool := decide (i.val = n)

theorem firstSuccess_prefix (ω : ℕ → Bool) (n : ℕ) :
    firstSuccess ω = n ↔ Tier2.tapePrefix (n+1) ω = firstSuccessWord n := by
  rw [firstSuccess_eq]
  constructor
  · rintro ⟨hn,hi⟩
    funext i
    by_cases h : i.val = n
    · simp [Tier2.tapePrefix,firstSuccessWord,h,hn]
    · have hil : i.val < n := by omega
      simp [Tier2.tapePrefix,firstSuccessWord,h,hi _ hil]
  · intro h
    constructor
    · have hh := congrFun h ⟨n,Nat.lt_succ_self n⟩
      simpa [Tier2.tapePrefix,firstSuccessWord] using hh
    · intro i hi
      have hh := congrFun h ⟨i,lt_trans hi (Nat.lt_succ_self n)⟩
      simpa [Tier2.tapePrefix,firstSuccessWord,ne_of_lt hi] using hh

theorem firstSuccessWord_probability (p : ℝ) (n : ℕ) :
    streamProb p (firstSuccessWord n) = (1-p)^n*p := by
  unfold streamProb
  rw [Fin.prod_univ_castSucc]
  have he (i : Fin n) : firstSuccessWord n i.castSucc = false := by
    simp [firstSuccessWord,ne_of_lt i.isLt]
  have hl : firstSuccessWord n (Fin.last n) = true := by simp [firstSuccessWord]
  simp only [he,hl,Bool.false_eq_true,ite_false,ite_true,Finset.prod_const,
    Finset.card_univ,Fintype.card_fin]

theorem firstSuccess_probability (p : unitInterval) (n : ℕ) :
    Tier2.tapeMeasure p {ω | firstSuccess ω = n} = ENNReal.ofReal ((1-(p : ℝ))^n*(p : ℝ)) := by
  have he : {ω | firstSuccess ω = n} =
      Tier2.tapePrefix (n+1) ⁻¹' {firstSuccessWord n} := by
    ext ω; exact firstSuccess_prefix ω n
  have hm : Measurable (Tier2.tapePrefix (n+1)) :=
    Measurable.of_eval (fun i => measurable_pi_apply i.val)
  rw [he,← Measure.map_apply hm
    (measurableSet_singleton _),Tier2.prefix_map]
  calc
    _ = ENNReal.ofReal ((Tier2.finiteMeasure p (n+1)).real {firstSuccessWord n}) :=
      (ENNReal.ofReal_toReal (measure_ne_top _ _)).symm
    _ = _ := by rw [Tier2.finiteMeasure_real_singleton,firstSuccessWord_probability]


theorem firstSuccess_ae_finite (p : unitInterval) (hp : p ≠ 0) :
    ∀ᵐ ω ∂Tier2.tapeMeasure p, firstSuccess ω ≠ ⊤ := by
  let E (n : ℕ) : Set (ℕ → Bool) := {ω | firstSuccess ω = n}
  have hE (n : ℕ) : MeasurableSet (E n) :=
    measurableSet_eq_fun measurable_firstSuccess measurable_const
  have hdis : Pairwise (fun i j => Disjoint (E i) (E j)) := by
    intro i j hij
    apply Set.disjoint_left.mpr
    intro ω hi hj
    exact hij (ENat.natCast_inj.mp (hi.symm.trans hj))
  have he : (⋃ n, E n) = {ω | firstSuccess ω ≠ ⊤} := by
    ext ω
    simp only [Set.mem_iUnion,Set.mem_ofPred_eq,E]
    constructor
    · rintro ⟨n,hn⟩; rw [hn]; exact ENat.natCast_ne_top n
    · intro h
      obtain ⟨n,hn⟩ := ENat.ne_top_iff_exists.mp h
      exact ⟨n,hn.symm⟩
  have hmass : Tier2.tapeMeasure p (⋃ n, E n) = 1 := by
    rw [measure_iUnion hdis hE]
    simp_rw [E,firstSuccess_probability]
    rw [← ENNReal.ofReal_tsum_of_nonneg (geometricMeasure_nonneg p)
      (hasSum_one_geometricMeasure hp).summable,(hasSum_one_geometricMeasure hp).tsum_eq]
    simp
  apply (mem_ae_iff_prob_eq_one (measurable_firstSuccess (measurableSet_singleton (⊤ : ℕ∞))).compl).mpr
  change Tier2.tapeMeasure p {ω | firstSuccess ω ≠ ⊤} = 1
  rw [← he]
  exact hmass

theorem firstSuccess_nat_map (p : unitInterval) (hp : p ≠ 0) :
    (Tier2.tapeMeasure p).map (fun ω => (firstSuccess ω).toNat) = geometricMeasure p := by
  apply Measure.ext_of_singleton
  intro n
  have hm : Measurable (fun ω => (firstSuccess ω).toNat) :=
    (measurable_of_countable ENat.toNat).comp measurable_firstSuccess
  rw [Measure.map_apply hm (measurableSet_singleton n),geometricMeasure_singleton hp]
  calc
    _ = Tier2.tapeMeasure p {ω | firstSuccess ω = n} := by
      apply measure_congr
      filter_upwards [firstSuccess_ae_finite p hp] with ω hω
      obtain ⟨m,hm⟩ := ENat.ne_top_iff_exists.mp hω
      simp [← hm]
    _ = _ := firstSuccess_probability p n


end ThresholdHC.BlindUpper
