import ThresholdHC.Tier5.CreationFresh
import ThresholdHC.Tier3.StoppingBase

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace ThresholdHC.Tier5
open ThresholdHC.Tier3

theorem freshTape_coordinate_measurable (n : ℕ) (b : Option Bool) :
    MeasurableSet {z : ℕ × (ℕ → Bool) | freshTape z n = b} :=
  measurableSet_eq_fun ((measurable_pi_apply n).comp measurable_freshTape) measurable_const

theorem fresh_realizes (q : unitInterval) :
    RealizesCreationPrefixes exampleSeedLaw (freshProcessLaw q) Prod.fst freshTape
      freshPolicy (fun _ _ => 1/2) (fun _ _ => (q : ℝ)) := by
  intro n f hf hb
  obtain ⟨C,hC⟩ := hb
  have hm : Measurable (fun z : ℕ × (ℕ → Bool) => f z.1 (processPrefix n (freshTape z))) :=
    measurable_prefix_function Prod.fst freshTape measurable_fst
      freshTape_coordinate_measurable n f hf
  have hi : Integrable (fun z : ℕ × (ℕ → Bool) => f z.1 (processPrefix n (freshTape z)))
      (freshProcessLaw q) := by
    apply (integrable_const C).mono' hm.aestronglyMeasurable
    exact ae_of_all _ (fun z => by simpa only [Real.norm_eq_abs] using hC z.1 _)
  unfold freshProcessLaw at hi ⊢
  rw [integral_prod _ hi]
  apply integral_congr_ae
  filter_upwards [] with N
  change (∫ x, (fun s : Fin (n+1) → Bool =>
    f N (freshTruncatedPrefix N n (Nat.le_succ n) s))
      (fun i : Fin (n+1) => x i.val) ∂freshBitLaw q) = _
  rw [freshBitLaw_integral_prefix q (n+1)
    (fun s => f N (freshTruncatedPrefix N n (Nat.le_succ n) s))]
  exact (fresh_transcript_expect N n (q:ℝ) (f N)).symm

theorem fresh_prefix_work_eq (z : ℕ × (ℕ → Bool)) (n : ℕ) :
    workOf (processPrefix n (freshTape z)) =
      workOf (processPrefix n (exampleTape (z.1, false))) := by
  unfold workOf
  congr 1
  congr 1
  ext i
  by_cases h : i.val < z.1+1 <;> simp [processPrefix, freshTape, exampleTape, h]

theorem fresh_totalWork (z : ℕ × (ℕ → Bool)) :
    totalProcessWork (freshTape z) = (z.1+1 : ℕ) := by
  have heq : totalProcessWork (freshTape z) = totalProcessWork (exampleTape (z.1,false)) := by
    unfold totalProcessWork
    congr 1
    funext n
    rw [fresh_prefix_work_eq]
  rw [heq, example_totalWork]

theorem fresh_finite_expected_work (q : unitInterval) :
    (∫⁻ z, totalProcessWork (freshTape z) ∂freshProcessLaw q) < ∞ := by
  have hi : Integrable (fun z : ℕ × (ℕ → Bool) => ((z.1+1:ℕ):ℝ)) (freshProcessLaw q) :=
    example_seed_work_integrable.comp_fst _
  have hn : (0 : (ℕ × (ℕ → Bool)) → ℝ) ≤ᵐ[freshProcessLaw q]
      (fun z => ((z.1+1:ℕ):ℝ)) := ae_of_all _ (fun _ => by positivity)
  have hf := (hasFiniteIntegral_iff_ofReal hn).1 hi.2
  simpa only [fresh_totalWork, ENNReal.ofReal_natCast] using hf

theorem fresh_unbounded_work (q : unitInterval) (n : ℕ) :
    0 < freshProcessLaw q {z | (n:ℝ≥0∞) < totalProcessWork (freshTape z)} := by
  have hs : ({n} : Set ℕ) ×ˢ (Set.univ : Set (ℕ → Bool)) ⊆
      {z | (n:ℝ≥0∞) < totalProcessWork (freshTape z)} := by
    intro z hz
    have hN : z.1 = n := hz.1
    simp only [Set.mem_ofPred_eq, fresh_totalWork, hN]
    exact_mod_cast Nat.lt_succ_self n
  have hp : (⟨1/2, by constructor <;> norm_num⟩ : unitInterval) ≠ 0 := by
    intro he
    have := congrArg (fun p : unitInterval => (p:ℝ)) he
    norm_num at this
  have hpos : 0 < freshProcessLaw q (({n} : Set ℕ) ×ˢ (Set.univ : Set (ℕ → Bool))) := by
    rw [freshProcessLaw, Measure.prod_prod]
    simp only [measure_univ, mul_one]
    rw [exampleSeedLaw, geometricMeasure_singleton hp]
    apply ENNReal.ofReal_pos.mpr
    norm_num
  exact hpos.trans_le (measure_mono hs)

theorem unbounded_creation_example : UnboundedCreationExampleStatement := by
  let qp : unitInterval := ⟨5/8, by constructor <;> norm_num⟩
  let qm : unitInterval := ⟨3/8, by constructor <;> norm_num⟩
  refine ⟨ℕ × (ℕ → Bool), inferInstance, exampleSeedLaw,
    freshProcessLaw qp, freshProcessLaw qm, Prod.fst, freshTape,
    inferInstance, inferInstance, inferInstance, measurable_fst,
    freshTape_coordinate_measurable, fresh_realizes qp, fresh_realizes qm,
    fresh_finite_expected_work qp, fresh_unbounded_work qp⟩

end ThresholdHC.Tier5
