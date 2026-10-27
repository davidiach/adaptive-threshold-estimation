import ThresholdHC.CriticalEntropy.CriticalCommonPair

noncomputable section

open MeasureTheory Set
open scoped ENNReal
namespace ThresholdHC.CriticalEntropy

theorem hellingerAffinity_finite {I : Type} [Fintype I]
    [MeasurableSpace I] [MeasurableSingletonClass I]
    (P Q : Measure I) [IsFiniteMeasure P] [IsFiniteMeasure Q] :
    hellingerAffinity P Q = finiteAffinity (fun i => P {i}) (fun i => Q {i}) := by
  have hP : P ≪ P+Q := Measure.AbsolutelyContinuous.rfl.add_right Q
  have hQ : Q ≪ P+Q := Measure.AbsolutelyContinuous.rfl.add_right' P
  unfold hellingerAffinity finiteAffinity
  rw [lintegral_fintype]
  apply Finset.sum_congr rfl
  intro i hi
  have hp := Measure.setLIntegral_rnDeriv hP ({i} : Set I)
  have hq := Measure.setLIntegral_rnDeriv hQ ({i} : Set I)
  rw [lintegral_singleton] at hp hq
  dsimp only
  rw [← hp, ← hq]
  exact (affinity_mass_scaling _ _ _).symm

theorem lintegral_sqrt_product_le {Ω : Type} [MeasurableSpace Ω]
    (ξ : Measure Ω) (f g : Ω → ℝ≥0∞)
    (hf : AEMeasurable f ξ) (hg : AEMeasurable g ξ) :
    (∫⁻ z, (f z*g z)^(1/2 : ℝ) ∂ξ) ≤
      ((∫⁻ z, f z ∂ξ)*(∫⁻ z, g z ∂ξ))^(1/2 : ℝ) := by
  have hpq : (2 : ℝ).HolderConjugate 2 := by norm_num [Real.holderConjugate_iff]
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq ξ hpq
    (hf.pow_const (1/2 : ℝ)) (hg.pow_const (1/2 : ℝ))
  have hs (a : ℝ≥0∞) : (a^(1/2 : ℝ))^(2 : ℝ) = a := by
    rw [← ENNReal.rpow_mul]
    norm_num
  simp only [Pi.mul_apply,hs] at h
  simp_rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 1/2)]
  exact h

/-- Finite-output data processing, with an arbitrary measurable input space. -/
theorem hellingerAffinity_map_finite {Ω I : Type} [MeasurableSpace Ω]
    [Fintype I] [MeasurableSpace I] [MeasurableSingletonClass I]
    (P Q : Measure Ω) [IsFiniteMeasure P] [IsFiniteMeasure Q]
    (F : Ω → I) (hF : Measurable F) :
    hellingerAffinity P Q ≤ hellingerAffinity (P.map F) (Q.map F) := by
  classical
  have hP : P ≪ P+Q := Measure.AbsolutelyContinuous.rfl.add_right Q
  have hQ : Q ≪ P+Q := Measure.AbsolutelyContinuous.rfl.add_right' P
  let s (i : I) := F ⁻¹' {i}
  have hsm (i : I) : MeasurableSet (s i) := hF (measurableSet_singleton i)
  have hdis : Pairwise (fun i j => Disjoint (s i) (s j)) := by
    intro i j hij
    exact Set.disjoint_left.mpr (fun x hi hj => hij (hi.symm.trans hj))
  have hunion : (⋃ i, s i) = Set.univ := by
    ext x
    simp [s]
  unfold hellingerAffinity
  rw [← setLIntegral_univ (μ := P+Q), ← hunion, lintegral_iUnion hsm hdis,
    tsum_fintype]
  change _ ≤ hellingerAffinity (P.map F) (Q.map F)
  rw [hellingerAffinity_finite,finiteAffinity]
  apply Finset.sum_le_sum
  intro i hi
  have h := lintegral_sqrt_product_le ((P+Q).restrict (s i))
    (P.rnDeriv (P+Q)) (Q.rnDeriv (P+Q))
    (Measure.measurable_rnDeriv _ _).aemeasurable (Measure.measurable_rnDeriv _ _).aemeasurable
  rw [Measure.setLIntegral_rnDeriv hP (s i),Measure.setLIntegral_rnDeriv hQ (s i)] at h
  simpa only [Measure.map_apply hF (measurableSet_singleton i),s] using h

theorem hellingerAffinity_probability_le_one {Ω : Type} [MeasurableSpace Ω]
    (P Q : Measure Ω) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] :
    hellingerAffinity P Q ≤ 1 := by
  have hP : P ≪ P+Q := Measure.AbsolutelyContinuous.rfl.add_right Q
  have hQ : Q ≪ P+Q := Measure.AbsolutelyContinuous.rfl.add_right' P
  have h := lintegral_sqrt_product_le (P+Q) (P.rnDeriv (P+Q)) (Q.rnDeriv (P+Q))
    (Measure.measurable_rnDeriv _ _).aemeasurable (Measure.measurable_rnDeriv _ _).aemeasurable
  rw [Measure.lintegral_rnDeriv hP,Measure.lintegral_rnDeriv hQ] at h
  simpa only [hellingerAffinity,measure_univ,mul_one,ENNReal.one_rpow] using h

theorem finiteWeightMeasure_finite {I : Type} [Fintype I]
    [MeasurableSpace I] (p : I → ℝ) : IsFiniteMeasure (finiteWeightMeasure p) := by
  classical
  constructor
  simp [finiteWeightMeasure, ENNReal.sum_lt_top]

theorem finiteWeightMeasure_affinity {I : Type} [Fintype I]
    [MeasurableSpace I] [MeasurableSingletonClass I]
    (p q : I → ℝ) (hp : ∀ i, 0 ≤ p i) (hq : ∀ i, 0 ≤ q i) :
    (hellingerAffinity (finiteWeightMeasure p) (finiteWeightMeasure q)).toReal =
      realFiniteAffinity p q := by
  let : IsFiniteMeasure (finiteWeightMeasure p) := finiteWeightMeasure_finite p
  let : IsFiniteMeasure (finiteWeightMeasure q) := finiteWeightMeasure_finite q
  rw [hellingerAffinity_finite,finiteAffinity_toReal _ _
    (fun i => measure_ne_top _ _) (fun i => measure_ne_top _ _)]
  simp only [finiteWeightMeasure_singleton,ENNReal.toReal_ofReal,hp,hq]

end ThresholdHC.CriticalEntropy

open MeasureTheory Set
open scoped ENNReal
namespace ThresholdHC.CriticalEntropy

/-- Densities may vanish simultaneously, as they do on impossible transcripts. -/
theorem hellingerAffinity_withDensity_nonnegative {Ω : Type} [MeasurableSpace Ω]
    (ξ : Measure Ω) [SigmaFinite ξ] (f g : Ω → ℝ≥0∞)
    (hf : Measurable f) (hg : Measurable g)
    (hf_top : ∀ x, f x ≠ ∞) (hg_top : ∀ x, g x ≠ ∞) :
    hellingerAffinity (ξ.withDensity f) (ξ.withDensity g) =
      ∫⁻ z, (f z*g z)^(1/2 : ℝ) ∂ξ := by
  let P := ξ.withDensity f
  let Q := ξ.withDensity g
  let : SigmaFinite P := SigmaFinite.withDensity_of_ne_top' hf_top
  let : SigmaFinite Q := SigmaFinite.withDensity_of_ne_top' hg_top
  have hP : P ≪ P+Q := Measure.AbsolutelyContinuous.rfl.add_right Q
  have hQ : Q ≪ P+Q := Measure.AbsolutelyContinuous.rfl.add_right' P
  have hs : P+Q = ξ.withDensity (f+g) := (withDensity_add_left hf g).symm
  have hpf : P.rnDeriv ξ =ᵐ[ξ] f := Measure.rnDeriv_withDensity ξ hf
  have hqg : Q.rnDeriv ξ =ᵐ[ξ] g := Measure.rnDeriv_withDensity ξ hg
  have hsum : (P+Q).rnDeriv ξ =ᵐ[ξ] f+g := by
    rw [hs]
    exact Measure.rnDeriv_withDensity ξ (hf.add hg)
  have hpc := Measure.rnDeriv_mul_rnDeriv (κ := ξ) hP
  have hqc := Measure.rnDeriv_mul_rnDeriv (κ := ξ) hQ
  change (∫⁻ z, (P.rnDeriv (P+Q) z*Q.rnDeriv (P+Q) z)^(1/2 : ℝ) ∂(P+Q)) = _
  rw [hs,lintegral_withDensity_eq_lintegral_mul ξ (hf.add hg) (by fun_prop)]
  apply lintegral_congr_ae
  filter_upwards [hpc,hqc,hpf,hqg,hsum] with z hp hq hpf hqg hsum
  dsimp only [Pi.mul_apply,Pi.add_apply] at *
  rw [← hs]
  have hp' : P.rnDeriv (P+Q) z*(f z+g z) = f z := by simpa [hsum,hpf] using hp
  have hq' : Q.rnDeriv (P+Q) z*(f z+g z) = g z := by simpa [hsum,hqg] using hq
  rw [mul_comm,← affinity_mass_scaling, hp',hq']

theorem hellingerAffinity_revealed_finite {R I : Type} [MeasurableSpace R]
    [Fintype I] [MeasurableSpace I] [MeasurableSingletonClass I]
    (ν : Measure R) [SigmaFinite ν] (f g : R × I → ℝ≥0∞)
    (hf : Measurable f) (hg : Measurable g)
    (hf_top : ∀ x, f x ≠ ∞) (hg_top : ∀ x, g x ≠ ∞) :
    hellingerAffinity ((ν.prod Measure.count).withDensity f)
      ((ν.prod Measure.count).withDensity g) =
      ∫⁻ r, finiteAffinity (fun i => f (r,i)) (fun i => g (r,i)) ∂ν := by
  rw [hellingerAffinity_withDensity_nonnegative _ f g hf hg hf_top hg_top,
    lintegral_prod _ (by fun_prop)]
  apply lintegral_congr
  intro r
  simp [lintegral_fintype,finiteAffinity]

end ThresholdHC.CriticalEntropy
namespace ThresholdHC.CriticalEntropy
open MeasureTheory ProbabilityTheory Set

def cappedOutput {R E : Type} [MeasurableSpace R] [MeasurableSpace E]
    (A : StoppedProcedure R E) (m : ℕ) (z : R × CappedWord m) : E :=
  A.output (z.1,completePrefix z.2.1.val z.2.2)

theorem measurable_cappedOutput {R E : Type} [MeasurableSpace R] [MeasurableSpace E]
    (A : StoppedProcedure R E) (m : ℕ) : Measurable (cappedOutput A m) :=
  A.measurable_output.comp (measurable_fst.prodMk
    ((measurable_of_countable (fun w : CappedWord m => completePrefix w.1.val w.2)).comp
      measurable_snd))

theorem cappedOutput_cappedTranscript {R E : Type} [MeasurableSpace R] [MeasurableSpace E]
    (A : StoppedProcedure R E) (m : ℕ) (hcap : ∀ z, A.stop z ≤ m)
    (z : R × (ℕ → Bool)) : cappedOutput A m (cappedTranscript A m z) = A.output z := by
  have hfin : A.stop z ≠ ⊤ := ne_top_of_le_ne_top (by simp) (hcap z)
  obtain ⟨k,hk⟩ := ENat.ne_top_iff_exists.mp hfin
  have hkm : k ≤ m := by
    have h := hcap z
    rw [← hk] at h
    exact_mod_cast h
  rw [cappedTranscript_of_stop A m k hkm z hk.symm]
  exact (stopped_prefix_ext A z.1 z.2 (completePrefix k (Tier2.tapePrefix k z.2)) k
    (tapePrefix_completePrefix k (Tier2.tapePrefix k z.2)).symm hk.symm).2

theorem cappedOutput_map {R E : Type} [MeasurableSpace R] [MeasurableSpace E]
    (A : StoppedProcedure R E) (m : ℕ) (hcap : ∀ z, A.stop z ≤ m)
    (P : Measure (R × (ℕ → Bool))) :
    (P.map (cappedTranscript A m)).map (cappedOutput A m) = P.map A.output := by
  rw [Measure.map_map (measurable_cappedOutput A m) (measurable_cappedTranscript A m)]
  congr 1
  funext z
  exact cappedOutput_cappedTranscript A m hcap z

theorem cappedOutput_affinity {R E : Type} [MeasurableSpace R] [Fintype E]
    [MeasurableSpace E] [MeasurableSingletonClass E]
    (A : StoppedProcedure R E) (m : ℕ) (hcap : ∀ z, A.stop z ≤ m)
    (P Q : Measure (R × (ℕ → Bool))) [IsFiniteMeasure P] [IsFiniteMeasure Q] :
    hellingerAffinity (P.map (cappedTranscript A m)) (Q.map (cappedTranscript A m)) ≤
      hellingerAffinity (P.map A.output) (Q.map A.output) := by
  have h := hellingerAffinity_map_finite (P.map (cappedTranscript A m))
    (Q.map (cappedTranscript A m)) (cappedOutput A m) (measurable_cappedOutput A m)
  simpa only [cappedOutput_map A m hcap] using h

end ThresholdHC.CriticalEntropy
