import ThresholdHC.CriticalEntropy.SelectedPolicy

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace ThresholdHC.CriticalEntropy

/-- Enlarging a genuine stopping cap only embeds the finite statistic. -/
def statisticCapEmbedding {m M : ℕ} (h : m ≤ M) :
    Fin (m+1) × Fin (m+1) → Fin (M+1) × Fin (M+1) :=
  Prod.map (Fin.castLE (Nat.add_le_add_right h 1))
    (Fin.castLE (Nat.add_le_add_right h 1))

theorem statisticCapEmbedding_injective {m M : ℕ} (h : m ≤ M) :
    Function.Injective (statisticCapEmbedding h) := by
  intro x y he
  apply Prod.ext
  · apply Fin.ext
    exact congrArg (fun z => z.1.val) he
  · apply Fin.ext
    exact congrArg (fun z => z.2.val) he

theorem stoppedStatistic_enlarge_cap {R E : Type}
    [MeasurableSpace R] [MeasurableSpace E]
    (A : StoppedProcedure R E) {m M : ℕ} (h : m ≤ M)
    (z : R × (ℕ → Bool)) (hcap : A.stop z ≤ m) :
    stoppedStatistic M (cappedTranscript A M z).2 =
      statisticCapEmbedding h (stoppedStatistic m (cappedTranscript A m z).2) := by
  have hfin : A.stop z ≠ ⊤ := ne_top_of_le_ne_top (by simp) hcap
  have hn : (A.stop z).toNat ≤ m := by
    simpa using ENat.toNat_le_toNat hcap (by simp)
  have he : A.stop z = ((A.stop z).toNat : ℕ∞) := (ENat.natCast_toNat hfin).symm
  rw [cappedTranscript_of_stop A M _ (hn.trans h) z he,
    cappedTranscript_of_stop A m _ hn z he]
  apply Prod.ext <;> apply Fin.ext <;> rfl

theorem cappedStatisticLaw_enlarge_cap {D R E : Type}
    [MeasurableSpace D] [MeasurableSpace R] [MeasurableSpace E]
    (μ : Measure D) (ν : Measure R) (p₀ p₁ q : D → unitInterval)
    (h₀ : Measurable p₀) (h₁ : Measurable p₁) (hq : Measurable q)
    (A : StoppedProcedure R E) {m M : ℕ} (h : m ≤ M)
    (hcap : ∀ z, A.stop z ≤ m) :
    cappedStatisticLaw μ ν p₀ p₁ q A M =
      (cappedStatisticLaw μ ν p₀ p₁ q A m).map (statisticCapEmbedding h) := by
  have hT (k : ℕ) : Measurable (fun z : R × CappedWord k => stoppedStatistic k z.2) :=
    (measurable_of_countable (stoppedStatistic k)).comp measurable_snd
  have hP (k : ℕ) : Measurable (cappedTranscript A k ∘ populationInput p₀ p₁ q) :=
    (measurable_cappedTranscript A k).comp (measurable_populationInput p₀ p₁ q h₀ h₁ hq)
  unfold cappedStatisticLaw cappedTranscriptLaw
  rw [Measure.map_map (hT M) (hP M),Measure.map_map (hT m) (hP m),
    Measure.map_map (measurable_of_countable _) ((hT m).comp (hP m))]
  congr 1
  funext z
  exact stoppedStatistic_enlarge_cap A h _ (hcap _)

theorem realFiniteAffinity_map_injective {I J : Type} [Fintype I] [Fintype J]
    [MeasurableSpace I] [MeasurableSingletonClass I]
    [MeasurableSpace J] [MeasurableSingletonClass J]
    (μ ν : Measure I) (f : I → J) (hf : Function.Injective f) :
    realFiniteAffinity (fun j => (μ.map f).real {j}) (fun j => (ν.map f).real {j}) =
      realFiniteAffinity (fun i => μ.real {i}) (fun i => ν.real {i}) := by
  classical
  have hm (η : Measure I) (i : I) : (η.map f).real {f i} = η.real {i} := by
    have he : f ⁻¹' {f i} = {i} := by
      ext j
      simp [hf.eq_iff]
    rw [measureReal_def,Measure.map_apply (measurable_of_countable f) (measurableSet_singleton _)]
    rw [he]
    rfl
  have hz (η : Measure I) (j : J) (hj : j ∉ Set.range f) : (η.map f).real {j} = 0 := by
    have he : f ⁻¹' {j} = ∅ := by
      ext i
      simp only [mem_preimage,mem_singleton_iff,mem_empty_iff_false,iff_false]
      exact fun hi => hj ⟨i,hi⟩
    rw [measureReal_def,Measure.map_apply (measurable_of_countable f) (measurableSet_singleton _),he]
    simp
  unfold realFiniteAffinity
  exact (Fintype.sum_of_injective f hf _ _
    (fun j hj => by dsimp only; rw [hz μ j hj]; simp)
    (fun i => by dsimp only; rw [hm μ i,hm ν i])).symm

theorem capped_affinity_enlarge_cap {D R E : Type}
    [MeasurableSpace D] [MeasurableSpace R] [MeasurableSpace E]
    (μ : Measure D) [IsProbabilityMeasure μ] (ν : Measure R) [IsProbabilityMeasure ν]
    (p₀ p₁ q r : D → unitInterval)
    (h₀ : Measurable p₀) (h₁ : Measurable p₁) (hq : Measurable q) (hr : Measurable r)
    (A : StoppedProcedure R E) {m M : ℕ} (h : m ≤ M) (hcap : ∀ z, A.stop z ≤ m)
    (hp : ∀ᵐ d ∂μ, 0 < (p₀ d : ℝ) ∧ (p₀ d : ℝ) < 1 ∧
      0 < (p₁ d : ℝ) ∧ (p₁ d : ℝ) < 1) :
    (hellingerAffinity (cappedTranscriptLaw μ ν p₀ p₁ q A M)
      (cappedTranscriptLaw μ ν p₀ p₁ r A M)).toReal =
    (hellingerAffinity (cappedTranscriptLaw μ ν p₀ p₁ q A m)
      (cappedTranscriptLaw μ ν p₀ p₁ r A m)).toReal := by
  have hcapM (z) : A.stop z ≤ M := (hcap z).trans (by exact_mod_cast h)
  rw [capped_observation_affinity_real μ ν p₀ p₁ q r h₀ h₁ hq hr A M hcapM hp,
    capped_observation_affinity_real μ ν p₀ p₁ q r h₀ h₁ hq hr A m hcap hp,
    cappedStatisticLaw_enlarge_cap μ ν p₀ p₁ q h₀ h₁ hq A h hcap,
    cappedStatisticLaw_enlarge_cap μ ν p₀ p₁ r h₀ h₁ hr A h hcap]
  exact realFiniteAffinity_map_injective _ _ _ (statisticCapEmbedding_injective h)

end ThresholdHC.CriticalEntropy
