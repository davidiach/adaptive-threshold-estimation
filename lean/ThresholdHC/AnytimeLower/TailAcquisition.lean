
import ThresholdHC.AnytimeLower.TailTranscript
import ThresholdHC.Tier5.FiniteCreation
import ThresholdHC.RareAboveTwo.TerminalInformation

noncomputable section
open MeasureTheory InformationTheory
open scoped ENNReal
namespace ThresholdHC.AnytimeLower
open ThresholdHC.Tier3 ThresholdHC.Tier4 ThresholdHC.Tier5 ThresholdHC.Tier6 ThresholdHC.RareAboveTwo

theorem tailContrast_symm {d q r : ℝ} (h : TailContrast d q r) : TailContrast d r q := by
  rcases h with he | ⟨hd,hq,hr⟩
  · exact Or.inl he.symm
  · exact Or.inr ⟨hd,hr,hq⟩

/-- Revealing the gap array only increases KL. The resulting finite kernel
charges at most epsilon squared for each physical observation, even when
the adaptive policy revisits a coin or uses unrestricted creation labels. -/
theorem tail_observable_prefix_kl {R : Type} [MeasurableSpace R]
    (μ : Measure Gap) [IsProbabilityMeasure μ] (A : AdaptiveEstimator R)
    (q r : SignLaw) {ε : ℝ} (hε : 0 ≤ ε)
    (hcentral : ∀ d : Gap, TailContrast d (q.val d) (r.val d))
    (hcontrast : ∀ d : Gap, (d:ℝ)*|q.val d-r.val d| ≤ ε/32) (n : ℕ) :
    klDiv (observablePrefixLaw μ A q n) (observablePrefixLaw μ A r n) ≤
      ENNReal.ofReal (n*ε^2) := by
  let v (b : SignLaw) (u : PopulationSeed R) (w : Prefix n) :=
    creationLaw (populationPolicy A u) (populationGap u) (populationPrior b u) w
  have ht (b : SignLaw) (u : PopulationSeed R) :
      (∀ w, 0 ≤ v b u w) ∧ ∑ w, v b u w = 1 :=
    creationLaw_total n (populationPolicy A u) (populationGap u) (populationPrior b u)
      (fun i => ⟨(populationGap_range u i).1,(populationGap_range u i).2⟩)
      (populationPrior_range b u)
  have hm (b : SignLaw) (w : Prefix n) : Measurable (fun u => v b u w) :=
    measurable_creationLaw (populationPolicy A) (measurable_populationPolicy A)
      populationGap (populationPrior b) measurable_populationGap (measurable_populationPrior b) w
  let P (b : SignLaw) :=
    prefixTranscriptLaw (experimentLaw μ A b) Prod.fst Prod.snd n
  let (b : SignLaw) : IsProbabilityMeasure (P b) := by
    dsimp [P,prefixTranscriptLaw]
    infer_instance
  have hk (b : SignLaw) : FiniteKernelRealization (populationSeedLaw μ A) (P b) (v b) :=
    realized_creation_prefix_kernel (populationSeedLaw μ A) (experimentLaw μ A b)
      Prod.fst Prod.snd (populationPolicy A) populationGap (populationPrior b)
      measurable_fst observable_tape_measurable (population_realization R μ A b).2 n
  have hratio (b c : SignLaw)
      (hc : ∀ d : Gap, TailContrast d (b.val d) (c.val d))
      (u : PopulationSeed R) (w : Prefix n) : v b u w ≤ 3^n*v c u w := by
    apply finite_transcript_le_of_prior_ratio_horizon
    · intro i; exact ⟨(populationGap_range u i.val).1,(populationGap_range u i.val).2⟩
    · intro i; exact populationPrior_range c u i.val
    · intro i; exact populationPrior_range b u i.val
    · norm_num
    · intro i
      exact (tailContrast_ratio (hc (u.2 i.val)) (b.property.2 _) (c.property.2 _)).1
    · intro i
      exact (tailContrast_ratio (hc (u.2 i.val)) (b.property.2 _) (c.property.2 _)).2
  have hpoint (u : PopulationSeed R) :
      klFT (v q u) (v r u) ≤ (n*ε^2)*∑ w, v q u w*(1:ℝ) := by
    simp only [mul_one,(ht q u).2]
    exact tail_transcript_kl n (capPolicy (coinCap n (populationPolicy A u)) (populationPolicy A u)) _ _ _ hε
      (fun i => ⟨(populationGap_range u i.val).1,(populationGap_range u i.val).2⟩)
      (fun i => populationPrior_range q u i.val) (fun i => populationPrior_range r u i.val)
      (fun i => hcentral (u.2 i.val)) (fun i => hcontrast (u.2 i.val))
  have hb := finite_kernel_kl_bound (populationSeedLaw μ A) (P q) (P r) (v q) (v r)
    (hm q) (hm r) (fun u => (ht q u).1)
    (fun u w => (Finset.single_le_sum (fun z _ => (ht q u).1 z) (Finset.mem_univ w)).trans_eq (ht q u).2)
    (fun u => (ht r u).1) (3^n) (by positivity)
    (hratio q r hcentral) (hratio r q (fun d => tailContrast_symm (hcentral d)))
    (hk q) (hk r) (fun _ => 1) (n*ε^2) hpoint
  have hsum (u : PopulationSeed R) : (∑ w, v q u w) = 1 := (ht q u).2
  simp only [mul_one,hsum] at hb
  simp only [integral_const,probReal_univ,one_smul,mul_one] at hb
  let f : PopulationSeed R × Prefix n → R × Prefix n := fun z => (z.1.1,z.2)
  have hf : Measurable f := measurable_fst.fst.prodMk measurable_snd
  have he (b : SignLaw) : (P b).map f = observablePrefixLaw μ A b n := by
    dsimp [P,prefixTranscriptLaw]
    rw [Measure.map_map hf (measurable_fst.prodMk
      (measurable_processPrefix Prod.snd observable_tape_measurable n))]
    rfl
  have hdata := klDiv_map_le (P q) (P r) hf
  rw [he q,he r] at hdata
  exact hdata.trans hb

end ThresholdHC.AnytimeLower
