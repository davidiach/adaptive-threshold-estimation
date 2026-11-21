import ThresholdHC.BernoulliTimeUniform.Specification
import ThresholdHC.BernoulliTimeUniform.TranscriptKL
import ThresholdHC.Tier5.FiniteCreation
import ThresholdHC.RareAboveTwo.TerminalInformation
import ThresholdHC.Tier6.Full

/-!
The observable prefix law of the actual online experiment under two constant
sign laws. Each private seed and gap array gives a finite transcript kernel;
the per-seed queried-coin bound is integrated against the seed law, and the
gap array is then discarded by data processing.
-/

noncomputable section
open MeasureTheory InformationTheory
open scoped ENNReal
namespace ThresholdHC.BernoulliTimeUniform
open ThresholdHC.Tier3 ThresholdHC.Tier4 ThresholdHC.Tier5 ThresholdHC.Tier6
  ThresholdHC.RareAboveTwo

/-- A common likelihood-ratio constant for two interior constant priors. -/
theorem constant_prior_ratio {θ θ' : ℝ} (hθ : 0 < θ ∧ θ < 1) (hθ' : 0 < θ' ∧ θ' < 1) :
    1 ≤ 1/θ+1/(1-θ)+1/θ'+1/(1-θ') ∧
    θ' ≤ (1/θ+1/(1-θ)+1/θ'+1/(1-θ'))*θ ∧
    1-θ' ≤ (1/θ+1/(1-θ)+1/θ'+1/(1-θ'))*(1-θ) := by
  have h1 : 0 < 1-θ := by linarith [hθ.2]
  have h1' : 0 < 1-θ' := by linarith [hθ'.2]
  have ha : 0 < 1/θ := one_div_pos.mpr hθ.1
  have hb : 0 < 1/(1-θ) := one_div_pos.mpr h1
  have hc : 0 < 1/θ' := one_div_pos.mpr hθ'.1
  have hd : 0 < 1/(1-θ') := one_div_pos.mpr h1'
  have hθinv : 1 ≤ 1/θ := by rw [le_div_iff₀ hθ.1]; linarith [hθ.2]
  have e1 : (1/θ)*θ = 1 := one_div_mul_cancel hθ.1.ne'
  have e2 : (1/(1-θ))*(1-θ) = 1 := one_div_mul_cancel h1.ne'
  refine ⟨by linarith, ?_, ?_⟩
  · have : 0 ≤ (1/(1-θ)+1/θ'+1/(1-θ'))*θ := mul_nonneg (by linarith) hθ.1.le
    nlinarith [hθ'.2]
  · have : 0 ≤ (1/θ+1/θ'+1/(1-θ'))*(1-θ) := mul_nonneg (by linarith) h1.le
    nlinarith [hθ'.1]

theorem constant_prefix_kl : ConstantPriorPrefixKLStatement := by
  intro R _ μ _ A θ θ' hθ hθ' n
  let b' := ThresholdHC.StoppingProgram.constantPrior θ' ⟨hθ'.1.le, hθ'.2.le⟩
  let b := ThresholdHC.StoppingProgram.constantPrior θ ⟨hθ.1.le, hθ.2.le⟩
  let v (c : SignLaw) (u : PopulationSeed R) (w : Prefix n) :=
    creationLaw (populationPolicy A u) (populationGap u) (populationPrior c u) w
  have ht (c : SignLaw) (u : PopulationSeed R) :
      (∀ w, 0 ≤ v c u w) ∧ ∑ w, v c u w = 1 :=
    creationLaw_total n (populationPolicy A u) (populationGap u) (populationPrior c u)
      (fun i => ⟨(populationGap_range u i).1,(populationGap_range u i).2⟩)
      (populationPrior_range c u)
  have hm (c : SignLaw) (w : Prefix n) : Measurable (fun u => v c u w) :=
    measurable_creationLaw (populationPolicy A) (measurable_populationPolicy A)
      populationGap (populationPrior c) measurable_populationGap (measurable_populationPrior c) w
  let P (c : SignLaw) :=
    prefixTranscriptLaw (experimentLaw μ A c) Prod.fst Prod.snd n
  let (c : SignLaw) : IsProbabilityMeasure (P c) := by
    dsimp [P,prefixTranscriptLaw]
    infer_instance
  have hk (c : SignLaw) : FiniteKernelRealization (populationSeedLaw μ A) (P c) (v c) :=
    realized_creation_prefix_kernel (populationSeedLaw μ A) (experimentLaw μ A c)
      Prod.fst Prod.snd (populationPolicy A) populationGap (populationPrior c)
      measurable_fst observable_tape_measurable (population_realization R μ A c).2 n
  set K := 1/θ+1/(1-θ)+1/θ'+1/(1-θ') with hKdef
  have hK := constant_prior_ratio hθ hθ'
  have hK' : 1 ≤ K ∧ θ ≤ K*θ' ∧ 1-θ ≤ K*(1-θ') := by
    have h := constant_prior_ratio hθ' hθ
    refine ⟨hK.1, ?_, ?_⟩
    · have he : K = 1/θ'+1/(1-θ')+1/θ+1/(1-θ) := by rw [hKdef]; ring
      rw [he]; exact h.2.1
    · have he : K = 1/θ'+1/(1-θ')+1/θ+1/(1-θ) := by rw [hKdef]; ring
      rw [he]; exact h.2.2
  have hratio1 (u : PopulationSeed R) (w : Prefix n) : v b' u w ≤ K^n*v b u w := by
    apply finite_transcript_le_of_prior_ratio_horizon
    · intro i; exact ⟨(populationGap_range u i.val).1,(populationGap_range u i.val).2⟩
    · intro i; exact populationPrior_range b u i.val
    · intro i; exact populationPrior_range b' u i.val
    · exact hK.1
    · intro i; exact hK.2.1
    · intro i; exact hK.2.2
  have hratio2 (u : PopulationSeed R) (w : Prefix n) : v b u w ≤ K^n*v b' u w := by
    apply finite_transcript_le_of_prior_ratio_horizon
    · intro i; exact ⟨(populationGap_range u i.val).1,(populationGap_range u i.val).2⟩
    · intro i; exact populationPrior_range b' u i.val
    · intro i; exact populationPrior_range b u i.val
    · exact hK'.1
    · intro i; exact hK'.2.1
    · intro i; exact hK'.2.2
  have hpoint (u : PopulationSeed R) :
      klFT (v b' u) (v b u) ≤ (n*((θ'-θ)^2/(θ*(1-θ))))*∑ w, v b' u w*(1:ℝ) := by
    simp only [mul_one,(ht b' u).2]
    exact constant_transcript_kl n (capPolicy (coinCap n (populationPolicy A u)) (populationPolicy A u))
      _ (fun i => ⟨(populationGap_range u i.val).1,(populationGap_range u i.val).2⟩) hθ hθ'
  have hb := finite_kernel_kl_bound (populationSeedLaw μ A) (P b') (P b) (v b') (v b)
    (hm b') (hm b) (fun u => (ht b' u).1)
    (fun u w => (Finset.single_le_sum (fun z _ => (ht b' u).1 z) (Finset.mem_univ w)).trans_eq
      (ht b' u).2)
    (fun u => (ht b u).1) (K^n) (pow_nonneg (by linarith [hK.1]) n)
    hratio1 hratio2 (hk b') (hk b) (fun _ => 1) (n*((θ'-θ)^2/(θ*(1-θ)))) hpoint
  have hsum (u : PopulationSeed R) : (∑ w, v b' u w) = 1 := (ht b' u).2
  simp only [mul_one,hsum] at hb
  simp only [integral_const,probReal_univ,one_smul,mul_one] at hb
  let f : PopulationSeed R × Prefix n → R × Prefix n := fun z => (z.1.1,z.2)
  have hf : Measurable f := measurable_fst.fst.prodMk measurable_snd
  have he (c : SignLaw) : (P c).map f = observablePrefixLaw μ A c n := by
    dsimp [P,prefixTranscriptLaw]
    rw [Measure.map_map hf (measurable_fst.prodMk
      (measurable_processPrefix Prod.snd observable_tape_measurable n))]
    rfl
  have hdata := klDiv_map_le (P b') (P b) hf
  rw [he b',he b] at hdata
  refine hdata.trans (hb.trans (le_of_eq ?_))
  congr 1
  ring

end ThresholdHC.BernoulliTimeUniform
