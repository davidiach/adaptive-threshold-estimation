import ThresholdHC.StoppingProgram.FiniteProgram
import ThresholdHC.StoppingProgram.PrefixCoefficients
import Mathlib.MeasureTheory.Function.FactorsThrough

/-! Finite atom values are exactly realizable by globally measurable sign
priors. Thus finite-law programs do not retain hidden functional variables. -/

noncomputable section
open MeasureTheory
open scoped ENNReal BigOperators
namespace ThresholdHC.Genie
open ThresholdHC.Tier6 ThresholdHC.RareAboveTwo ThresholdHC.StoppingProgram
open ThresholdHC.CapIdentification
variable {I : Type*} [Fintype I]

def atomSignLaw (d : I → Gap) (hd : Function.Injective d) (q : I → ℝ)
    (hq : ∀ i, 0 ≤ q i ∧ q i ≤ 1) : SignLaw := by
  letI : MeasurableSpace I := ⊤
  have he : MeasurableEmbedding d := ⟨hd,measurable_of_countable d,
    fun s _ => ((Set.toFinite s).image d).measurableSet⟩
  refine ⟨Function.extend d q (fun _ => 0),he.measurable_extend (measurable_of_countable q) measurable_const,?_⟩
  intro x
  by_cases hx : ∃ i, d i = x
  · obtain ⟨i,rfl⟩ := hx
    rw [hd.extend_apply]
    exact hq i
  · rw [Function.extend_apply' _ _ _ hx]
    norm_num

theorem atomSignLaw_apply (d : I → Gap) (hd : Function.Injective d) (q : I → ℝ)
    (hq : ∀ i, 0 ≤ q i ∧ q i ≤ 1) (i : I) : (atomSignLaw d hd q hq).val (d i) = q i :=
  hd.extend_apply q (fun _ => 0) i

theorem finite_prior_mean (μ : Measure Gap) (w : I → ℝ) (d : I → Gap)
    (hw : ∀ i, 0 ≤ w i) (hμ : μ = ∑ i, ENNReal.ofReal (w i) • Measure.dirac (d i))
    (q : SignLaw) : signMean μ q.val = ∑ i, w i*q.val (d i) :=
  finite_law_integral μ w d hw hμ q.val

theorem atomSignLaw_rare (μ : Measure Gap) (w : I → ℝ) (d : I → Gap)
    (hw : ∀ i, 0 ≤ w i) (hμ : μ = ∑ i, ENNReal.ofReal (w i) • Measure.dirac (d i))
    (hd : Function.Injective d) (q : I → ℝ) (hq : ∀ i, 0 ≤ q i ∧ q i ≤ 1) (ρ : ℝ) :
    RarePrior μ ρ (atomSignLaw d hd q hq) ↔ ∑ i, w i*q i ≤ ρ := by
  unfold RarePrior
  rw [finite_prior_mean μ w d hw hμ]
  simp only [atomSignLaw_apply]

theorem finite_prefixCoefficient (μ : Measure Gap) (w : I → ℝ) (d : I → Gap)
    (hw : ∀ i, 0 ≤ w i) (hμ : μ = ∑ i, ENNReal.ofReal (w i) • Measure.dirac (d i))
    (q : SignLaw) (n k : ℕ) : prefixCoefficient μ q n k = ∑ i, w i*
      (q.val (d i)*prefixLikelihood true n k (d i)+(1-q.val (d i))*prefixLikelihood false n k (d i)) :=
  finite_law_integral μ w d hw hμ _

def atomPrefixCoefficient (w : I → ℝ) (d : I → Gap) (c : ℝ) (u : I → ℝ) (n k : ℕ) : ℝ :=
  ∑ i, w i*(u i*prefixLikelihood true n k (d i)+(c-u i)*prefixLikelihood false n k (d i))

theorem finite_scaled_prefixCoefficient (μ : Measure Gap) (w : I → ℝ) (d : I → Gap)
    (hw : ∀ i, 0 ≤ w i) (hμ : μ = ∑ i, ENNReal.ofReal (w i) • Measure.dirac (d i))
    (q : SignLaw) (c : ℝ) (u : I → ℝ) (he : ∀ i, c*q.val (d i) = u i) (n k : ℕ) :
    c*prefixCoefficient μ q n k = atomPrefixCoefficient w d c u n k := by
  rw [finite_prefixCoefficient μ w d hw hμ,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [←he i]
  ring

theorem finite_scaled_mean (μ : Measure Gap) (w : I → ℝ) (d : I → Gap)
    (hw : ∀ i, 0 ≤ w i) (hμ : μ = ∑ i, ENNReal.ofReal (w i) • Measure.dirac (d i))
    (q : SignLaw) (c : ℝ) (u : I → ℝ) (he : ∀ i, c*q.val (d i) = u i) :
    c*signMean μ q.val = ∑ i, w i*u i := by
  rw [finite_prior_mean μ w d hw hμ,Finset.mul_sum]
  exact Finset.sum_congr rfl (fun i _ => by rw [←he i]; ring)

theorem exists_scaled_atom_prior (μ : Measure Gap) [IsProbabilityMeasure μ]
    (w : I → ℝ) (d : I → Gap) (hw : ∀ i, 0 ≤ w i)
    (hμ : μ = ∑ i, ENNReal.ofReal (w i) • Measure.dirac (d i)) (hd : Function.Injective d)
    (ρ c : ℝ) (hρ : 0 ≤ ρ) (hc : 0 ≤ c) (u : I → ℝ)
    (hu : ∀ i, 0 ≤ u i ∧ u i ≤ c) (hra : ∑ i, w i*u i ≤ c*ρ) :
    ∃ q : SignLaw, RarePrior μ ρ q ∧ ∀ i, c*q.val (d i) = u i := by
  by_cases hc0 : c = 0
  · subst c
    refine ⟨nullSignLaw,?_,?_⟩
    · simpa [RarePrior,signMean,nullSignLaw] using hρ
    · intro i
      have hi : u i = 0 := le_antisymm (hu i).2 (hu i).1
      simp [hi]
  have hcp : 0 < c := lt_of_le_of_ne hc (Ne.symm hc0)
  have hv (i : I) : 0 ≤ u i/c ∧ u i/c ≤ 1 :=
    ⟨div_nonneg (hu i).1 hc,(div_le_one hcp).mpr (hu i).2⟩
  refine ⟨atomSignLaw d hd (fun i => u i/c) hv,?_,?_⟩
  · rw [atomSignLaw_rare μ w d hw hμ]
    have he : (∑ i, w i*(u i/c)) = (∑ i, w i*u i)/c := by
      rw [Finset.sum_div]
      exact Finset.sum_congr rfl (fun _ _ => by ring)
    rw [he,div_le_iff₀ hcp]
    nlinarith
  · intro i
    rw [atomSignLaw_apply]
    field_simp

end ThresholdHC.Genie
