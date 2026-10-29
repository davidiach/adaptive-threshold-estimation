import ThresholdHC.RareAboveTwo.PopulationInformation
import ThresholdHC.RareAboveTwo.TerminalInformation
import ThresholdHC.CriticalEntropy.SeededPopulationTransfer

noncomputable section
namespace ThresholdHC.RareAboveTwo
open MeasureTheory ProbabilityTheory Set Filter ThresholdHC.Tier3 ThresholdHC.Tier4
open ThresholdHC.Tier6 ThresholdHC.CriticalEntropy
open scoped ENNReal Topology

def flatSign (u : ℝ) (hu : 0 ≤ u ∧ u ≤ 1) : SignLaw :=
  ⟨fun _ => u,measurable_const,fun _ => hu⟩

theorem flatSign_mean (μ : Measure Gap) [IsProbabilityMeasure μ] (u : ℝ) (hu : 0 ≤ u ∧ u ≤ 1) :
    signMean μ (flatSign u hu).val=u := by simp [signMean,flatSign]

theorem rare_prefix_information {R : Type} [MeasurableSpace R]
    (μ : Measure Gap) [IsProbabilityMeasure μ] (A : AdaptiveEstimator R)
    (a ρ B u v : ℝ) (ha : a ≤ 1/2) (hsupp : ∀ᵐ d : Gap ∂μ, (d : ℝ) ≤ a)
    (hρ : ρ ≤ 1/4) (hB : 0 ≤ B) (hu : 0 < u) (huv : u ≤ v) (hvρ : v ≤ ρ)
    (hbu : 0 ≤ u ∧ u ≤ 1) (hbv : 0 ≤ v ∧ v ≤ 1)
    (hbudget : RareBudget μ A ρ B) (n : ℕ) :
    (1-(hellingerAffinity (observablePrefixLaw μ A (flatSign u hbu) n)
      (observablePrefixLaw μ A (flatSign v hbv) n)).toReal)*u ≤ 64*(v-u)^2*a^2*B := by
  let q := flatSign u hbu
  let r := flatSign v hbv
  have hbs : 0 ≤ (u+v)/2 ∧ (u+v)/2 ≤ 1 := by constructor <;> linarith
  let s := flatSign ((u+v)/2) hbs
  have hrare : RarePrior μ ρ s := by
    change signMean μ (flatSign ((u+v)/2) hbs).val ≤ ρ
    rw [flatSign_mean]; linarith
  have hw := hbudget s hrare
  have hfin : expectedWork μ A s < ∞ := hw.trans_lt (by simp)
  have hi := observable_population_hellinger_bound A.randomLaw μ
    (experimentLaw μ A q) (experimentLaw μ A r) (experimentLaw μ A s)
    Prod.fst Prod.snd A.policy (fun d : Gap => (d : ℝ)) q.val r.val s.val
    measurable_fst observable_tape_measurable A.policy_measurable measurable_subtype_coe
    q.property.1 r.property.1 s.property.1
    (fun d => ⟨d.property.1.le,d.property.2⟩) q.property.2 r.property.2 s.property.2
    (population_realization R μ A q).2 (population_realization R μ A r).2
    (population_realization R μ A s).2 n u (64*(v-u)^2*a^2)
    (fun seed => creation_rare_information μ (A.policy seed) a u v ha hsupp hu huv (by linarith))
  have hpre := prefix_work_le_total (experimentLaw μ A s) Prod.snd observable_tape_measurable hfin n
  have hwork : (expectedWork μ A s).toReal ≤ B := by
    have h := ENNReal.toReal_mono (by simp : ENNReal.ofReal B ≠ ∞) hw
    simpa only [ENNReal.toReal_ofReal hB] using h
  exact hi.trans (mul_le_mul_of_nonneg_left (hpre.trans hwork) (by positivity))

end ThresholdHC.RareAboveTwo
