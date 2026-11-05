
import ThresholdHC.AnytimeLower.QuarterDrops
import ThresholdHC.AnytimeLower.TailAcquisition
import ThresholdHC.AnytimeLower.ObservedTesting

noncomputable section
open MeasureTheory InformationTheory Real Set Filter
open scoped ENNReal Topology
namespace ThresholdHC.AnytimeLower
open ThresholdHC.Tier6 ThresholdHC.RareAboveTwo

def tailMassSequence (μ : Measure Gap) (τ : ℝ) (k : ℕ) : ℝ :=
  profileMass μ τ (geometricScale τ k)

theorem tailMassSequence_pos (μ : Measure Gap) [IsFiniteMeasure μ]
    {τ : ℝ} (hτ : 0 < τ) (hμ : 0 < μ {d : Gap | (d:ℝ) ≤ τ}) (k : ℕ) :
    0 < tailMassSequence μ τ k :=
  profileMass_pos μ (geometricScale_pos hτ k) hμ

theorem tailMassSequence_tendsto_zero (μ : Measure Gap) [IsFiniteMeasure μ]
    {τ : ℝ} (hτ : 0 < τ) : Tendsto (tailMassSequence μ τ) atTop (𝓝 0) :=
  profileMass_tendsto_zero μ τ (geometricScale τ)
    (fun k => (geometricScale_pos hτ k).le) (geometricScale_tendsto_zero τ)

theorem tailMassSequence_antitone (μ : Measure Gap) [IsFiniteMeasure μ]
    {τ : ℝ} (hτ : 0 < τ) : Antitone (tailMassSequence μ τ) := by
  intro i j hij
  exact profileMass_mono μ τ (geometricScale_pos hτ j).le (geometricScale_antitone hτ.le hij)

def tailDropIndex (μ : Measure Gap) [IsFiniteMeasure μ]
    {τ : ℝ} (hτ : 0 < τ) (hμ : 0 < μ {d : Gap | (d:ℝ) ≤ τ}) : ℕ → ℕ :=
  dropIndex (tailMassSequence μ τ) (tailMassSequence_pos μ hτ hμ)
    (tailMassSequence_tendsto_zero μ hτ)

def selectedScale (μ : Measure Gap) [IsFiniteMeasure μ]
    {τ : ℝ} (hτ : 0 < τ) (hμ : 0 < μ {d : Gap | (d:ℝ) ≤ τ}) (k : ℕ) : ℝ :=
  geometricScale τ (tailDropIndex μ hτ hμ k)

theorem selectedScale_antitone (μ : Measure Gap) [IsFiniteMeasure μ]
    {τ : ℝ} (hτ : 0 < τ) (hμ : 0 < μ {d : Gap | (d:ℝ) ≤ τ}) :
    Antitone (selectedScale μ hτ hμ) :=
  (geometricScale_antitone hτ.le).comp_monotone
    (dropIndex_strictMono _ _ _).monotone

def selectedAlternative (μ : Measure Gap) [IsFiniteMeasure μ]
    {τ : ℝ} (hτ : 0 < τ) (hμ : 0 < μ {d : Gap | (d:ℝ) ≤ τ}) (k : ℕ) : SignLaw :=
  tailAlternative τ (selectedScale μ hτ hμ k) (selectedScale μ hτ hμ (k+1))
    (geometricScale_pos hτ _).le
    (selectedScale_antitone μ hτ hμ (Nat.le_succ k))

def selectedSeparation (μ : Measure Gap) [IsFiniteMeasure μ]
    {τ : ℝ} (hτ : 0 < τ) (hμ : 0 < μ {d : Gap | (d:ℝ) ≤ τ}) (k : ℕ) : ℝ :=
  (profileMass μ τ (selectedScale μ hτ hμ k)-
    profileMass μ τ (selectedScale μ hτ hμ (k+1)))/32

theorem selectedSeparation_pos (μ : Measure Gap) [IsFiniteMeasure μ]
    {τ : ℝ} (hτ : 0 < τ) (hμ : 0 < μ {d : Gap | (d:ℝ) ≤ τ}) (k : ℕ) :
    0 < selectedSeparation μ hτ hμ k :=
  dropSeparation_pos (tailMassSequence μ τ) (tailMassSequence_pos μ hτ hμ)
    (tailMassSequence_tendsto_zero μ hτ) k

theorem selectedSeparation_separated (μ : Measure Gap) [IsFiniteMeasure μ]
    {τ : ℝ} (hτ : 0 < τ) (hμ : 0 < μ {d : Gap | (d:ℝ) ≤ τ}) (i k : ℕ) (hik : i < k) :
    3*selectedSeparation μ hτ hμ k ≤ selectedSeparation μ hτ hμ i :=
  dropSeparation_separated _ _ _ (tailMassSequence_antitone μ hτ) i k hik

theorem selectedSeparation_lower (μ : Measure Gap) [IsFiniteMeasure μ]
    {τ : ℝ} (hτ : 0 < τ) (hμ : 0 < μ {d : Gap | (d:ℝ) ≤ τ}) (k : ℕ) :
    3*profileMass μ τ (selectedScale μ hτ hμ k)/128 ≤ selectedSeparation μ hτ hμ k :=
  dropSeparation_lower (tailMassSequence μ τ) (tailMassSequence_pos μ hτ hμ)
    (tailMassSequence_tendsto_zero μ hτ) k

theorem selectedAlternative_mean (μ : Measure Gap) [IsFiniteMeasure μ]
    {τ : ℝ} (hτ : 0 < τ) (hμ : 0 < μ {d : Gap | (d:ℝ) ≤ τ}) (k : ℕ) :
    signMean μ (selectedAlternative μ hτ hμ k).val =
      signMean μ (tailBase τ).val+selectedSeparation μ hτ hμ k := by
  have hm := tailAlternative_mean μ τ (geometricScale_pos hτ _).le
    (selectedScale_antitone μ hτ hμ (Nat.le_succ k))
  change signMean μ (selectedAlternative μ hτ hμ k).val -
    signMean μ (tailBase τ).val = selectedSeparation μ hτ hμ k at hm
  linarith

theorem selectedAlternative_prefix_kl {R : Type} [MeasurableSpace R]
    (μ : Measure Gap) [IsProbabilityMeasure μ] (A : AdaptiveEstimator R)
    {τ : ℝ} (hτ : 0 < τ) (hτq : τ ≤ 1/4)
    (hμ : 0 < μ {d : Gap | (d:ℝ) ≤ τ}) (k n : ℕ) :
    klDiv (observablePrefixLaw μ A (selectedAlternative μ hτ hμ k) n)
      (observablePrefixLaw μ A (tailBase τ) n) ≤
        ENNReal.ofReal (n*(selectedScale μ hτ hμ k)^2) := by
  apply tail_observable_prefix_kl μ A _ _ (geometricScale_pos hτ _).le
  · intro d
    by_cases hd : (d:ℝ) ≤ τ
    · right
      have hc := tailAlternative_central τ (geometricScale_pos hτ _).le
        (selectedScale_antitone μ hτ hμ (Nat.le_succ k)) d hd
      change 1/4 ≤ (selectedAlternative μ hτ hμ k).val d ∧
        (selectedAlternative μ hτ hμ k).val d ≤ 9/32 at hc
      refine ⟨hd.trans hτq,⟨hc.1,by linarith [hc.2]⟩,?_⟩
      norm_num [tailBase,hd]
    · left
      simp [selectedAlternative,tailAlternative,tailBase,tailProfile,hd]
  · exact tailAlternative_contrast τ _ _

/-- The infinite sequence of actual rare alternatives forces widths comparable
to the capped inverse-gap mass whenever the testing schedule is nonsummable. -/
theorem tail_profile_frequently {R : Type} [MeasurableSpace R]
    (μ : Measure Gap) [IsProbabilityMeasure μ] (A : AdaptiveEstimator R)
    (H : ∀ n, R × ThresholdHC.Tier3.Prefix n → ℝ) (hH : ∀ n, Measurable (H n))
    {τ ρ δ : ℝ} (hτ : 0 < τ) (hτq : τ ≤ 1/4)
    (hμ : 0 < μ {d : Gap | (d:ℝ) ≤ τ})
    (hrare : μ.real {d : Gap | (d:ℝ) ≤ τ} ≤ ρ)
    (hd : 0 ≤ δ ∧ δ ≤ 1/2) (t : ℕ → ℝ) (hacc : OnlineAccuracy μ A H ρ δ t)
    (N : ℕ → ℕ) (hN : Monotone N)
    (hdiv : ¬Summable (fun k => exp (-((N k:ℝ)*(selectedScale μ hτ hμ k)^2)/(1-δ)))) :
    ∃ᶠ k in atTop, profileMass μ τ (selectedScale μ hτ hμ k)/256 ≤ t (N k) := by
  have hh := observed_separated_frequently μ A H hH hd t hacc
    (tailBase τ) (tailBase_rare μ hrare) (selectedAlternative μ hτ hμ)
    (fun k => tailAlternative_rare μ _ _ hrare)
    (selectedSeparation μ hτ hμ) (selectedSeparation_pos μ hτ hμ)
    (selectedAlternative_mean μ hτ hμ) (selectedSeparation_separated μ hτ hμ)
    N hN (fun k => (N k:ℝ)*(selectedScale μ hτ hμ k)^2)
    (fun k => by positivity) (fun k => selectedAlternative_prefix_kl μ A hτ hτq hμ k _) hdiv
  apply hh.mono
  intro k hk
  have hl := selectedSeparation_lower μ hτ hμ k
  linarith

end ThresholdHC.AnytimeLower
