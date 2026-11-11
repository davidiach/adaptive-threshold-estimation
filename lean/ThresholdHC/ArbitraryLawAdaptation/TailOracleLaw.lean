import ThresholdHC.ArbitraryLawAdaptation.TailOracle
import ThresholdHC.ArbitraryLawAdaptation.TailMedianLaw

/-! Statement (3) of the tail certificate: the oracle comparison of the median.

For a probability law `μ` of positive gaps, a measurable gap-dependent sign law
and a rarity `0 < ρ ≤ 1/4`, the median certificate `U` at depth `J` satisfies,
with probability at least `1 - δ`,

  `F(2^{-J}) ≤ U ≤ 524288 K_{μ,ρ}(4^J)`

at every depth that meets the onset condition `TailOnset μ ρ J`. The condition
holds at every depth past a finite onset that depends on `μ` and `ρ` only. The
procedure receives neither `ρ` nor the onset. The statements are given on
independent streams, on one coin array, at one depth and at every depth at
once. `K` is the entropy-tail selection functional of the rare-event theory,
with its cap at `ρ` and its infimum over all submeasures. -/

noncomputable section
open MeasureTheory Real
open scoped ENNReal
namespace ThresholdHC.ArbitraryLawAdaptation
open ThresholdHC.Tier2 ThresholdHC.Tier6 ThresholdHC.CriticalEntropy
open ThresholdHC.ObservableSimulation ThresholdHC.EntropyTailQuantile

/-- Statement (3) at one depth, on independent streams. Under the onset
condition, with probability at least `1 - δ` the median of `m ≥ 8 log(2/δ)`
probes with flip budget `4^J` covers `F(2^{-J})` and is at most
`524288 K_{μ,ρ}(4^J)`. -/
theorem original_tail_oracle (μ : Measure Gap) [IsProbabilityMeasure μ] (q : SignLaw) {ρ : ℝ}
    (hρ : 0 < ρ) (hρ4 : ρ ≤ 1 / 4) (J m : ℕ) (hm : 0 < m) {δ : ℝ} (hδ : 0 < δ)
    (hmδ : 8 * log (2 / δ) ≤ m) (hon : TailOnset μ ρ J) :
    1 - δ ≤
      (Measure.infinitePi (fun _ : ℕ =>
          Measure.infinitePi (fun _ : ℕ => originalPopulationTapeLaw μ q))).real
        {ω | (∀ b' M' : ℕ → ℕ,
            μ.real {d : Gap | (d : ℝ) ≤ (1 / 2) ^ J} ≤ medianUpper J m b' M' ω) ∧
          ENNReal.ofReal (medianUpper J m (fun _ => 4 ^ J) (fun _ => 4 ^ J) ω) ≤
            524288 * EntropyTail.selection μ ρ (4 ^ J)} := by
  refine (original_tail_certificate μ q J m hm hδ hmδ).trans (measureReal_mono ?_)
  rintro ω ⟨h1, h2⟩
  exact ⟨h1, (ENNReal.ofReal_le_ofReal h2).trans (tail_bound_le_oracle μ hρ hρ4 J hon)⟩

/-- Statement (3) at one depth, on a single coin array: probe `j` reads the
coins `Nat.pair j i`. -/
theorem original_tail_oracle_array (μ : Measure Gap) [IsProbabilityMeasure μ] (q : SignLaw)
    {ρ : ℝ} (hρ : 0 < ρ) (hρ4 : ρ ≤ 1 / 4) (J m : ℕ) (hm : 0 < m) {δ : ℝ} (hδ : 0 < δ)
    (hmδ : 8 * log (2 / δ) ≤ m) (hon : TailOnset μ ρ J) :
    1 - δ ≤
      (Measure.infinitePi (fun _ : ℕ => originalPopulationTapeLaw μ q)).real
        {ω | (∀ b' M' : ℕ → ℕ, μ.real {d : Gap | (d : ℝ) ≤ (1 / 2) ^ J} ≤
            medianUpper J m b' M' (fun j i => ω (Nat.pair j i))) ∧
          ENNReal.ofReal (medianUpper J m (fun _ => 4 ^ J) (fun _ => 4 ^ J)
              (fun j i => ω (Nat.pair j i))) ≤
            524288 * EntropyTail.selection μ ρ (4 ^ J)} := by
  refine (original_tail_certificate_array μ q J m hm hδ hmδ).trans (measureReal_mono ?_)
  rintro ω ⟨h1, h2⟩
  exact ⟨h1, (ENNReal.ofReal_le_ofReal h2).trans (tail_bound_le_oracle μ hρ hρ4 J hon)⟩

/-- Statement (3) past the onset. There is a finite onset `J₀`, depending on
the gap law and `ρ` only, such that at every depth `J ≥ J₀` and for every
`m ≥ 8 log(2/δ)`, with probability at least `1 - δ` the median on one coin
array covers `F(2^{-J})` and is at most `524288 K_{μ,ρ}(4^J)`. -/
theorem original_tail_oracle_eventually (μ : Measure Gap) [IsProbabilityMeasure μ]
    (q : SignLaw) {ρ : ℝ} (hρ : 0 < ρ) (hρ4 : ρ ≤ 1 / 4) :
    ∃ J₀ : ℕ, ∀ (J m : ℕ) (δ : ℝ), J₀ ≤ J → 0 < m → 0 < δ → 8 * log (2 / δ) ≤ m →
      1 - δ ≤
        (Measure.infinitePi (fun _ : ℕ => originalPopulationTapeLaw μ q)).real
          {ω | (∀ b' M' : ℕ → ℕ, μ.real {d : Gap | (d : ℝ) ≤ (1 / 2) ^ J} ≤
              medianUpper J m b' M' (fun j i => ω (Nat.pair j i))) ∧
            ENNReal.ofReal (medianUpper J m (fun _ => 4 ^ J) (fun _ => 4 ^ J)
                (fun j i => ω (Nat.pair j i))) ≤
              524288 * EntropyTail.selection μ ρ (4 ^ J)} := by
  obtain ⟨J₀, hJ₀⟩ := tailOnset_eventually μ hρ (by linarith)
  exact ⟨J₀, fun J m δ hJ hm hδ hmδ =>
    original_tail_oracle_array μ q hρ hρ4 J m hm hδ hmδ (hJ₀ J hJ)⟩

/-- Every depth at once, on independent streams. Depth `J ≥ 1` runs
`m_J ≥ 8 log(2J(J+1)/δ)` probes with flip budget `4^J` on its own streams. With
probability at least `1 - δ`, at every depth `J ≥ 1` the median covers
`F(2^{-J})`, and at every depth that meets the onset condition it is at most
`524288 K_{μ,ρ}(4^J)`. -/
theorem original_tail_oracle_all_depths (μ : Measure Gap) [IsProbabilityMeasure μ]
    (q : SignLaw) {ρ : ℝ} (hρ : 0 < ρ) (hρ4 : ρ ≤ 1 / 4) (m : ℕ → ℕ) {δ : ℝ} (hδ : 0 < δ)
    (hm : ∀ J : ℕ, 1 ≤ J → 0 < m J)
    (hmδ : ∀ J : ℕ, 1 ≤ J → 8 * log (2 * ((J : ℝ) * (J + 1)) / δ) ≤ m J) :
    1 - δ ≤
      (Measure.infinitePi (fun _ : ℕ => Measure.infinitePi (fun _ : ℕ =>
          Measure.infinitePi (fun _ : ℕ => originalPopulationTapeLaw μ q)))).real
        {ω | ∀ J, 1 ≤ J →
          (∀ b' M' : ℕ → ℕ,
            μ.real {d : Gap | (d : ℝ) ≤ (1 / 2) ^ J} ≤ medianUpper J (m J) b' M' (ω J)) ∧
          (TailOnset μ ρ J →
            ENNReal.ofReal (medianUpper J (m J) (fun _ => 4 ^ J) (fun _ => 4 ^ J) (ω J)) ≤
              524288 * EntropyTail.selection μ ρ (4 ^ J))} := by
  have hN : ∀ J : ℕ, 1 ≤ J → 0 < 4 ^ J := fun J _ => pow_pos (by norm_num) J
  refine (original_median_all_depths μ q m (fun J => 4 ^ J) (fun J => 4 ^ J) hδ hm hmδ hN
    hN).trans (measureReal_mono ?_)
  intro ω hω J hJ
  obtain ⟨h1, h2⟩ := hω J hJ
  refine ⟨h1, fun hon => ?_⟩
  rw [tail_bound_uncapped μ J] at h2
  exact (ENNReal.ofReal_le_ofReal h2).trans (tail_bound_le_oracle μ hρ hρ4 J hon)

/-- Every depth at once, on a single coin array: probe `j` of depth `J` reads
the coins `Nat.pair J (Nat.pair j i)`. -/
theorem original_tail_oracle_all_depths_array (μ : Measure Gap) [IsProbabilityMeasure μ]
    (q : SignLaw) {ρ : ℝ} (hρ : 0 < ρ) (hρ4 : ρ ≤ 1 / 4) (m : ℕ → ℕ) {δ : ℝ} (hδ : 0 < δ)
    (hm : ∀ J : ℕ, 1 ≤ J → 0 < m J)
    (hmδ : ∀ J : ℕ, 1 ≤ J → 8 * log (2 * ((J : ℝ) * (J + 1)) / δ) ≤ m J) :
    1 - δ ≤
      (Measure.infinitePi (fun _ : ℕ => originalPopulationTapeLaw μ q)).real
        {ω | ∀ J, 1 ≤ J →
          (∀ b' M' : ℕ → ℕ, μ.real {d : Gap | (d : ℝ) ≤ (1 / 2) ^ J} ≤
            medianUpper J (m J) b' M' (fun j i => ω (Nat.pair J (Nat.pair j i)))) ∧
          (TailOnset μ ρ J →
            ENNReal.ofReal (medianUpper J (m J) (fun _ => 4 ^ J) (fun _ => 4 ^ J)
                (fun j i => ω (Nat.pair J (Nat.pair j i)))) ≤
              524288 * EntropyTail.selection μ ρ (4 ^ J))} := by
  have hN : ∀ J : ℕ, 1 ≤ J → 0 < 4 ^ J := fun J _ => pow_pos (by norm_num) J
  refine (original_median_all_depths_array μ q m (fun J => 4 ^ J) (fun J => 4 ^ J) hδ hm hmδ
    hN hN).trans (measureReal_mono ?_)
  intro ω hω J hJ
  obtain ⟨h1, h2⟩ := hω J hJ
  refine ⟨h1, fun hon => ?_⟩
  rw [tail_bound_uncapped μ J] at h2
  exact (ENNReal.ofReal_le_ofReal h2).trans (tail_bound_le_oracle μ hρ hρ4 J hon)

/-- Every depth at once, past the onset. There is a finite onset `J₀`,
depending on the gap law and `ρ` only, such that with probability at least
`1 - δ` the medians on one coin array cover `F(2^{-J})` at every depth `J ≥ 1`
and are at most `524288 K_{μ,ρ}(4^J)` at every depth `J ≥ J₀`. -/
theorem original_tail_oracle_all_depths_eventually (μ : Measure Gap) [IsProbabilityMeasure μ]
    (q : SignLaw) {ρ : ℝ} (hρ : 0 < ρ) (hρ4 : ρ ≤ 1 / 4) :
    ∃ J₀ : ℕ, ∀ (m : ℕ → ℕ) (δ : ℝ), 0 < δ → (∀ J : ℕ, 1 ≤ J → 0 < m J) →
      (∀ J : ℕ, 1 ≤ J → 8 * log (2 * ((J : ℝ) * (J + 1)) / δ) ≤ m J) →
      1 - δ ≤
        (Measure.infinitePi (fun _ : ℕ => originalPopulationTapeLaw μ q)).real
          {ω | ∀ J, 1 ≤ J →
            (∀ b' M' : ℕ → ℕ, μ.real {d : Gap | (d : ℝ) ≤ (1 / 2) ^ J} ≤
              medianUpper J (m J) b' M' (fun j i => ω (Nat.pair J (Nat.pair j i)))) ∧
            (J₀ ≤ J →
              ENNReal.ofReal (medianUpper J (m J) (fun _ => 4 ^ J) (fun _ => 4 ^ J)
                  (fun j i => ω (Nat.pair J (Nat.pair j i)))) ≤
                524288 * EntropyTail.selection μ ρ (4 ^ J))} := by
  obtain ⟨J₀, hJ₀⟩ := tailOnset_eventually μ hρ (by linarith)
  refine ⟨J₀, fun m δ hδ hm hmδ => ?_⟩
  refine (original_tail_oracle_all_depths_array μ q hρ hρ4 m hδ hm hmδ).trans
    (measureReal_mono ?_)
  intro ω hω J hJ
  obtain ⟨h1, h2⟩ := hω J hJ
  exact ⟨h1, fun hJ0 => h2 (hJ₀ J hJ0)⟩

end ThresholdHC.ArbitraryLawAdaptation
