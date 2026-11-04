import ThresholdHC.ConfidenceTransfer.Testing

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace ThresholdHC.ConfidenceTransfer
open ThresholdHC.Tier6 ThresholdHC.RareAboveTwo ThresholdHC.ObservableSimulation

/-- The quantitative common-pair premise (CP) of the confidence-transfer note.
The same priors must work for every randomized capped local policy. -/
def CommonPairBound (μ : Measure Gap) (ρ b J : ℝ) : Prop :=
  ∀ s : ℝ, 0 < s → s ≤ b/3 →
    ∃ q r : SignLaw, RarePrior μ ρ q ∧ RarePrior μ ρ r ∧
      (∀ d, q.val d ≤ 1/2) ∧ (∀ d, r.val d ≤ 1/2) ∧
      s ≤ signMean μ r.val - signMean μ q.val ∧
      LocalNullWorkBound μ (gapParameter false) (gapParameter true) (signUnit q) (signUnit r) (42*s^2/J)

/-- Every observable procedure subject to the uniform expected budget and
failure guarantees obeys the paper's 1/128 lower bound, given (CP). -/
theorem confidence_rate_of_common_pair {R : Type} [MeasurableSpace R]
    (μ : Measure Gap) [IsProbabilityMeasure μ] (A : AdaptiveEstimator R)
    {ρ b J B ε δ : ℝ} (hb : 0 < b) (hJ : 0 < J) (hB : 0 < B)
    (hδ : 0 < δ) (hδ' : δ ≤ 1/4) (cp : CommonPairBound μ ρ b J)
    (hw : RareBudget μ A ρ B) (hconf : ∀ u : SignLaw, RarePrior μ ρ u →
      ThresholdHC.Confidence.failureProbability μ A u ε ≤ ENNReal.ofReal δ) :
    min b (Real.sqrt (J*Real.log (1/δ)/B))/128 ≤ ε := by
  let ℓ := Real.log (1/δ)
  have hℓ : 0 < ℓ := ThresholdHC.Confidence.confidence_log_pos hδ hδ'
  let z := Real.sqrt (J*ℓ/B)
  have hz : 0 < z := Real.sqrt_pos.mpr (by positivity)
  have hz2 : z^2 = J*ℓ/B := Real.sq_sqrt (by positivity)
  let u := min b z
  have hu : 0 < u := lt_min hb hz
  have hu' : u ≤ b := min_le_left _ _
  have huz : u ≤ z := min_le_right _ _
  have hu2 : u^2 ≤ z^2 := by nlinarith only [mul_nonneg (sub_nonneg.mpr huz) (add_nonneg hz.le hu.le)]
  let s := u/32
  have hs : 0 < s := by positivity
  obtain ⟨q,r,hq,hr,hqh,hrh,hsep,hloc⟩ := cp s hs (by dsimp [s]; linarith)
  have hrev : LocalNullWorkBound μ (gapParameter false) (gapParameter true)
      (signUnit r) (signUnit q) (42*s^2/J) := by
    intro U E _ _ ν _ proc n hc
    have h := hloc ν proc n hc
    apply le_trans _ h
    apply le_of_eq
    congr 2
    unfold ThresholdHC.CriticalEntropy.hellingerAffinity
    rw [add_comm]
    apply lintegral_congr
    intro x; rw [mul_comm]
  by_contra! he
  change ε < u/128 at he
  have h := pair_confidence_work μ A r q hB.le (by positivity : 0 ≤ 42*s^2/J)
    hδ hδ' hr hq hrh hqh hrev hw hconf (by dsimp [s] at hsep; linarith)
  change ℓ/4 ≤ 16/3*(42*s^2/J)*B at h
  rw [hz2] at hu2
  have hj := (le_div_iff₀ hB).mp hu2
  dsimp [s] at h
  field_simp [ne_of_gt hJ] at h
  nlinarith only [h,hj,mul_pos hJ hℓ]

/-- Minimax confidence radius with a uniform expected budget over the global
rarity class. The infimum includes arbitrary measurable private seed spaces. -/
def rareConfidenceRadius (μ : Measure Gap) [IsProbabilityMeasure μ] (ρ B δ : ℝ) : ℝ≥0∞ :=
  sInf {t | ∃ (R : Type) (_ : MeasurableSpace R) (A : AdaptiveEstimator R) (ε : ℝ),
    0 ≤ ε ∧ RareBudget μ A ρ B ∧
    (∀ u : SignLaw, RarePrior μ ρ u → ThresholdHC.Confidence.failureProbability μ A u ε ≤ ENNReal.ofReal δ) ∧
    t = ENNReal.ofReal ε}

theorem minimax_confidence_rate_of_common_pair (μ : Measure Gap) [IsProbabilityMeasure μ]
    {ρ b J B δ : ℝ} (hb : 0 < b) (hJ : 0 < J) (hB : 0 < B) (hδ : 0 < δ) (hδ' : δ ≤ 1/4)
    (cp : CommonPairBound μ ρ b J) :
    ENNReal.ofReal (min b (Real.sqrt (J*Real.log (1/δ)/B))/128) ≤ rareConfidenceRadius μ ρ B δ := by
  apply le_sInf
  rintro t ⟨R,mR,A,ε,hε,hw,hconf,rfl⟩
  exact ENNReal.ofReal_le_ofReal (confidence_rate_of_common_pair μ A hb hJ hB hδ hδ' cp hw hconf)

end ThresholdHC.ConfidenceTransfer
