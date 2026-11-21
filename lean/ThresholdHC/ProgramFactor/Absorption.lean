import ThresholdHC.StoppingProgram.OrderedInformationBound

/-! Weighted reference absorption. Each endpoint `q` of a four-prior quartet
keeps weight `a` and gives weight `1-a` to the midpoint of the two reference
priors: `q' = a q + (1-a)(q_v + q_w)/2`. The
stopped-transcript Hellinger distance of the new endpoints is then bounded by
a²/(2(1-a)²) times the ordinary information/work ratio times the actual work
under the new midpoint. A finite ratio forces zero contrast on every null
reference prefix, so the closed-perspective convention costs nothing. -/

noncomputable section
namespace ThresholdHC.ProgramFactor
open MeasureTheory
open scoped ENNReal
open ThresholdHC.CriticalEntropy ThresholdHC.ObservableSimulation ThresholdHC.StoppingProgram
open ThresholdHC.Tier6 (Gap SignLaw signMean)
open ThresholdHC.RareAboveTwo

/-- The low endpoint mixed toward the midpoint of the reference priors. -/
def weightedLow (Q : FourPriors) (a : ℝ) (ha : 0 ≤ a ∧ a ≤ 1) : SignLaw :=
  mixPrior Q.low (midpointPrior Q.variance Q.work) a ha

/-- The high endpoint mixed toward the midpoint of the reference priors. -/
def weightedHigh (Q : FourPriors) (a : ℝ) (ha : 0 ≤ a ∧ a ≤ 1) : SignLaw :=
  mixPrior Q.high (midpointPrior Q.variance Q.work) a ha

theorem weighted_rare (μ : Measure Gap) [IsProbabilityMeasure μ] {ρ : ℝ}
    (Q : FourPriors) (hQ : Admissible μ ρ Q) (a : ℝ) (ha : 0 ≤ a ∧ a ≤ 1) :
    RarePrior μ ρ (weightedLow Q a ha) ∧ RarePrior μ ρ (weightedHigh Q a ha) := by
  have hm := mixPrior_rare μ Q.variance Q.work hQ.2.2.1 hQ.2.2.2 (1/2) (by norm_num)
  exact ⟨mixPrior_rare μ _ _ hQ.1 hm a ha,mixPrior_rare μ _ _ hQ.2.1 hm a ha⟩

theorem weighted_gap (μ : Measure Gap) [IsProbabilityMeasure μ]
    (Q : FourPriors) (a : ℝ) (ha : 0 ≤ a ∧ a ≤ 1) :
    signMean μ (weightedHigh Q a ha).val-signMean μ (weightedLow Q a ha).val =
      a*(signMean μ Q.high.val-signMean μ Q.low.val) := by
  simp only [weightedLow,weightedHigh,mixPrior_mean]
  ring

theorem mix_prefixCoefficient (μ : Measure Gap) [IsProbabilityMeasure μ]
    (q r : SignLaw) (t : ℝ) (ht : 0 ≤ t ∧ t ≤ 1) (n k : ℕ) (hk : k ≤ n) :
    prefixCoefficient μ (mixPrior q r t ht) n k =
      t*prefixCoefficient μ q n k+(1-t)*prefixCoefficient μ r n k := by
  let s : CountState n := ⟨⟨n,by omega⟩,⟨k,by change k < n+1; omega⟩⟩
  have he := mixPrior_countCoefficient μ q r t ht s
  change (n.choose k:ℝ)*prefixCoefficient μ (mixPrior q r t ht) n k =
    t*((n.choose k:ℝ)*prefixCoefficient μ q n k)+(1-t)*((n.choose k:ℝ)*prefixCoefficient μ r n k) at he
  have hc : (n.choose k:ℝ) ≠ 0 := by exact_mod_cast (Nat.choose_pos hk).ne'
  apply mul_left_cancel₀ hc
  rw [he]
  ring

theorem weightedLow_prefixCoefficient (μ : Measure Gap) [IsProbabilityMeasure μ]
    (Q : FourPriors) (a : ℝ) (ha : 0 ≤ a ∧ a ≤ 1) (n k : ℕ) (hk : k ≤ n) :
    prefixCoefficient μ (weightedLow Q a ha) n k =
      a*prefixCoefficient μ Q.low n k+(1-a)/2*prefixCoefficient μ Q.variance n k+
        (1-a)/2*prefixCoefficient μ Q.work n k := by
  rw [weightedLow,mix_prefixCoefficient μ _ _ a ha n k hk,midpoint_prefixCoefficient μ _ _ n k hk]
  ring

theorem weightedHigh_prefixCoefficient (μ : Measure Gap) [IsProbabilityMeasure μ]
    (Q : FourPriors) (a : ℝ) (ha : 0 ≤ a ∧ a ≤ 1) (n k : ℕ) (hk : k ≤ n) :
    prefixCoefficient μ (weightedHigh Q a ha) n k =
      a*prefixCoefficient μ Q.high n k+(1-a)/2*prefixCoefficient μ Q.variance n k+
        (1-a)/2*prefixCoefficient μ Q.work n k := by
  rw [weightedHigh,mix_prefixCoefficient μ _ _ a ha n k hk,midpoint_prefixCoefficient μ _ _ n k hk]
  ring

/-- Two numbers at least a positive floor c have squared root difference at
most their squared difference over 4c. -/
theorem sqrt_sub_sq_le (x y c : ℝ) (hc : 0 < c) (hx : c ≤ x) (hy : c ≤ y) :
    (Real.sqrt x-Real.sqrt y)^2 ≤ (x-y)^2/(4*c) := by
  have hx0 : 0 ≤ x := hc.le.trans hx
  have hy0 : 0 ≤ y := hc.le.trans hy
  have hsx := Real.sq_sqrt hx0
  have hsy := Real.sq_sqrt hy0
  have hsc := Real.sq_sqrt hc.le
  have hcx : Real.sqrt c ≤ Real.sqrt x := Real.sqrt_le_sqrt hx
  have hcy : Real.sqrt c ≤ Real.sqrt y := Real.sqrt_le_sqrt hy
  have hc0 : 0 ≤ Real.sqrt c := Real.sqrt_nonneg c
  have hid : (x-y)^2 = (Real.sqrt x-Real.sqrt y)^2*(Real.sqrt x+Real.sqrt y)^2 := by
    calc
      _ = ((Real.sqrt x)^2-(Real.sqrt y)^2)^2 := by rw [hsx,hsy]
      _ = _ := by ring
  have hlow : 4*c ≤ (Real.sqrt x+Real.sqrt y)^2 := by nlinarith
  apply (le_div_iff₀ (by positivity)).mpr
  rw [hid]
  exact mul_le_mul_of_nonneg_left hlow (sq_nonneg _)

theorem weighted_prefix_square_le (μ : Measure Gap) [IsProbabilityMeasure μ]
    (Q : FourPriors) (a : ℝ) (ha : 0 ≤ a ∧ a ≤ 1) (ha1 : a < 1) (n k : ℕ) (hk : k ≤ n)
    (hfin : prefixInformation μ Q n k ≠ ⊤) :
    (Real.sqrt (prefixCoefficient μ (weightedLow Q a ha) n k)-
      Real.sqrt (prefixCoefficient μ (weightedHigh Q a ha) n k))^2 ≤
      a^2/(4*((1-a)/2))*prefixReward μ Q n k := by
  have hb : 0 < (1-a)/2 := by linarith
  have hL := prefixCoefficient_nonneg μ Q.low n k
  have hH := prefixCoefficient_nonneg μ Q.high n k
  have hv := prefixCoefficient_nonneg μ Q.variance n k
  have hw := prefixCoefficient_nonneg μ Q.work n k
  rw [weightedLow_prefixCoefficient μ Q a ha n k hk,weightedHigh_prefixCoefficient μ Q a ha n k hk]
  by_cases hpos : 0 < prefixCoefficient μ Q.variance n k
  · have hc : 0 < (1-a)/2*prefixCoefficient μ Q.variance n k := mul_pos hb hpos
    have hh := sqrt_sub_sq_le
      (a*prefixCoefficient μ Q.low n k+(1-a)/2*prefixCoefficient μ Q.variance n k+
        (1-a)/2*prefixCoefficient μ Q.work n k)
      (a*prefixCoefficient μ Q.high n k+(1-a)/2*prefixCoefficient μ Q.variance n k+
        (1-a)/2*prefixCoefficient μ Q.work n k)
      ((1-a)/2*prefixCoefficient μ Q.variance n k) hc
      (by nlinarith [mul_nonneg ha.1 hL,mul_nonneg hb.le hw])
      (by nlinarith [mul_nonneg ha.1 hH,mul_nonneg hb.le hw])
    apply hh.trans (le_of_eq _)
    rw [prefixReward,prefixInformation,perspective_toReal_eq _ _ hv]
    field_simp
    ring
  · have hz : prefixCoefficient μ Q.variance n k = 0 := by linarith
    have heq : prefixCoefficient μ Q.high n k = prefixCoefficient μ Q.low n k := by
      by_contra hne
      exact hfin ((prefixInformation_top_iff μ Q n k).mpr ⟨hz,hne⟩)
    rw [heq,sub_self,zero_pow (by norm_num : (2:ℕ) ≠ 0)]
    exact mul_nonneg (by positivity) ENNReal.toReal_nonneg

theorem weighted_midpoint_work_ge {N : ℕ} (μ : Measure Gap) [IsProbabilityMeasure μ]
    (Q : FourPriors) (a : ℝ) (ha : 0 ≤ a ∧ a ≤ 1) (u : CountState N → ℝ) (hu : ∀ s, 0 ≤ u s) :
    (1-a)/2*countMean μ Q.work u ≤
      countMean μ (midpointPrior (weightedLow Q a ha) (weightedHigh Q a ha)) u := by
  unfold countMean
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro s _
  have he : countCoefficient μ (midpointPrior (weightedLow Q a ha) (weightedHigh Q a ha)) s =
      a/2*(countCoefficient μ Q.low s+countCoefficient μ Q.high s)+
        (1-a)/2*countCoefficient μ Q.variance s+(1-a)/2*countCoefficient μ Q.work s := by
    simp only [midpointPrior_countCoefficient,weightedLow,weightedHigh,mixPrior_countCoefficient]
    ring
  rw [he]
  have hL := countCoefficient_nonneg μ Q.low s
  have hH := countCoefficient_nonneg μ Q.high s
  have hv := countCoefficient_nonneg μ Q.variance s
  have hb : 0 ≤ (1-a)/2 := by linarith [ha.2]
  have hge : (1-a)/2*countCoefficient μ Q.work s ≤
      a/2*(countCoefficient μ Q.low s+countCoefficient μ Q.high s)+
        (1-a)/2*countCoefficient μ Q.variance s+(1-a)/2*countCoefficient μ Q.work s := by
    nlinarith [mul_nonneg ha.1 (add_nonneg hL hH),mul_nonneg hb hv]
  have hh := mul_le_mul_of_nonneg_right hge (hu s)
  linarith

/-- The new local lemma: stopped Hellinger distance of the weighted endpoints
against the actual work under their midpoint. -/
theorem weighted_stopped_hellinger_work {R E : Type} [MeasurableSpace R] [MeasurableSpace E]
    (μ : Measure Gap) [IsProbabilityMeasure μ] (ν : Measure R) [IsProbabilityMeasure ν]
    (Q : FourPriors) (a : ℝ) (ha : 0 ≤ a ∧ a ≤ 1) (ha1 : a < 1)
    (A : StoppedProcedure R E) (N : ℕ) (hN : 0 < N) (hK : informationRatio μ N Q ≠ ⊤)
    (hcap : ∀ z, A.stop z ≤ N) :
    stoppedHellinger μ ν (weightedLow Q a ha) (weightedHigh Q a ha) A N ≤
      (a^2/(2*(1-a)^2)*(informationRatio μ N Q).toReal)*
        (populationExpectedWork μ ν (gapParameter false) (gapParameter true)
          (signUnit (midpointPrior (weightedLow Q a ha) (weightedHigh Q a ha))) A).toReal := by
  have hb : 0 < (1-a)/2 := by linarith
  have hfin := prefixInformation_finite_of_ratio μ Q hN hK
  have hsq := stoppedHellinger_squares μ ν (weightedLow Q a ha) (weightedHigh Q a ha) A N hcap
  have hinfo := orderedFlow_information μ ν Q A N hcap hfin
  have hf := orderedFlow_cone ν A N hcap
  let m := midpointPrior (weightedLow Q a ha) (weightedHigh Q a ha)
  let W := countMean μ m (orderedFlow ν A N).continueWeight
  have hW : 0 ≤ W := countMean_nonneg μ m _ hf.continue_nonneg
  have hwork : countMean μ Q.work (orderedFlow ν A N).continueWeight ≤ W/((1-a)/2) := by
    apply (le_div_iff₀ hb).mpr
    rw [mul_comm]
    exact weighted_midpoint_work_ge μ Q a ha _ hf.continue_nonneg
  have hI := flowInformation_toReal_le μ Q (orderedFlow ν A N) hf hK (div_nonneg hW hb.le) hwork
  have hsum : stoppedReferenceSum ν A N
      (fun n k => (Real.sqrt (prefixCoefficient μ (weightedLow Q a ha) n k)-
        Real.sqrt (prefixCoefficient μ (weightedHigh Q a ha) n k))^2) ≤
      a^2/(4*((1-a)/2))*stoppedReferenceSum ν A N (prefixReward μ Q) := by
    unfold stoppedReferenceSum
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro w _
    have hk := wordHeads_le_length w.2
    have hn : w.1.val ≤ N := Nat.le_of_lt_succ w.1.isLt
    have hh := mul_le_mul_of_nonneg_left
      (weighted_prefix_square_le μ Q a ha ha1 w.1.val (wordHeads w.2) hk
        (hfin _ _ hn hk))
      (show 0 ≤ ν.real (stoppedSeedCell A w.2 Set.univ) from measureReal_nonneg)
    linarith
  rw [← hinfo] at hsum
  rw [orderedFlow_actual_work μ ν m A N hcap,ENNReal.toReal_ofReal hW]
  have h2 := mul_le_mul_of_nonneg_left hI (show 0 ≤ a^2/(4*((1-a)/2)) by positivity)
  have h3 : a^2/(4*((1-a)/2))*((informationRatio μ N Q).toReal*(W/((1-a)/2))) =
      2*((a^2/(2*(1-a)^2)*(informationRatio μ N Q).toReal)*W) := by
    have h1a : (1-a) ≠ 0 := by linarith
    field_simp
    ring
  change 2*stoppedHellinger μ ν (weightedLow Q a ha) (weightedHigh Q a ha) A N = _ at hsq
  linarith

end ThresholdHC.ProgramFactor
