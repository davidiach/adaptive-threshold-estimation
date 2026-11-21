import ThresholdHC.FullNullBank.CoinWork
import ThresholdHC.RobustContinuation.RobustLevelCertificates

/-! The level certificates of the race with the full-null bank, under a true
law coupled above the reference.

The reference law is `z0 delta_0 + (1 - z0) eta`, and the bank evaluates its
whole null mixture. The coupling `pi` has first marginal `(1 - z0) eta` and
`z.1 <= z.2`; the true law is its second marginal plus a part `mu0` coupled to
no positive reference gap.

* Error. The race is monotone, so its error transfers to the reference gaps
  (`RobustContinuation.coupled_population_error_le`). The false positives at
  the reference gaps integrate to `(1 - z0) int P_d(false positive) d eta <= u`
  under the full null, so with `u = rho * levelEpsilon l` the error is that of
  the robust bank, at most `levelAccuracy rho l`.
* Work. The per-coin bounds of `CoinWork` are integrated over the coupling as
  in `RobustContinuation.coupled_selected_work`, with the unresolved mass
  `z0 + zeta(all)` in the rarity surcharge; the logarithmic surcharge bound
  needs only `z0 + zeta(all) <= rho`. -/

noncomputable section
open MeasureTheory Set
open scoped ENNReal NNReal BigOperators

namespace ThresholdHC.FullNullBank
open ThresholdHC ThresholdHC.Tier2 ThresholdHC.Tier6 ThresholdHC.ObservableSimulation
open ThresholdHC.BlindUpper ThresholdHC.EntropyTailUpper ThresholdHC.RareAboveTwo
open ThresholdHC.EntropyTailQuantile ThresholdHC.EntropyTailAssembly ThresholdHC.RobustContinuation

/-- The error of the full-null bank under a true law coupled above
`(1 - z₀) η`: at most `ρ ε + u + (1 - z₀) ∫ ordinary error dη` plus the
uncoupled mass. -/
theorem fullNull_bank_population_error {z₀ : ℝ} (hz1 : z₀ ≤ 1) (η : Measure Gap)
    [IsProbabilityMeasure η] (π : Measure (Gap × Gap)) [IsFiniteMeasure π]
    (hup : ∀ᵐ z ∂π, (z.1:ℝ) ≤ z.2) (href : π.map Prod.fst = ENNReal.ofReal (1 - z₀) • η)
    (μ₀ : Measure Gap) [IsFiniteMeasure μ₀] (weights : ℕ → ℝ≥0) (hw : HasSum weights 1)
    {ε u ρ : ℝ} (hε : 0 ≤ ε) (hu : 0 ≤ u) (q : SignLaw)
    (hq : RarePrior (π.map Prod.snd + μ₀) ρ q) (L : ℕ) :
    racePopulationError (π.map Prod.snd + μ₀) q (negativeBankTest weights ε)
        (fullNullBankTest z₀ η weights u) L ≤
      ρ*ε + u + (1 - z₀)*(∫ d : Gap, ordinaryErrorKernel (Uniform713.cap L) (d:ℝ) ∂η) +
        μ₀.real univ := by
  have hc : 0 ≤ 1 - z₀ := by linarith
  set neg := negativeBankTest weights ε with hnegdef
  set pos := fullNullBankTest z₀ η weights u with hposdef
  let o := fun d : Gap => ordinaryErrorKernel (Uniform713.cap L) (d:ℝ)
  let k := tapeEventProbability false (everPrefixHit pos)
  have hom : Measurable o := by
    change Measurable (fun d : Gap => ordinaryErrorKernel (Uniform713.cap L) (d:ℝ))
    unfold ordinaryErrorKernel
    fun_prop
  have hkm : Measurable k := measurable_tapeEventProbability false (measurableSet_everPrefixHit pos)
  have ho0 : ∀ d, 0 ≤ o d := fun d => by
    change 0 ≤ ordinaryErrorKernel (Uniform713.cap L) (d:ℝ)
    unfold ordinaryErrorKernel
    positivity
  have ho1 : ∀ d, o d ≤ 1 := fun d => min_le_left _ _
  have hk0 : ∀ d, 0 ≤ k d := fun d => measureReal_nonneg
  have hk1 : ∀ d, k d ≤ 1 := fun d => measureReal_le_one
  have hqm := q.property.1
  have hbound : ∀ {ν : Measure Gap} [IsFiniteMeasure ν] {f : Gap → ℝ}, Measurable f →
      (∀ d, 0 ≤ f d) → (∀ d, f d ≤ 1) → Integrable f ν := by
    intro ν _ f hf h0 h1
    apply Integrable.of_bound hf.aestronglyMeasurable 1
    exact ae_of_all _ fun d => by rw [Real.norm_of_nonneg (h0 d)]; exact h1 d
  have hqi : ∀ {ν : Measure Gap} [IsFiniteMeasure ν], Integrable q.val ν := fun {ν} _ =>
    hbound hqm (fun d => (q.property.2 d).1) (fun d => (q.property.2 d).2)
  have htransfer := coupled_population_error_le (negativeBankTest_downward weights hε)
    (fullNullBankTest_upward z₀ η weights u) π hup μ₀ q L
  refine htransfer.trans (add_le_add ?_ le_rfl)
  have hpoint : ∀ z : Gap × Gap, q.val z.2 * raceConditionalError neg pos L true z.1 +
      (1 - q.val z.2) * raceConditionalError neg pos L false z.1 ≤
      ε * q.val z.2 + o z.1 + k z.1 := by
    intro z
    have hq := q.property.2 z.2
    have h1 : raceConditionalError neg pos L true z.1 ≤ ε + o z.1 :=
      (race_error_positive_bound neg pos L z.1).trans
        (add_le_add (negative_bank_probability weights hw hε z.1) le_rfl)
    have h2 : raceConditionalError neg pos L false z.1 ≤ k z.1 + o z.1 :=
      race_error_negative_bound neg pos L z.1
    nlinarith [mul_le_mul_of_nonneg_left h1 hq.1,
      mul_le_mul_of_nonneg_left h2 (by linarith : 0 ≤ 1 - q.val z.2),
      mul_nonneg hq.1 (hk0 z.1)]
  have hi1 : Integrable (fun z : Gap × Gap => q.val z.2) π :=
    (integrable_map_measure hqm.aestronglyMeasurable measurable_snd.aemeasurable).mp hqi
  have hi2 : Integrable (fun z : Gap × Gap => o z.1) π :=
    (integrable_map_measure hom.aestronglyMeasurable measurable_fst.aemeasurable).mp
      (hbound hom ho0 ho1)
  have hi3 : Integrable (fun z : Gap × Gap => k z.1) π :=
    (integrable_map_measure hkm.aestronglyMeasurable measurable_fst.aemeasurable).mp
      (hbound hkm hk0 hk1)
  have hi0 : Integrable (fun z : Gap × Gap => ε * q.val z.2) π := hi1.const_mul ε
  have hi12 : Integrable (fun z : Gap × Gap => ε * q.val z.2 + o z.1) π := hi0.add hi2
  have hi : Integrable (fun z : Gap × Gap => ε * q.val z.2 + o z.1 + k z.1) π := hi12.add hi3
  have hsum := integral_mono (integrable_coupledIntegrand π q neg pos L) hi hpoint
  have hsplit : (∫ z : Gap × Gap, ε * q.val z.2 + o z.1 + k z.1 ∂π) =
      ε * (∫ z : Gap × Gap, q.val z.2 ∂π) + (∫ z : Gap × Gap, o z.1 ∂π) +
        ∫ z : Gap × Gap, k z.1 ∂π := by
    rw [integral_add hi12 hi3, integral_add hi0 hi2, integral_const_mul]
  rw [hsplit] at hsum
  have hA : (∫ z : Gap × Gap, q.val z.2 ∂π) ≤ ρ := by
    have hmap : (∫ z : Gap × Gap, q.val z.2 ∂π) = ∫ d, q.val d ∂(π.map Prod.snd) :=
      (integral_map measurable_snd.aemeasurable hqm.aestronglyMeasurable).symm
    have hadd : signMean (π.map Prod.snd + μ₀) q.val =
        (∫ d, q.val d ∂(π.map Prod.snd)) + ∫ d, q.val d ∂μ₀ := integral_add_measure hqi hqi
    have h0 : 0 ≤ ∫ d, q.val d ∂μ₀ := integral_nonneg fun d => (q.property.2 d).1
    have hq' : signMean (π.map Prod.snd + μ₀) q.val ≤ ρ := hq
    linarith
  have hB : (∫ z : Gap × Gap, o z.1 ∂π) = (1 - z₀) * ∫ d, o d ∂η := by
    rw [← integral_map measurable_fst.aemeasurable hom.aestronglyMeasurable, href,
      integral_smul_measure, ENNReal.toReal_ofReal hc, smul_eq_mul]
  have hC : (∫ z : Gap × Gap, k z.1 ∂π) ≤ u := by
    rw [← integral_map measurable_fst.aemeasurable hkm.aestronglyMeasurable, href,
      integral_smul_measure, ENNReal.toReal_ofReal hc, smul_eq_mul]
    exact fullNull_integrated_false_positive z₀ η weights hw hz1 hu
  change coupledRaceError π q neg pos L ≤ _
  unfold coupledRaceError
  have hε' : ε * (∫ z : Gap × Gap, q.val z.2 ∂π) ≤ ρ * ε := by
    rw [mul_comm]
    exact mul_le_mul_of_nonneg_right hA hε
  rw [hB] at hsum
  change (∫ z : Gap × Gap, q.val z.2 * raceConditionalError neg pos L true z.1 +
    (1 - q.val z.2) * raceConditionalError neg pos L false z.1 ∂π) ≤
      ρ*ε + u + (1 - z₀)*(∫ d : Gap, o d ∂η)
  linarith

/-- **Level error with the full-null bank.** At a cap `4^k` whose resolved
error for the reference design is at most `δ_l/8`, with unresolved mass
`ζ(all gaps) + μ₀(all gaps) ≤ δ_l/8`, the error of the level race under the
true law is at most `δ_l`. -/
theorem fullNull_level_error {z₀ : ℝ} (hz1 : z₀ < 1) (η : Measure Gap) [IsProbabilityMeasure η]
    (ν ζ : Measure Gap) [IsFiniteMeasure ν] [IsFiniteMeasure ζ]
    (hdesign : ν+ζ = ENNReal.ofReal (1 - z₀) • η)
    (π : Measure (Gap × Gap)) [IsFiniteMeasure π] (hup : ∀ᵐ z ∂π, (z.1:ℝ) ≤ z.2)
    (href : π.map Prod.fst = ENNReal.ofReal (1 - z₀) • η) (μ₀ : Measure Gap) [IsFiniteMeasure μ₀]
    (weights : ℕ → ℝ≥0) (hw : HasSum weights 1) {ρ : ℝ} (hρ : 0 < ρ)
    (q : SignLaw) (hq : RarePrior (π.map Prod.snd + μ₀) ρ q) (l k : ℕ)
    (hk : eta ν (4 ^ k) ≤ levelAccuracy ρ l/8)
    (hz : ζ.real univ + μ₀.real univ ≤ levelAccuracy ρ l/8) :
    racePopulationError (π.map Prod.snd + μ₀) q (negativeBankTest weights (levelEpsilon l))
      (fullNullBankTest z₀ η weights (ρ*levelEpsilon l)) (2*k) ≤ levelAccuracy ρ l := by
  have hc : 0 ≤ 1 - z₀ := by linarith
  have hu : 0 ≤ ρ*levelEpsilon l := (mul_pos hρ (levelEpsilon_pos l)).le
  have h := fullNull_bank_population_error hz1.le η π hup href μ₀ weights hw
    (levelEpsilon_pos l).le hu q hq (2*k)
  have he : (1 - z₀)*(∫ d : Gap, ordinaryErrorKernel (Uniform713.cap (2*k)) (d:ℝ) ∂η) =
      eta ν (4 ^ k) + eta ζ (4 ^ k) := by
    rw [cap_twice, ← eta_add, hdesign, eta_smul_ofReal η hc]
    rfl
  rw [he] at h
  have hacc := levelEpsilon_accuracy ρ l
  have hz' := eta_le_mass ζ ((4:ℝ)^k)
  have hδ := levelAccuracy_pos hρ l
  linarith

/-- The envelope of the full-null bank, regrouped with the unresolved mass
`z₀ + ζ(all gaps)`. -/
theorem fullNull_envelope_eq (z₀ : ℝ) (σ τ ζ : Measure Gap) (d : Gap) :
    z₀ + threePieceEnvelope σ τ ζ d = (z₀ + ζ.real univ) + (∫ x : Gap, (x:ℝ)⁻¹^2 ∂σ)*(d:ℝ)^2 +
      (∫ x : Gap, (x:ℝ)⁻¹ ∂τ)*(d:ℝ) := by
  unfold threePieceEnvelope
  ring

/-- Selected core under a coupling, for the full-null bank: the known-law
selected-work bound for the design, with unresolved mass `z₀ + ζ(all gaps)`
in the surcharge. -/
theorem fullNull_coupled_selected_work {z₀ : ℝ} (hz0 : 0 ≤ z₀) (hz1 : z₀ ≤ 1) (η : Measure Gap)
    [IsProbabilityMeasure η]
    (σ τ ζ : Measure Gap) [IsFiniteMeasure σ] [IsFiniteMeasure τ] [IsFiniteMeasure ζ]
    (hdesign : σ+τ+ζ = ENNReal.ofReal (1 - z₀) • η)
    (π : Measure (Gap × Gap)) [IsFiniteMeasure π] (hup : ∀ᵐ z ∂π, (z.1:ℝ) ≤ z.2)
    (hfst : π.map Prod.fst = σ)
    {t ε ρ : ℝ} {N : ℕ} (ht : 0 < t) (hs : ∀ᵐ d : Gap ∂σ, t ≤ (d:ℝ))
    (hN : bandEdge N < t) (hA : 0 < ∫ d : Gap, (d:ℝ)⁻¹^2 ∂σ)
    (hτ : Integrable (fun d : Gap => (d:ℝ)⁻¹) τ)
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hρ : 0 < ρ) (hz : z₀ + ζ.real univ ≤ ρ)
    (q : SignLaw) (hq : (∫ z, q.val z.2 ∂π) ≤ ρ) (L : ℕ) :
    (∫ z, mixtureRaceWork q (negativeBankTest (bandWeights σ) ε)
      (fullNullBankTest z₀ η (bandWeights σ) (ρ*ε)) L z.2 ∂π) ≤
      12*costEntropy (fun j : Fin N => bandCost σ j.val) +
      12*(∫ d : Gap, (d:ℝ)⁻¹^2 ∂σ)*Real.log (ε⁻¹) +
      12*(Real.log 3+1)*(∫ d : Gap, (d:ℝ)⁻¹^2 ∂σ) +
      6*(∫ d : Gap, (d:ℝ)⁻¹ ∂τ)^2/ρ := by
  let A := ∫ d : Gap, (d:ℝ)⁻¹^2 ∂σ
  let H := ∫ d : Gap, (d:ℝ)⁻¹ ∂τ
  let m := z₀ + ζ.real univ
  let neg := negativeBankTest (bandWeights σ) ε
  let pos := fullNullBankTest z₀ η (bandWeights σ) (ρ*ε)
  let W := fun z : Gap × Gap => mixtureRaceWork q neg pos L z.2
  let V := fun z : Gap × Gap => (z.1:ℝ)⁻¹^2
  let G := fun z : Gap × Gap => logPlus ((m+A*(z.1:ℝ)^2+H*(z.1:ℝ))/ρ)
  let K := fun z : Gap × Gap => q.val z.2*V z*G z
  let C := A/ρ+H^2/(2*ρ^2)
  let cj := fun j : Fin N => 1+Real.log (ε⁻¹)+Real.log ((bandWeights σ j.val:ℝ)⁻¹)
  have hI₂ := inverseSquare_integrable_of_support σ ht hs
  have hH : 0 ≤ H := integral_nonneg (fun d => inv_nonneg.mpr d.property.1.le)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hm0 : 0 ≤ m := add_nonneg hz0 measureReal_nonneg
  have hinv : AEStronglyMeasurable (fun d : Gap => (d:ℝ)⁻¹^2) (π.map Prod.fst) :=
    (by fun_prop : Measurable (fun d : Gap => (d:ℝ)⁻¹^2)).aestronglyMeasurable
  have hVm : Measurable V := by dsimp [V]; fun_prop
  have hVi : Integrable V π := by
    have h := hI₂
    rw [← hfst] at h
    exact (integrable_map_measure hinv measurable_fst.aemeasurable).mp h
  have hVint : (∫ z, V z ∂π) = A := by
    have h := integral_map measurable_fst.aemeasurable hinv
    rw [hfst] at h
    exact h.symm
  have hqm : Measurable (fun z : Gap × Gap => q.val z.2) := q.property.1.comp measurable_snd
  have hqi : Integrable (fun z : Gap × Gap => q.val z.2) π := by
    apply Integrable.of_bound hqm.aestronglyMeasurable 1
    exact ae_of_all _ (fun z => by
      rw [Real.norm_of_nonneg (q.property.2 z.2).1]
      exact (q.property.2 z.2).2)
  have hWi : Integrable W π := integrable_coupledRaceWork π q neg pos L
  have hGm : Measurable G := by
    dsimp [G]
    unfold logPlus
    fun_prop
  have hKm : Measurable K := (hqm.mul hVm).mul hGm
  have hK0 : ∀ z, 0 ≤ K z := fun z =>
    mul_nonneg (mul_nonneg (q.property.2 z.2).1 (sq_nonneg _)) (logPlus_nonneg _)
  have hKpt : ∀ z, K z ≤ Real.log 3*V z+q.val z.2*C := by
    intro z
    have hs' := mul_le_mul_of_nonneg_left
      (log_surcharge_bound hm0 hz hA.le hH hρ z.1.property.1) (q.property.2 z.2).1
    have hb := mul_le_mul_of_nonneg_right (q.property.2 z.2).2
      (mul_nonneg (Real.log_nonneg (by norm_num : (1:ℝ) ≤ 3)) (sq_nonneg ((z.1:ℝ)⁻¹)))
    dsimp [K, V, G, C]
    dsimp [A, H, m] at hs'
    nlinarith only [hs', hb]
  have hri : Integrable (fun z : Gap × Gap => Real.log 3*V z+q.val z.2*C) π :=
    (hVi.const_mul (Real.log 3)).add (hqi.mul_const C)
  have hKi : Integrable K π := by
    apply hri.mono' hKm.aestronglyMeasurable
    refine ae_of_all _ (fun z => ?_)
    rw [Real.norm_of_nonneg (hK0 z)]
    exact hKpt z
  have hKb : (∫ z, K z ∂π) ≤ Real.log 3*A+A+H^2/(2*ρ) := by
    have h := integral_mono hKi hri hKpt
    rw [integral_add (hVi.const_mul (Real.log 3)) (hqi.mul_const C), integral_const_mul,
      integral_mul_const, hVint] at h
    have hmass := mul_le_mul_of_nonneg_right hq hC
    have he : ρ*C = A+H^2/(2*ρ) := by dsimp [C]; field_simp [hρ.ne']
    linarith
  have hband (j : Fin N) :
      (∫ z in Prod.fst ⁻¹' band j.val, W z ∂π) ≤
        12*cj j*bandCost σ j.val+12*(∫ z in Prod.fst ⁻¹' band j.val, K z ∂π) := by
    have hSm : MeasurableSet (Prod.fst ⁻¹' band j.val : Set (Gap × Gap)) :=
      measurable_fst (measurableSet_band j.val)
    have hVj : (∫ z in Prod.fst ⁻¹' band j.val, V z ∂π) = bandCost σ j.val := by
      have h := setIntegral_map (measurableSet_band j.val) hinv measurable_fst.aemeasurable
      rw [hfst] at h
      exact h.symm
    by_cases hj : bandCost σ j.val = 0
    · have h0 : π (Prod.fst ⁻¹' band j.val) = 0 := by
        rw [← Measure.map_apply measurable_fst (measurableSet_band j.val), hfst]
        exact bandCost_zero_measure σ j.val hj
      rw [Measure.restrict_eq_zero.mpr h0]
      simp [hj]
    have hjpos : 0 < bandCost σ j.val := lt_of_le_of_ne (bandCost_nonneg σ j.val) (Ne.symm hj)
    have hw := bandWeights_positive σ hA hjpos
    have hw1 := bandWeights_le_one σ hs hN hA j.val
    have hiR : IntegrableOn (fun z : Gap × Gap => (12*cj j)*V z+12*K z)
        (Prod.fst ⁻¹' band j.val) π :=
      (hVi.integrableOn.const_mul (12*cj j)).add (hKi.integrableOn.const_mul 12)
    have h := integral_mono_ae hWi.integrableOn hiR (by
      filter_upwards [ae_restrict_mem hSm, ae_restrict_of_ae hup] with z hzj hle
      have hpt := fullNull_mixture_work hz0 hz1 η σ τ ζ hdesign hI₂ hτ (bandWeights σ) hε hε1 hρ
        j.val L hw hw1 q hzj hle
      rw [fullNull_envelope_eq] at hpt
      apply hpt.trans_eq
      dsimp [cj, K, V, G, m, A, H]
      ring)
    rw [integral_add (hVi.integrableOn.const_mul (12*cj j)) (hKi.integrableOn.const_mul 12),
      integral_const_mul, integral_const_mul, hVj] at h
    exact h
  have hsum :
      (∑ j : Fin N, (12*cj j*bandCost σ j.val+12*(∫ z in Prod.fst ⁻¹' band j.val, K z ∂π))) =
      12*costEntropy (fun j : Fin N => bandCost σ j.val)+12*A*Real.log (ε⁻¹)+
        12*(∫ z, K z ∂π) := by
    have he : (∑ j : Fin N,
        (12*cj j*bandCost σ j.val+12*(∫ z in Prod.fst ⁻¹' band j.val, K z ∂π))) =
        12*(∑ j : Fin N, bandCost σ j.val*(1+Real.log ((bandWeights σ j.val:ℝ)⁻¹)))+
        12*Real.log (ε⁻¹)*(∑ j : Fin N, bandCost σ j.val)+
        12*(∑ j : Fin N, ∫ z in Prod.fst ⁻¹' band j.val, K z ∂π) := by
      simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro j _
      dsimp [cj]
      ring
    rw [he, bandWeights_entropy σ hs hN,
      ← coupled_integral_eq_sum_bands π hfst hs hN K (fun _ => hKi.integrableOn)]
    have htot := inverseSquare_eq_band_total σ hs hN
    change A = ∑ j : Fin N, bandCost σ j.val at htot
    rw [← htot]
    ring
  have htotal : (∫ z, W z ∂π) ≤
      12*costEntropy (fun j : Fin N => bandCost σ j.val)+12*A*Real.log (ε⁻¹)+
        12*(∫ z, K z ∂π) := by
    rw [coupled_integral_eq_sum_bands π hfst hs hN W (fun _ => hWi.integrableOn), ← hsum]
    exact Finset.sum_le_sum (fun j _ => hband j)
  have hk := mul_le_mul_of_nonneg_left hKb (by norm_num : (0:ℝ) ≤ 12)
  change (∫ z, W z ∂π) ≤ _
  dsimp only [A, H] at htotal hk
  exact htotal.trans ((add_le_add le_rfl hk).trans_eq (by ring))

/-- Selected core under a coupling at level `l`, for the full-null bank: at
most `128 (l+1) Γ + 6 H²/ρ`, as in the known-law theorem. -/
theorem fullNull_coupled_selected_level_work {z₀ : ℝ} (hz0 : 0 ≤ z₀) (hz1 : z₀ ≤ 1)
    (η : Measure Gap) [IsProbabilityMeasure η]
    (σ τ ζ : Measure Gap) [IsFiniteMeasure σ] [IsFiniteMeasure τ] [IsFiniteMeasure ζ]
    (hdesign : σ+τ+ζ = ENNReal.ofReal (1 - z₀) • η)
    (π : Measure (Gap × Gap)) [IsFiniteMeasure π] (hup : ∀ᵐ z ∂π, (z.1:ℝ) ≤ z.2)
    (hfst : π.map Prod.fst = σ)
    {t ρ : ℝ} {N : ℕ} (ht : 0 < t) (hs : ∀ᵐ d : Gap ∂σ, t ≤ (d:ℝ))
    (hN : bandEdge N < t) (hτ : Integrable (fun d : Gap => (d:ℝ)⁻¹) τ)
    (hρ : 0 < ρ) (hz : z₀ + ζ.real univ ≤ ρ) (q : SignLaw)
    (hq : (∫ z, q.val z.2 ∂π) ≤ ρ) (l L : ℕ) :
    (∫ z, mixtureRaceWork q (negativeBankTest (referenceWeights σ) (levelEpsilon l))
      (fullNullBankTest z₀ η (referenceWeights σ) (ρ*levelEpsilon l)) L z.2 ∂π) ≤
      128*(l+1)*costEntropy (fun j : Fin N => bandCost σ j.val) +
      6*(∫ d : Gap, (d:ℝ)⁻¹ ∂τ)^2/ρ := by
  by_cases hσ : σ = 0
  · rw [coupling_eq_zero_of_fst π (hfst.trans hσ)]
    simp only [integral_zero_measure]
    have hΓ := costEntropy_nonneg (fun j : Fin N => bandCost_nonneg σ j.val)
    positivity
  · have hA := selected_inverseSquare_pos σ ht hs hσ
    have he : referenceWeights σ = bandWeights σ := by
      funext j
      simp [referenceWeights, hσ]
    rw [he]
    have h := fullNull_coupled_selected_work hz0 hz1 η σ τ ζ hdesign π hup hfst ht hs hN hA hτ
      (levelEpsilon_pos l) (levelEpsilon_le_one l) hρ hz q hq L
    have hlog := levelEpsilon_log l
    have h3 : Real.log (3:ℝ) ≤ 2 := by
      linarith [Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 3)]
    have hAΓ : (∫ d : Gap, (d:ℝ)⁻¹^2 ∂σ) ≤ costEntropy (fun j : Fin N => bandCost σ j.val) := by
      rw [inverseSquare_eq_band_total σ hs hN]
      exact costTotal_le_costEntropy (fun j => bandCost_nonneg σ j.val)
    have hΓ := costEntropy_nonneg (fun j : Fin N => bandCost_nonneg σ j.val)
    have h1 := mul_le_mul_of_nonneg_left hlog
      (show 0 ≤ 12*(∫ d : Gap, (d:ℝ)⁻¹^2 ∂σ) by positivity)
    have h2 := mul_le_mul_of_nonneg_right h3 hA.le
    have h4 := mul_le_mul_of_nonneg_left hAΓ (show (0:ℝ) ≤ 108+48*l by positivity)
    have h5 : 0 ≤ (20+80*(l:ℝ))*costEntropy (fun j : Fin N => bandCost σ j.val) := by positivity
    nlinarith

/-- The level work of the race with the full-null bank, with one coupling for
each part of the design. -/
theorem fullNull_coupled_three_piece_level_work {z₀ : ℝ} (hz0 : 0 ≤ z₀) (hz1 : z₀ ≤ 1)
    (η : Measure Gap) [IsProbabilityMeasure η]
    (σ τ ζ : Measure Gap) [IsFiniteMeasure σ] [IsFiniteMeasure τ] [IsFiniteMeasure ζ]
    (hdesign : σ+τ+ζ = ENNReal.ofReal (1 - z₀) • η)
    (πσ πτ πζ : Measure (Gap × Gap)) [IsFiniteMeasure πσ] [IsFiniteMeasure πτ]
    [IsFiniteMeasure πζ] (hupσ : ∀ᵐ z ∂πσ, (z.1:ℝ) ≤ z.2) (hupτ : ∀ᵐ z ∂πτ, (z.1:ℝ) ≤ z.2)
    (hfσ : πσ.map Prod.fst = σ) (hfτ : πτ.map Prod.fst = τ) (hfζ : πζ.map Prod.fst = ζ)
    (μ₀ : Measure Gap) [IsFiniteMeasure μ₀]
    {t ρ : ℝ} {N : ℕ} (ht : 0 < t) (hs : ∀ᵐ d : Gap ∂σ, t ≤ (d:ℝ))
    (hN : bandEdge N < t) (hτ : Integrable (fun d : Gap => (d:ℝ)⁻¹) τ)
    (hρ : 0 < ρ) (hz : z₀ + ζ.real univ ≤ ρ) (q : SignLaw)
    (hq : RarePrior (πσ.map Prod.snd + πτ.map Prod.snd + πζ.map Prod.snd + μ₀) ρ q)
    (l L : ℕ) :
    (∫ d, mixtureRaceWork q (negativeBankTest (referenceWeights σ) (levelEpsilon l))
      (fullNullBankTest z₀ η (referenceWeights σ) (ρ*levelEpsilon l)) L d
      ∂(πσ.map Prod.snd + πτ.map Prod.snd + πζ.map Prod.snd + μ₀)) ≤
      128*(l+1)*costEntropy (fun j : Fin N => bandCost σ j.val) +
      6*(∫ d : Gap, (d:ℝ)⁻¹ ∂τ)^2/ρ + 2*ordinaryCost τ (Uniform713.cap L) +
      2*Uniform713.cap L*(ζ.real univ + μ₀.real univ) := by
  let neg := negativeBankTest (referenceWeights σ) (levelEpsilon l)
  let pos := fullNullBankTest z₀ η (referenceWeights σ) (ρ*levelEpsilon l)
  let W := mixtureRaceWork q neg pos L
  have hsnd (π : Measure (Gap × Gap)) : (∫ d, W d ∂π.map Prod.snd) = ∫ z, W z.2 ∂π :=
    integral_map measurable_snd.aemeasurable
      (measurable_mixtureRaceWork q neg pos L).aestronglyMeasurable
  have hqσ : (∫ z, q.val z.2 ∂πσ) ≤ ρ := by
    have hle : πσ.map Prod.snd ≤ πσ.map Prod.snd + πτ.map Prod.snd + πζ.map Prod.snd + μ₀ :=
      Measure.le_add_right (Measure.le_add_right (Measure.le_add_right le_rfl))
    have h := selected_signMean_le hle q hq
    rwa [integral_map measurable_snd.aemeasurable q.property.1.aestronglyMeasurable] at h
  change (∫ d, W d ∂(πσ.map Prod.snd + πτ.map Prod.snd + πζ.map Prod.snd + μ₀)) ≤ _
  rw [integral_add_measure (integrable_mixtureRaceWork _ q neg pos L)
      (integrable_mixtureRaceWork μ₀ q neg pos L),
    integral_add_measure (integrable_mixtureRaceWork _ q neg pos L)
      (integrable_mixtureRaceWork _ q neg pos L),
    integral_add_measure (integrable_mixtureRaceWork _ q neg pos L)
      (integrable_mixtureRaceWork _ q neg pos L), hsnd πσ, hsnd πτ, hsnd πζ]
  have h1 := fullNull_coupled_selected_level_work hz0 hz1 η σ τ ζ hdesign πσ hupσ hfσ ht hs hN
    hτ hρ hz q hqσ l L
  have h2 := coupled_work_le_ordinary πτ hupτ τ hfτ q neg pos L
  have h3 := coupled_work_le_cap πζ q neg pos L
  rw [coupling_real_univ πζ hfζ] at h3
  have h4 := integrated_raceWork_le_cap μ₀ q neg pos L
  change (∫ z, W z.2 ∂πσ) ≤ _ at h1
  change (∫ z, W z.2 ∂πτ) ≤ _ at h2
  change (∫ z, W z.2 ∂πζ) ≤ _ at h3
  change (∫ d, W d ∂μ₀) ≤ _ at h4
  linarith

/-- **Level work with the full-null bank under a true law coupled above the
reference.** The coupling `π` has first marginal `(1 - z₀) η = σ + τ + ζ`
and `z.1 ≤ z.2` almost everywhere; the true law is its second marginal plus
`μ₀`. The expected work of the level race is at most the level-work
certificate of the known-law theorem, with `μ₀` added to the unresolved mass,
when `z₀ + ζ(all gaps) ≤ ρ`. -/
theorem fullNull_three_piece_level_work {z₀ : ℝ} (hz0 : 0 ≤ z₀) (hz1 : z₀ ≤ 1)
    (η : Measure Gap) [IsProbabilityMeasure η]
    (σ τ ζ : Measure Gap) [IsFiniteMeasure σ] [IsFiniteMeasure τ] [IsFiniteMeasure ζ]
    (hdesign : σ+τ+ζ = ENNReal.ofReal (1 - z₀) • η)
    (π : Measure (Gap × Gap)) [IsFiniteMeasure π] (hup : ∀ᵐ z ∂π, (z.1:ℝ) ≤ z.2)
    (href : π.map Prod.fst = ENNReal.ofReal (1 - z₀) • η) (μ₀ : Measure Gap) [IsFiniteMeasure μ₀]
    {t ρ : ℝ} {N : ℕ} (ht : 0 < t) (hs : ∀ᵐ d : Gap ∂σ, t ≤ (d:ℝ))
    (hN : bandEdge N < t) (hτ : Integrable (fun d : Gap => (d:ℝ)⁻¹) τ)
    (hρ : 0 < ρ) (hz : z₀ + ζ.real univ ≤ ρ) (q : SignLaw)
    (hq : RarePrior (π.map Prod.snd + μ₀) ρ q) (l L : ℕ) :
    (∫ d, mixtureRaceWork q (negativeBankTest (referenceWeights σ) (levelEpsilon l))
      (fullNullBankTest z₀ η (referenceWeights σ) (ρ*levelEpsilon l)) L d
      ∂(π.map Prod.snd + μ₀)) ≤
      128*(l+1)*costEntropy (fun j : Fin N => bandCost σ j.val) +
      6*(∫ d : Gap, (d:ℝ)⁻¹ ∂τ)^2/ρ + 2*ordinaryCost τ (Uniform713.cap L) +
      2*Uniform713.cap L*(ζ.real univ + μ₀.real univ) := by
  obtain ⟨πσ, πτ, πζ, hπ, hfσ, hfτ, hfζ⟩ :=
    exists_split_of_map_add₃ π measurable_fst σ τ ζ (href.trans hdesign.symm)
  have hleσ : πσ ≤ π := by
    rw [← hπ, add_assoc]
    exact Measure.le_add_right le_rfl
  have hleτ : πτ ≤ π := by
    rw [← hπ, add_comm πσ πτ, add_assoc]
    exact Measure.le_add_right le_rfl
  have hleζ : πζ ≤ π := by
    rw [← hπ, add_comm]
    exact Measure.le_add_right le_rfl
  have := isFiniteMeasure_of_le π hleσ
  have := isFiniteMeasure_of_le π hleτ
  have := isFiniteMeasure_of_le π hleζ
  have hmap : π.map Prod.snd = πσ.map Prod.snd + πτ.map Prod.snd + πζ.map Prod.snd := by
    rw [← hπ, Measure.map_add _ _ measurable_snd, Measure.map_add _ _ measurable_snd]
  rw [hmap] at hq ⊢
  exact fullNull_coupled_three_piece_level_work hz0 hz1 η σ τ ζ hdesign πσ πτ πζ
    (ae_mono hleσ hup) (ae_mono hleτ hup) hfσ hfτ hfζ μ₀ ht hs hN hτ hρ hz q hq l L

end ThresholdHC.FullNullBank
