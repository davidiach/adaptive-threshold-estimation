import ThresholdHC.RobustContinuation.RobustCoinWork
import ThresholdHC.RobustContinuation.RobustLevelError
import ThresholdHC.RobustContinuation.CouplingSplit
import ThresholdHC.EntropyTailAssembly.LevelCertificates

/-! The level certificates of the race under a law with larger gaps than its
reference.

The reference law has positive part `c η`, with `η` a probability law of
positive gaps, and a design `σ + τ + ζ = c η`: selected core, resolved tail
and unresolved part. The bank is the one designed from this reference: band
weights of `σ`, null law `η`, negative allowance `ε` and positive allowance
`ρ ε / c`. With `c = 1` it is the bank of the known-law theorem.

Let `π` be a coupling of reference gaps `z.1` and true gaps `z.2` with
`z.1 ≤ z.2` and first marginal `c η`, and let the true law be the second
marginal of `π` plus a part `μ₀` coupled to no positive reference gap. For
every sign law `q` of the true gaps with positive fraction at most `ρ` under
the true law, the expected work of the level race at cap `M` is at most

  `128 (l+1) Γ + 6 H²/ρ + 2 O_τ(M) + 2 M (ζ(all gaps) + μ₀(all gaps))`,

the level-work certificate of the known-law theorem with the integrals of
the reference design: `Γ` the cost entropy of the band costs of `σ`,
`H = ∫ d⁻¹ dτ` and `O_τ` the ordinary work of `τ`. Its error at a cap
`4^k` with resolved error at most `δ_l/8` is at most `δ_l`, when
`ζ(all gaps) + μ₀(all gaps) ≤ δ_l/8`.

The work proof integrates the bounds on one coin over the coupling. The
rarity surcharge is integrated against the signs of the true gaps, read at
the reference gaps through the coupling; no conditional law of the sign
given the reference gap is needed. The coupling is split along the design
by `exists_split_of_map_add₃`. -/

noncomputable section
open MeasureTheory Set
open scoped ENNReal NNReal BigOperators

namespace ThresholdHC.RobustContinuation
open ThresholdHC ThresholdHC.Tier2 ThresholdHC.Tier6 ThresholdHC.ObservableSimulation
open ThresholdHC.BlindUpper ThresholdHC.EntropyTailUpper ThresholdHC.RareAboveTwo
open ThresholdHC.EntropyTailQuantile ThresholdHC.EntropyTailAssembly

/-- The three-piece envelope is linear in the design. -/
theorem threePieceEnvelope_smul (σ τ ζ : Measure Gap) (a : ℝ≥0∞) (d : Gap) :
    threePieceEnvelope (a • σ) (a • τ) (a • ζ) d = a.toReal * threePieceEnvelope σ τ ζ d := by
  unfold threePieceEnvelope
  rw [integral_smul_measure, integral_smul_measure, measureReal_ennreal_smul_apply]
  simp only [smul_eq_mul]
  ring

/-- Work of the race on a positive coin of gap `d ≥ d₀`, for the bank of a
design `σ + τ + ζ = c η` with null law `η` and positive allowance `ρ ε / c`:
the bound of the known-law theorem at `d₀`, with the envelope of the design. -/
theorem scaled_bank_positive_work (η : Measure Gap) [IsProbabilityMeasure η]
    (σ τ ζ : Measure Gap) [IsFiniteMeasure σ] [IsFiniteMeasure τ] [IsFiniteMeasure ζ]
    {c : ℝ} (hc : 0 < c) (hdesign : σ+τ+ζ = ENNReal.ofReal c • η)
    (hσ : Integrable (fun x : Gap => (x:ℝ)⁻¹^2) σ)
    (hτ : Integrable (fun x : Gap => (x:ℝ)⁻¹) τ)
    (weights : ℕ → ℝ≥0) {ε ρ : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (hρ : 0 < ρ)
    (j L : ℕ) (hw : 0 < (weights j:ℝ)) (hw1 : (weights j:ℝ) ≤ 1)
    {d₀ d : Gap} (hd : d₀ ∈ band j) (h : (d₀:ℝ) ≤ d) :
    conditionalRaceWork (negativeBankTest weights ε) (positiveBankTest η weights (ρ*ε/c))
      L true d ≤
      12*positiveAllowance ε (weights j:ℝ) ρ (threePieceEnvelope σ τ ζ d₀)/(d₀:ℝ)^2 := by
  set a : ℝ≥0∞ := ENNReal.ofReal c⁻¹ with ha
  have hat : a ≠ ∞ := ENNReal.ofReal_ne_top
  have hac : a * ENNReal.ofReal c = 1 := by
    rw [ha, ← ENNReal.ofReal_mul (inv_nonneg.mpr hc.le), inv_mul_cancel₀ hc.ne',
      ENNReal.ofReal_one]
  have hsum : a • σ + a • τ + a • ζ = η := by
    rw [← smul_add, ← smul_add, hdesign, smul_smul, hac, one_smul]
  have := Measure.smul_finite σ hat
  have := Measure.smul_finite τ hat
  have := Measure.smul_finite ζ hat
  have : IsProbabilityMeasure (a • σ + a • τ + a • ζ) := by rw [hsum]; infer_instance
  have hr := bank_race_positive_work_of_le (a • σ) (a • τ) (a • ζ) (hσ.smul_measure hat)
    (hτ.smul_measure hat) weights hε hε1 (div_pos hρ hc) j L hw hw1 hd h
  rw [hsum, threePieceEnvelope_smul] at hr
  have hat' : a.toReal = c⁻¹ := ENNReal.toReal_ofReal (inv_nonneg.mpr hc.le)
  have hu : ρ/c*ε = ρ*ε/c := by ring
  have he : c⁻¹ * threePieceEnvelope σ τ ζ d₀ / (ρ/c) = threePieceEnvelope σ τ ζ d₀ / ρ := by
    field_simp
  have hV : positiveAllowance ε (weights j:ℝ) (ρ/c) (a.toReal * threePieceEnvelope σ τ ζ d₀) =
      positiveAllowance ε (weights j:ℝ) ρ (threePieceEnvelope σ τ ζ d₀) := by
    unfold positiveAllowance
    rw [hat', he]
  rw [hu, hV] at hr
  exact hr

/-- Work of the race on a coin of gap `d ≥ d₀` with the sign law `q` at `d`,
for the bank of a design `σ + τ + ζ = c η`: the known-law bound at `d₀`. -/
theorem scaled_bank_mixture_work (η : Measure Gap) [IsProbabilityMeasure η]
    (σ τ ζ : Measure Gap) [IsFiniteMeasure σ] [IsFiniteMeasure τ] [IsFiniteMeasure ζ]
    {c : ℝ} (hc : 0 < c) (hdesign : σ+τ+ζ = ENNReal.ofReal c • η)
    (hσ : Integrable (fun x : Gap => (x:ℝ)⁻¹^2) σ)
    (hτ : Integrable (fun x : Gap => (x:ℝ)⁻¹) τ)
    (weights : ℕ → ℝ≥0) {ε ρ : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (hρ : 0 < ρ)
    (j L : ℕ) (hw : 0 < (weights j:ℝ)) (hw1 : (weights j:ℝ) ≤ 1) (q : SignLaw)
    {d₀ d : Gap} (hd : d₀ ∈ band j) (h : (d₀:ℝ) ≤ d) :
    mixtureRaceWork q (negativeBankTest weights ε) (positiveBankTest η weights (ρ*ε/c)) L d ≤
      12*(d₀:ℝ)⁻¹^2*(1+Real.log (ε⁻¹)+Real.log ((weights j:ℝ)⁻¹))+
      12*q.val d*(d₀:ℝ)⁻¹^2*logPlus (threePieceEnvelope σ τ ζ d₀/ρ) := by
  let B := 12*(d₀:ℝ)⁻¹^2*(1+Real.log (ε⁻¹)+Real.log ((weights j:ℝ)⁻¹))
  let S := (d₀:ℝ)⁻¹^2*logPlus (threePieceEnvelope σ τ ζ d₀/ρ)
  have hb : 0 ≤ 1+Real.log (ε⁻¹)+Real.log ((weights j:ℝ)⁻¹) := by
    have he := Real.log_nonneg ((one_le_inv₀ hε).mpr hε1)
    have hw' := Real.log_nonneg ((one_le_inv₀ hw).mpr hw1)
    linarith
  have hp : conditionalRaceWork (negativeBankTest weights ε)
      (positiveBankTest η weights (ρ*ε/c)) L true d ≤ B+12*S := by
    have h' := scaled_bank_positive_work η σ τ ζ hc hdesign hσ hτ weights hε hε1 hρ j L hw hw1
      hd h
    apply h'.trans_eq
    dsimp [B, S, positiveAllowance, logPlus]
    ring
  have hn : conditionalRaceWork (negativeBankTest weights ε)
      (positiveBankTest η weights (ρ*ε/c)) L false d ≤ B := by
    have h' := bank_race_negative_work_of_le η weights hε hε1 (ρ*ε/c) j L hw hw1 hd h
    rw [log_inverse_product hε hw] at h'
    apply h'.trans
    have he : (3/(2*(d₀:ℝ)^2))*(1+(Real.log (ε⁻¹)+Real.log ((weights j:ℝ)⁻¹))) =
        (3/2)*((d₀:ℝ)⁻¹^2*(1+Real.log (ε⁻¹)+Real.log ((weights j:ℝ)⁻¹))) := by ring
    rw [he]
    dsimp [B]
    nlinarith only [mul_nonneg (sq_nonneg ((d₀:ℝ)⁻¹)) hb]
  have hp' := mul_le_mul_of_nonneg_left hp (q.property.2 d).1
  have hn' := mul_le_mul_of_nonneg_left hn (sub_nonneg.mpr (q.property.2 d).2)
  unfold mixtureRaceWork
  dsimp [B, S] at hp' hn'
  nlinarith only [hp', hn']

/-- An integral over a coupling whose reference gaps are bounded below is
the sum of its integrals over the bands of the reference gap. -/
theorem coupled_integral_eq_sum_bands (π : Measure (Gap × Gap)) {σ : Measure Gap}
    (hfst : π.map Prod.fst = σ) {t : ℝ} {N : ℕ}
    (hs : ∀ᵐ d : Gap ∂σ, t ≤ (d:ℝ)) (hN : bandEdge N < t)
    (f : Gap × Gap → ℝ) (hf : ∀ j : Fin N, IntegrableOn f (Prod.fst ⁻¹' band j.val) π) :
    (∫ z, f z ∂π) = ∑ j : Fin N, ∫ z in Prod.fst ⁻¹' band j.val, f z ∂π := by
  have hcover : ∀ᵐ z ∂π, z ∈ ⋃ j : Fin N, Prod.fst ⁻¹' band j.val := by
    have h := ae_finite_band_cover σ hs hN
    rw [← hfst] at h
    filter_upwards [ae_of_ae_map measurable_fst.aemeasurable h] with z hz
    obtain ⟨j, hj⟩ := mem_iUnion.mp hz
    exact mem_iUnion.mpr ⟨j, hj⟩
  calc
    _ = ∫ z in ⋃ j : Fin N, Prod.fst ⁻¹' band j.val, f z ∂π := by
      rw [Measure.restrict_eq_self_of_ae_mem hcover]
    _ = _ := integral_iUnion_fintype
      (fun j : Fin N => measurable_fst (measurableSet_band j.val))
      (fun i j hij => (bands_disjoint (Fin.val_injective.ne hij)).preimage Prod.fst) hf

/-- The work of the race is integrable over a coupling, read at the true gap. -/
theorem integrable_coupledRaceWork (π : Measure (Gap × Gap)) [IsFiniteMeasure π]
    (q : SignLaw) (neg pos : PrefixTest) (L : ℕ) :
    Integrable (fun z : Gap × Gap => mixtureRaceWork q neg pos L z.2) π := by
  have hm : Measurable (fun z : Gap × Gap => mixtureRaceWork q neg pos L z.2) :=
    (measurable_mixtureRaceWork q neg pos L).comp measurable_snd
  apply Integrable.of_bound hm.aestronglyMeasurable (2*(2^L))
  exact ae_of_all _ (fun z => by
    rw [Real.norm_of_nonneg (mixtureRaceWork_nonneg q neg pos L z.2)]
    exact mixtureRaceWork_le_cap q neg pos L z.2)

/-- Selected core under a coupling: the work of the bank's race at the true
gaps, integrated over a coupling with reference marginal `σ` and at most
`ρ` positive mass, is at most the known-law selected-work bound for the
design. -/
theorem coupled_selected_work (η : Measure Gap) [IsProbabilityMeasure η]
    (σ τ ζ : Measure Gap) [IsFiniteMeasure σ] [IsFiniteMeasure τ] [IsFiniteMeasure ζ]
    {c : ℝ} (hc : 0 < c) (hdesign : σ+τ+ζ = ENNReal.ofReal c • η)
    (π : Measure (Gap × Gap)) [IsFiniteMeasure π] (hup : ∀ᵐ z ∂π, (z.1:ℝ) ≤ z.2)
    (hfst : π.map Prod.fst = σ)
    {t ε ρ : ℝ} {N : ℕ} (ht : 0 < t) (hs : ∀ᵐ d : Gap ∂σ, t ≤ (d:ℝ))
    (hN : bandEdge N < t) (hA : 0 < ∫ d : Gap, (d:ℝ)⁻¹^2 ∂σ)
    (hτ : Integrable (fun d : Gap => (d:ℝ)⁻¹) τ)
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hρ : 0 < ρ) (hz : ζ.real univ ≤ ρ)
    (q : SignLaw) (hq : (∫ z, q.val z.2 ∂π) ≤ ρ) (L : ℕ) :
    (∫ z, mixtureRaceWork q (negativeBankTest (bandWeights σ) ε)
      (positiveBankTest η (bandWeights σ) (ρ*ε/c)) L z.2 ∂π) ≤
      12*costEntropy (fun j : Fin N => bandCost σ j.val) +
      12*(∫ d : Gap, (d:ℝ)⁻¹^2 ∂σ)*Real.log (ε⁻¹) +
      12*(Real.log 3+1)*(∫ d : Gap, (d:ℝ)⁻¹^2 ∂σ) +
      6*(∫ d : Gap, (d:ℝ)⁻¹ ∂τ)^2/ρ := by
  let A := ∫ d : Gap, (d:ℝ)⁻¹^2 ∂σ
  let H := ∫ d : Gap, (d:ℝ)⁻¹ ∂τ
  let m := ζ.real univ
  let neg := negativeBankTest (bandWeights σ) ε
  let pos := positiveBankTest η (bandWeights σ) (ρ*ε/c)
  let W := fun z : Gap × Gap => mixtureRaceWork q neg pos L z.2
  let V := fun z : Gap × Gap => (z.1:ℝ)⁻¹^2
  let G := fun z : Gap × Gap => logPlus ((m+A*(z.1:ℝ)^2+H*(z.1:ℝ))/ρ)
  let K := fun z : Gap × Gap => q.val z.2*V z*G z
  let C := A/ρ+H^2/(2*ρ^2)
  let cj := fun j : Fin N => 1+Real.log (ε⁻¹)+Real.log ((bandWeights σ j.val:ℝ)⁻¹)
  have hI₂ := inverseSquare_integrable_of_support σ ht hs
  have hH : 0 ≤ H := integral_nonneg (fun d => inv_nonneg.mpr d.property.1.le)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hm0 : 0 ≤ m := measureReal_nonneg
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
      have hpt := scaled_bank_mixture_work η σ τ ζ hc hdesign hI₂ hτ (bandWeights σ) hε hε1 hρ
        j.val L hw hw1 q hzj hle
      apply hpt.trans_eq
      dsimp [cj, K, V, G, m, A, H, threePieceEnvelope]
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

/-- A coupling with zero reference marginal is zero. -/
theorem coupling_eq_zero_of_fst (π : Measure (Gap × Gap)) (h : π.map Prod.fst = 0) : π = 0 := by
  apply Measure.measure_univ_eq_zero.mp
  have he : π.map Prod.fst univ = π univ := by
    rw [Measure.map_apply measurable_fst MeasurableSet.univ, preimage_univ]
  rw [← he, h]
  rfl

/-- Selected core under a coupling at level `l`: at most
`128 (l+1) Γ + 6 H²/ρ`, as in the known-law theorem. -/
theorem coupled_selected_level_work (η : Measure Gap) [IsProbabilityMeasure η]
    (σ τ ζ : Measure Gap) [IsFiniteMeasure σ] [IsFiniteMeasure τ] [IsFiniteMeasure ζ]
    {c : ℝ} (hc : 0 < c) (hdesign : σ+τ+ζ = ENNReal.ofReal c • η)
    (π : Measure (Gap × Gap)) [IsFiniteMeasure π] (hup : ∀ᵐ z ∂π, (z.1:ℝ) ≤ z.2)
    (hfst : π.map Prod.fst = σ)
    {t ρ : ℝ} {N : ℕ} (ht : 0 < t) (hs : ∀ᵐ d : Gap ∂σ, t ≤ (d:ℝ))
    (hN : bandEdge N < t) (hτ : Integrable (fun d : Gap => (d:ℝ)⁻¹) τ)
    (hρ : 0 < ρ) (hz : ζ.real univ ≤ ρ) (q : SignLaw)
    (hq : (∫ z, q.val z.2 ∂π) ≤ ρ) (l L : ℕ) :
    (∫ z, mixtureRaceWork q (negativeBankTest (referenceWeights σ) (levelEpsilon l))
      (positiveBankTest η (referenceWeights σ) (ρ*levelEpsilon l/c)) L z.2 ∂π) ≤
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
    have h := coupled_selected_work η σ τ ζ hc hdesign π hup hfst ht hs hN hA hτ
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

/-- Resolved tail under a coupling: the work of any race at the true gaps is
at most twice the ordinary work of the reference marginal. -/
theorem coupled_work_le_ordinary (π : Measure (Gap × Gap)) [IsFiniteMeasure π]
    (hup : ∀ᵐ z ∂π, (z.1:ℝ) ≤ z.2) (τ : Measure Gap) [IsFiniteMeasure τ]
    (hfst : π.map Prod.fst = τ) (q : SignLaw) (neg pos : PrefixTest) (L : ℕ) :
    (∫ z, mixtureRaceWork q neg pos L z.2 ∂π) ≤ 2*ordinaryCost τ (Uniform713.cap L) := by
  have hM : (0:ℝ) < Uniform713.cap L := Uniform713.cap_pos L
  have hkm : AEStronglyMeasurable (fun d : Gap => ordinaryWorkKernel (Uniform713.cap L) (d:ℝ))
      (π.map Prod.fst) := by
    rw [hfst]
    exact (integrable_ordinaryWorkKernel τ hM.le).aestronglyMeasurable
  have hki : Integrable (fun z : Gap × Gap => ordinaryWorkKernel (Uniform713.cap L) (z.1:ℝ)) π := by
    have h := integrable_ordinaryWorkKernel τ hM.le
    rw [← hfst] at h
    exact (integrable_map_measure hkm measurable_fst.aemeasurable).mp h
  have h := integral_mono_ae (integrable_coupledRaceWork π q neg pos L) (hki.const_mul 2) (by
    filter_upwards [hup] with z hle
    exact (mixtureRaceWork_le_ordinary q neg pos L z.2).trans
      (mul_le_mul_of_nonneg_left (ordinaryWorkKernel_antitone_gap hM hle) (by norm_num)))
  rw [integral_const_mul] at h
  have he := integral_map measurable_fst.aemeasurable hkm
  rw [hfst] at he
  unfold ordinaryCost
  rw [he]
  exact h

/-- Unresolved part under a coupling: the cap. -/
theorem coupled_work_le_cap (π : Measure (Gap × Gap)) [IsFiniteMeasure π]
    (q : SignLaw) (neg pos : PrefixTest) (L : ℕ) :
    (∫ z, mixtureRaceWork q neg pos L z.2 ∂π) ≤ 2*Uniform713.cap L*π.real univ := by
  have h := integral_mono (integrable_coupledRaceWork π q neg pos L)
    (integrable_const (2*Uniform713.cap L))
    (fun z => show mixtureRaceWork q neg pos L z.2 ≤ 2*Uniform713.cap L by
      have hc := mixtureRaceWork_le_cap q neg pos L z.2
      unfold Uniform713.cap
      exact hc)
  simpa only [integral_const, smul_eq_mul, mul_comm] using h

/-- The mass of a coupling is the mass of its reference marginal. -/
theorem coupling_real_univ (π : Measure (Gap × Gap)) {ν : Measure Gap}
    (hfst : π.map Prod.fst = ν) : π.real univ = ν.real univ := by
  rw [← hfst, map_measureReal_apply measurable_fst MeasurableSet.univ, preimage_univ]

/-- The level work of the race under a true law coupled above the reference,
with one coupling for each part of the design. The true law is the sum of
the second marginals plus `μ₀`. The coupling of the unresolved part need
not be increasing. -/
theorem coupled_three_piece_level_work (η : Measure Gap) [IsProbabilityMeasure η]
    (σ τ ζ : Measure Gap) [IsFiniteMeasure σ] [IsFiniteMeasure τ] [IsFiniteMeasure ζ]
    {c : ℝ} (hc : 0 < c) (hdesign : σ+τ+ζ = ENNReal.ofReal c • η)
    (πσ πτ πζ : Measure (Gap × Gap)) [IsFiniteMeasure πσ] [IsFiniteMeasure πτ]
    [IsFiniteMeasure πζ] (hupσ : ∀ᵐ z ∂πσ, (z.1:ℝ) ≤ z.2) (hupτ : ∀ᵐ z ∂πτ, (z.1:ℝ) ≤ z.2)
    (hfσ : πσ.map Prod.fst = σ) (hfτ : πτ.map Prod.fst = τ) (hfζ : πζ.map Prod.fst = ζ)
    (μ₀ : Measure Gap) [IsFiniteMeasure μ₀]
    {t ρ : ℝ} {N : ℕ} (ht : 0 < t) (hs : ∀ᵐ d : Gap ∂σ, t ≤ (d:ℝ))
    (hN : bandEdge N < t) (hτ : Integrable (fun d : Gap => (d:ℝ)⁻¹) τ)
    (hρ : 0 < ρ) (hz : ζ.real univ ≤ ρ) (q : SignLaw)
    (hq : RarePrior (πσ.map Prod.snd + πτ.map Prod.snd + πζ.map Prod.snd + μ₀) ρ q)
    (l L : ℕ) :
    (∫ d, mixtureRaceWork q (negativeBankTest (referenceWeights σ) (levelEpsilon l))
      (positiveBankTest η (referenceWeights σ) (ρ*levelEpsilon l/c)) L d
      ∂(πσ.map Prod.snd + πτ.map Prod.snd + πζ.map Prod.snd + μ₀)) ≤
      128*(l+1)*costEntropy (fun j : Fin N => bandCost σ j.val) +
      6*(∫ d : Gap, (d:ℝ)⁻¹ ∂τ)^2/ρ + 2*ordinaryCost τ (Uniform713.cap L) +
      2*Uniform713.cap L*(ζ.real univ + μ₀.real univ) := by
  let neg := negativeBankTest (referenceWeights σ) (levelEpsilon l)
  let pos := positiveBankTest η (referenceWeights σ) (ρ*levelEpsilon l/c)
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
  have h1 := coupled_selected_level_work η σ τ ζ hc hdesign πσ hupσ hfσ ht hs hN hτ hρ hz q hqσ
    l L
  have h2 := coupled_work_le_ordinary πτ hupτ τ hfτ q neg pos L
  have h3 := coupled_work_le_cap πζ q neg pos L
  rw [coupling_real_univ πζ hfζ] at h3
  have h4 := integrated_raceWork_le_cap μ₀ q neg pos L
  change (∫ z, W z.2 ∂πσ) ≤ _ at h1
  change (∫ z, W z.2 ∂πτ) ≤ _ at h2
  change (∫ z, W z.2 ∂πζ) ≤ _ at h3
  change (∫ d, W d ∂μ₀) ≤ _ at h4
  linarith

/-- **Level work under a true law coupled above the reference.** The
coupling `π` has first marginal `c η = σ + τ + ζ` and `z.1 ≤ z.2` almost
everywhere; the true law is its second marginal plus `μ₀`. The expected
work of the level race designed from the reference is at most the
level-work certificate of the known-law theorem, with `μ₀` added to the
unresolved mass. -/
theorem robust_three_piece_level_work (η : Measure Gap) [IsProbabilityMeasure η]
    (σ τ ζ : Measure Gap) [IsFiniteMeasure σ] [IsFiniteMeasure τ] [IsFiniteMeasure ζ]
    {c : ℝ} (hc : 0 < c) (hdesign : σ+τ+ζ = ENNReal.ofReal c • η)
    (π : Measure (Gap × Gap)) [IsFiniteMeasure π] (hup : ∀ᵐ z ∂π, (z.1:ℝ) ≤ z.2)
    (href : π.map Prod.fst = ENNReal.ofReal c • η) (μ₀ : Measure Gap) [IsFiniteMeasure μ₀]
    {t ρ : ℝ} {N : ℕ} (ht : 0 < t) (hs : ∀ᵐ d : Gap ∂σ, t ≤ (d:ℝ))
    (hN : bandEdge N < t) (hτ : Integrable (fun d : Gap => (d:ℝ)⁻¹) τ)
    (hρ : 0 < ρ) (hz : ζ.real univ ≤ ρ) (q : SignLaw)
    (hq : RarePrior (π.map Prod.snd + μ₀) ρ q) (l L : ℕ) :
    (∫ d, mixtureRaceWork q (negativeBankTest (referenceWeights σ) (levelEpsilon l))
      (positiveBankTest η (referenceWeights σ) (ρ*levelEpsilon l/c)) L d
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
  exact coupled_three_piece_level_work η σ τ ζ hc hdesign πσ πτ πζ (ae_mono hleσ hup)
    (ae_mono hleτ hup) hfσ hfτ hfζ μ₀ ht hs hN hτ hρ hz q hq l L

/-- The resolved error of a scaled law. -/
theorem eta_smul_ofReal (η : Measure Gap) {c : ℝ} (hc : 0 ≤ c) (M : ℝ) :
    eta (ENNReal.ofReal c • η) M = c * eta η M := by
  unfold eta
  rw [integral_smul_measure, ENNReal.toReal_ofReal hc, smul_eq_mul]

/-- **Level error under a true law coupled above the reference.** At a cap
`4^k` whose resolved error for the reference design is at most `δ_l/8`,
with unresolved mass `ζ(all gaps) + μ₀(all gaps) ≤ δ_l/8`, the error of the
level race under the true law is at most `δ_l`. -/
theorem robust_level_error (η : Measure Gap) [IsProbabilityMeasure η]
    (ν ζ : Measure Gap) [IsFiniteMeasure ν] [IsFiniteMeasure ζ]
    {c : ℝ} (hc : 0 < c) (hdesign : ν+ζ = ENNReal.ofReal c • η)
    (π : Measure (Gap × Gap)) [IsFiniteMeasure π] (hup : ∀ᵐ z ∂π, (z.1:ℝ) ≤ z.2)
    (href : π.map Prod.fst = ENNReal.ofReal c • η) (μ₀ : Measure Gap) [IsFiniteMeasure μ₀]
    (weights : ℕ → ℝ≥0) (hw : HasSum weights 1) {ρ : ℝ} (hρ : 0 < ρ)
    (q : SignLaw) (hq : RarePrior (π.map Prod.snd + μ₀) ρ q) (l k : ℕ)
    (hk : eta ν (4 ^ k) ≤ levelAccuracy ρ l/8)
    (hz : ζ.real univ + μ₀.real univ ≤ levelAccuracy ρ l/8) :
    racePopulationError (π.map Prod.snd + μ₀) q (negativeBankTest weights (levelEpsilon l))
      (positiveBankTest η weights (ρ*levelEpsilon l/c)) (2*k) ≤ levelAccuracy ρ l := by
  have hu : 0 ≤ ρ*levelEpsilon l/c := div_nonneg (mul_pos hρ (levelEpsilon_pos l)).le hc.le
  have h := robust_bank_population_error η π hup hc.le href μ₀ weights hw
    (levelEpsilon_pos l).le hu q hq (2*k)
  have he : c*(∫ d : Gap, ordinaryErrorKernel (Uniform713.cap (2*k)) (d:ℝ) ∂η) =
      eta ν (4 ^ k) + eta ζ (4 ^ k) := by
    rw [cap_twice, ← eta_add, hdesign, eta_smul_ofReal η hc.le]
    rfl
  have hcu : c*(ρ*levelEpsilon l/c) = ρ*levelEpsilon l := by field_simp
  rw [he, hcu] at h
  have hacc := levelEpsilon_accuracy ρ l
  have hz' := eta_le_mass ζ ((4:ℝ)^k)
  have hδ := levelAccuracy_pos hρ l
  linarith

end ThresholdHC.RobustContinuation
