import ThresholdHC.PilotCorrection.Mixture

/-! The production average on `n` independent coins.

For a square-integrable feature `W` under a probability law `μ`, the average
of `W` over `n ≥ 1` independent copies has mean `E W` and mean squared error
`Var W / n` about that mean. Under `FixedFeatures` and `q ∈ Q`, this gives
the mean and the fixed-coefficient risk of the raw average, and, by Tonelli's
theorem, the pilot risk as the `L q`-average of fixed-coefficient risks. -/

noncomputable section
namespace ThresholdHC.PilotCorrection
open MeasureTheory ProbabilityTheory
open scoped ENNReal

section Iid

variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
  {W : Ω → ℝ}

theorem iid_eval_integral (hW : MemLp W 2 μ) (n : ℕ) (j : Fin n) :
    (∫ ω : Fin n → Ω, W (ω j) ∂Measure.pi (fun _ : Fin n => μ)) = ∫ x, W x ∂μ := by
  have hm := (measurePreserving_eval (fun _ : Fin n => μ) j).map_eq
  calc
    _ = ∫ x, W x ∂(Measure.pi (fun _ : Fin n => μ)).map (fun ω => ω j) :=
      (integral_map (measurable_pi_apply j).aemeasurable
        (by rw [hm]; exact hW.aestronglyMeasurable)).symm
    _ = _ := by rw [hm]

theorem iid_average_memLp (hW : MemLp W 2 μ) (n : ℕ) :
    MemLp (fun ω : Fin n → Ω => (n : ℝ)⁻¹ * ∑ j, W (ω j)) 2
      (Measure.pi (fun _ : Fin n => μ)) := by
  have hi (j : Fin n) : MemLp (fun ω : Fin n → Ω => W (ω j)) 2
      (Measure.pi (fun _ : Fin n => μ)) :=
    hW.comp_measurePreserving (measurePreserving_eval (fun _ : Fin n => μ) j)
  exact (memLp_finsetSum Finset.univ (fun j _ => hi j)).const_mul _

theorem iid_average_integral (hW : MemLp W 2 μ) {n : ℕ} (hn : 1 ≤ n) :
    (∫ ω : Fin n → Ω, (n : ℝ)⁻¹ * ∑ j, W (ω j) ∂Measure.pi (fun _ : Fin n => μ)) =
      ∫ x, W x ∂μ := by
  have hi (j : Fin n) : Integrable (fun ω : Fin n → Ω => W (ω j))
      (Measure.pi (fun _ : Fin n => μ)) :=
    (hW.comp_measurePreserving (measurePreserving_eval (fun _ : Fin n => μ) j)).integrable
      (by norm_num)
  rw [integral_const_mul, integral_finsetSum _ (fun j _ => hi j)]
  simp_rw [iid_eval_integral μ hW n]
  have hn' : (n : ℝ) ≠ 0 := by
    have : (0 : ℝ) < n := by exact_mod_cast hn
    exact this.ne'
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp

theorem iid_average_variance (hW : MemLp W 2 μ) (n : ℕ) :
    variance (fun ω : Fin n → Ω => (n : ℝ)⁻¹ * ∑ j, W (ω j))
        (Measure.pi (fun _ : Fin n => μ)) =
      ((n : ℝ)⁻¹) ^ 2 * ((n : ℝ) * variance W μ) := by
  rw [variance_const_mul]
  have hh := variance_sum_pi (μ := fun _ : Fin n => μ) (X := fun _ => W) (fun _ => hW)
  congr 1
  calc
    _ = variance (∑ j : Fin n, fun ω : Fin n → Ω => W (ω j))
        (Measure.pi (fun _ : Fin n => μ)) := by
      congr 1
      funext ω
      simp [Finset.sum_apply]
    _ = ∑ _ : Fin n, variance W μ := hh
    _ = _ := by simp

/-- The mean squared error of the iid average about the mean `E W`. -/
theorem iid_average_risk (hW : MemLp W 2 μ) {n : ℕ} (hn : 1 ≤ n) :
    (∫⁻ ω : Fin n → Ω,
        ENNReal.ofReal (((n : ℝ)⁻¹ * ∑ j, W (ω j) - ∫ x, W x ∂μ) ^ 2)
        ∂Measure.pi (fun _ : Fin n => μ)) =
      ENNReal.ofReal (variance W μ / n) := by
  have hmean := iid_average_integral μ hW hn
  have h := evariance_eq_lintegral_ofReal
    (X := fun ω : Fin n → Ω => (n : ℝ)⁻¹ * ∑ j, W (ω j))
    (μ := Measure.pi (fun _ : Fin n => μ))
  rw [hmean] at h
  rw [← h, ← ofReal_variance (iid_average_memLp μ hW n), iid_average_variance μ hW n]
  congr 1
  have hn' : (n : ℝ) ≠ 0 := by
    have : (0 : ℝ) < n := by exact_mod_cast hn
    exact this.ne'
  field_simp

end Iid

section Features

variable {Ω : Type*} [MeasurableSpace Ω] {k : ℕ} {π : Fin k → ℝ} {ρ : ℝ}
  {Pplus Pminus : Fin k → Measure Ω} [∀ i, IsProbabilityMeasure (Pplus i)]
  [∀ i, IsProbabilityMeasure (Pminus i)] {Y Z : Ω → ℝ} {v : ℝ}

theorem coinLaw_isProbability_of_mem (hF : FixedFeatures π ρ Pplus Pminus Y Z v)
    {q : Fin k → ℝ} (hq : q ∈ rarityPolytope π ρ) :
    IsProbabilityMeasure (coinLaw π Pplus Pminus q) :=
  coinLaw_isProbability π Pplus Pminus hF.1 hF.2.1 hq.1

omit [∀ i, IsProbabilityMeasure (Pplus i)] [∀ i, IsProbabilityMeasure (Pminus i)] in
theorem memLp_feature (hF : FixedFeatures π ρ Pplus Pminus Y Z v) (q : Fin k → ℝ)
    (β : ℝ) : MemLp (fun ω => Y ω - β * Z ω) 2 (coinLaw π Pplus Pminus q) := by
  obtain ⟨_, _, _, _, _, hL, _⟩ := hF
  exact (memLp_coinLaw π Pplus Pminus (fun i => ⟨(hL i).1, (hL i).2.1⟩) q).sub
    ((memLp_coinLaw π Pplus Pminus (fun i => ⟨(hL i).2.2.1, (hL i).2.2.2⟩) q).const_mul β)

theorem integral_feature (hF : FixedFeatures π ρ Pplus Pminus Y Z v)
    {q : Fin k → ℝ} (hq : q ∈ rarityPolytope π ρ) (β : ℝ) :
    (∫ ω, Y ω - β * Z ω ∂coinLaw π Pplus Pminus q) = signMass π q := by
  have := coinLaw_isProbability_of_mem hF hq
  obtain ⟨_, _, _, _, _, hL, _, hmom⟩ := hF
  obtain ⟨hY1, hZ0, _⟩ := hmom q hq
  have hYm := memLp_coinLaw π Pplus Pminus (fun i => ⟨(hL i).1, (hL i).2.1⟩) q
  have hZm := memLp_coinLaw π Pplus Pminus (fun i => ⟨(hL i).2.2.1, (hL i).2.2.2⟩) q
  rw [integral_sub (hYm.integrable (by norm_num))
    ((hZm.integrable (by norm_num)).const_mul _), integral_const_mul, hY1, hZ0]
  ring

/-- The raw average is unbiased on `Q`. -/
theorem integral_rawAverage (hF : FixedFeatures π ρ Pplus Pminus Y Z v)
    {q : Fin k → ℝ} (hq : q ∈ rarityPolytope π ρ) (β : ℝ) {n : ℕ} (hn : 1 ≤ n) :
    (∫ ω, rawAverage Y Z n β ω
        ∂Measure.pi (fun _ : Fin n => coinLaw π Pplus Pminus q)) = signMass π q := by
  have := coinLaw_isProbability_of_mem hF hq
  rw [← integral_feature hF hq β]
  exact iid_average_integral (coinLaw π Pplus Pminus q) (memLp_feature hF q β) hn

/-- The fixed-coefficient risk is `Var_q(Y - βZ) / n` on `Q`. -/
theorem fixedRisk_eq (hF : FixedFeatures π ρ Pplus Pminus Y Z v)
    {q : Fin k → ℝ} (hq : q ∈ rarityPolytope π ρ) (β : ℝ) {n : ℕ} (hn : 1 ≤ n) :
    fixedRisk π Pplus Pminus Y Z n β q =
      ENNReal.ofReal (variance (fun ω => Y ω - β * Z ω) (coinLaw π Pplus Pminus q) / n) := by
  have := coinLaw_isProbability_of_mem hF hq
  unfold fixedRisk
  rw [← integral_feature hF hq β]
  exact iid_average_risk (coinLaw π Pplus Pminus q) (memLp_feature hF q β) hn

theorem measurable_pilotIntegrand {T : Type*} [MeasurableSpace T] (hY : Measurable Y)
    (hZ : Measurable Z) {βhat : T → ℝ} (hβ : Measurable βhat) (n : ℕ) (c : ℝ) :
    Measurable (fun x : T × (Fin n → Ω) =>
      ENNReal.ofReal ((rawAverage Y Z n (βhat x.1) x.2 - c) ^ 2)) := by
  unfold rawAverage
  refine ENNReal.measurable_ofReal.comp ?_
  refine ((measurable_const.mul ?_).sub measurable_const).pow_const 2
  refine Finset.measurable_sum _ fun j _ => ?_
  have hj : Measurable (fun x : T × (Fin n → Ω) => x.2 j) :=
    (measurable_pi_apply j).comp measurable_snd
  exact (hY.comp hj).sub ((hβ.comp measurable_fst).mul (hZ.comp hj))

/-- Tonelli: the pilot risk is the `L q`-average of fixed-coefficient risks. -/
theorem pilotRisk_eq (hF : FixedFeatures π ρ Pplus Pminus Y Z v)
    {q : Fin k → ℝ} (hq : q ∈ rarityPolytope π ρ) {n : ℕ} (hn : 1 ≤ n)
    {T : Type*} [MeasurableSpace T] (L : (Fin k → ℝ) → Measure T) {βhat : T → ℝ}
    (hβ : Measurable βhat) :
    pilotRisk π Pplus Pminus Y Z n L βhat q =
      ∫⁻ t, ENNReal.ofReal
        (variance (fun ω => Y ω - βhat t * Z ω) (coinLaw π Pplus Pminus q) / n) ∂L q := by
  have := coinLaw_isProbability_of_mem hF hq
  unfold pilotRisk
  rw [lintegral_prod _
    (measurable_pilotIntegrand hF.2.2.2.1 hF.2.2.2.2.1 hβ n (signMass π q)).aemeasurable]
  refine lintegral_congr fun t => ?_
  exact fixedRisk_eq hF hq (βhat t) hn

end Features

end ThresholdHC.PilotCorrection
