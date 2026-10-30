import ThresholdHC.EntropyTail.Superadditive
import ThresholdHC.EntropyTail.Objective
import ThresholdHC.EntropyTail.Specification

/-! Lemma 13.1: hard measurable selections attain the selection infimum. A
submeasure `σ = f μ`, `f ≤ 1`, is approximated from below by the dyadic layer
mixture `N⁻¹ Σ_{k<N} μ|{f ≥ (k+1)/N}`, whose density is within `1/N` of `f`.
The entropy of a mixture dominates the mixture of entropies and the square
root is concave, so some layer is at least as good as `σ` up to `1/N`. -/
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace ThresholdHC.EntropyTail
open ThresholdHC.Tier6

/-! ### Band costs and prefix entropies -/

theorem bandCost_mono {σ₁ σ₂ : Measure Gap} (h : σ₁ ≤ σ₂) (j : ℕ) :
    bandCost σ₁ j ≤ bandCost σ₂ j :=
  lintegral_mono' (Measure.restrict_mono subset_rfl h) le_rfl

theorem bandCost_ne_top (σ : Measure Gap) [IsFiniteMeasure σ] (j : ℕ) : bandCost σ j ≠ ∞ := by
  have hb : ∀ d ∈ band j, ENNReal.ofReal (((d : ℝ)⁻¹)^2) ≤
      ENNReal.ofReal ((((1/2 : ℝ)^(j+2))⁻¹)^2) := by
    intro d hd
    simp only [band, Set.mem_ofPred_eq] at hd
    exact ENNReal.ofReal_le_ofReal
      (pow_le_pow_left₀ (inv_nonneg.2 d.2.1.le) (inv_anti₀ (by positivity) hd.1.le) 2)
  refine ne_top_of_le_ne_top ?_ (setLIntegral_mono' (measurableSet_band j) hb)
  rw [setLIntegral_const]
  exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top σ _)

theorem bandCost_sum_smul {ι : Type*} (s : Finset ι) (w : ι → ℝ≥0∞) (τ : ι → Measure Gap)
    (j : ℕ) : bandCost (∑ k ∈ s, w k • τ k) j = ∑ k ∈ s, w k * bandCost (τ k) j := by
  unfold bandCost
  rw [← lintegral_indicator (measurableSet_band j), lintegral_finsetSum_measure]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [lintegral_smul_measure, smul_eq_mul, lintegral_indicator (measurableSet_band j)]

/-- The entropy `G(a_0(σ),…,a_J(σ))` of a finite prefix. -/
def prefixEntropy (σ : Measure Gap) (J : ℕ) : ℝ :=
  costEntropy fun j : Fin (J+1) => (bandCost σ j).toReal

theorem prefixEntropy_nonneg (σ : Measure Gap) (J : ℕ) : 0 ≤ prefixEntropy σ J :=
  costEntropy_nonneg _ fun _ => ENNReal.toReal_nonneg

theorem ofReal_prefixEntropy_le_gamma (σ : Measure Gap) (J : ℕ) :
    ENNReal.ofReal (prefixEntropy σ J) ≤ gamma σ := by
  unfold gamma
  refine le_iSup_of_le J ?_
  split_ifs
  · exact le_rfl
  · exact le_top

theorem gamma_eq_iSup (σ : Measure Gap) [IsFiniteMeasure σ] :
    gamma σ = ⨆ J, ENNReal.ofReal (prefixEntropy σ J) := by
  unfold gamma
  exact iSup_congr fun J => ite_eq_left (fun j : Fin (J+1) => bandCost_ne_top σ j)

theorem costEntropy_prefix_le_succ (a : ℕ → ℝ) (ha : ∀ j, 0 ≤ a j) (J : ℕ) :
    costEntropy (fun j : Fin (J+1) => a j) ≤ costEntropy (fun j : Fin (J+2) => a j) := by
  let v : Fin (J+2) → ℝ := fun j => if (j : ℕ) ≤ J then a j else 0
  have h1 : ∀ i : Fin (J+1), v i.castSucc = a i := fun i => by
    simp [v, Nat.lt_succ_iff.1 i.2]
  have h2 : v (Fin.last (J+1)) = 0 := by simp [v]
  have hs : ∑ i, v i = ∑ i : Fin (J+1), a i := by
    rw [Fin.sum_univ_castSucc, h2, add_zero]
    exact Finset.sum_congr rfl fun i _ => h1 i
  have hv : costEntropy v = costEntropy (fun j : Fin (J+1) => a j) := by
    unfold costEntropy
    rw [hs, Fin.sum_univ_castSucc (fun j => v j * Real.log ((∑ i : Fin (J+1), a i) / v j)),
      h2, zero_mul, add_zero]
    congr 1
    exact Finset.sum_congr rfl fun i _ => by rw [h1]
  rw [← hv]
  refine costEntropy_mono (fun j => ?_) (fun j => ?_)
  · simp only [v]
    split_ifs
    · exact ha _
    · exact le_rfl
  · simp only [v]
    split_ifs
    · exact le_rfl
    · exact ha _

theorem prefixEntropy_mono (σ : Measure Gap) : Monotone (prefixEntropy σ) :=
  monotone_nat_of_le_succ fun J =>
    costEntropy_prefix_le_succ (fun j => (bandCost σ j).toReal) (fun _ => ENNReal.toReal_nonneg) J

theorem gamma_mono {σ₁ σ₂ : Measure Gap} [IsFiniteMeasure σ₂] (h : σ₁ ≤ σ₂) :
    gamma σ₁ ≤ gamma σ₂ := by
  have : IsFiniteMeasure σ₁ := isFiniteMeasure_of_le σ₂ h
  rw [gamma_eq_iSup, gamma_eq_iSup]
  refine iSup_mono fun J => ENNReal.ofReal_le_ofReal
    (costEntropy_mono (fun _ => ENNReal.toReal_nonneg) fun j => ?_)
  exact ENNReal.toReal_mono (bandCost_ne_top σ₂ j) (bandCost_mono h j)

/-- The entropy of a nonnegative mixture dominates the mixture of entropies. -/
theorem sum_smul_gamma_le {ι : Type*} (s : Finset ι) (w : ι → ℝ) (hw : ∀ k, 0 ≤ w k)
    (τ : ι → Measure Gap) [∀ k, IsFiniteMeasure (τ k)] :
    ∑ k ∈ s, ENNReal.ofReal (w k) * gamma (τ k) ≤
      gamma (∑ k ∈ s, ENNReal.ofReal (w k) • τ k) := by
  have hp : ∀ J, ∑ k ∈ s, w k * prefixEntropy (τ k) J ≤
      prefixEntropy (∑ k ∈ s, ENNReal.ofReal (w k) • τ k) J := by
    intro J
    have hvec : (fun j : Fin (J+1) =>
        (bandCost (∑ k ∈ s, ENNReal.ofReal (w k) • τ k) j).toReal) =
        ∑ k ∈ s, w k • fun j : Fin (J+1) => (bandCost (τ k) j).toReal := by
      funext j
      rw [bandCost_sum_smul, ENNReal.toReal_sum fun k _ =>
        ENNReal.mul_ne_top ENNReal.ofReal_ne_top (bandCost_ne_top (τ k) j), Finset.sum_apply]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (hw k), Pi.smul_apply, smul_eq_mul]
    unfold prefixEntropy
    rw [hvec]
    exact sum_smul_costEntropy_le s w _ (fun k _ => hw k) fun _ _ _ => ENNReal.toReal_nonneg
  calc ∑ k ∈ s, ENNReal.ofReal (w k) * gamma (τ k)
      = ∑ k ∈ s, ⨆ J, ENNReal.ofReal (w k * prefixEntropy (τ k) J) := by
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [gamma_eq_iSup, ENNReal.mul_iSup]
        exact iSup_congr fun J => (ENNReal.ofReal_mul (hw k)).symm
    _ = ⨆ J, ∑ k ∈ s, ENNReal.ofReal (w k * prefixEntropy (τ k) J) :=
        ENNReal.finsetSum_iSup_of_monotone fun k _ _ hJ =>
          ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left (prefixEntropy_mono _ hJ) (hw k))
    _ ≤ ⨆ J, ENNReal.ofReal (prefixEntropy (∑ k ∈ s, ENNReal.ofReal (w k) • τ k) J) :=
        iSup_mono fun J => by
          rw [← ENNReal.ofReal_sum_of_nonneg fun k _ =>
            mul_nonneg (hw k) (prefixEntropy_nonneg _ _)]
          exact ENNReal.ofReal_le_ofReal (hp J)
    _ ≤ _ := iSup_le fun J => ofReal_prefixEntropy_le_gamma _ J

/-! ### The truncated inverse-gap cost -/

theorem measurable_tailWeight (h : ℝ) :
    Measurable fun d : Gap => ENNReal.ofReal (min 1 (h / (d : ℝ))) :=
  (measurable_const.min (measurable_const.div measurable_subtype_coe)).ennreal_ofReal

theorem tailCost_le_mass (τ : Measure Gap) (h : ℝ) : tailCost τ h ≤ τ Set.univ := by
  unfold tailCost
  calc ∫⁻ d, ENNReal.ofReal (min 1 (h / (d : ℝ))) ∂τ ≤ ∫⁻ _, 1 ∂τ :=
        lintegral_mono fun d => by simp
    _ = τ Set.univ := lintegral_one

theorem tailCost_sum_smul {ι : Type*} (s : Finset ι) (w : ι → ℝ≥0∞) (τ : ι → Measure Gap)
    (h : ℝ) : tailCost (∑ k ∈ s, w k • τ k) h = ∑ k ∈ s, w k * tailCost (τ k) h := by
  unfold tailCost
  rw [lintegral_finsetSum_measure]
  exact Finset.sum_congr rfl fun k _ => by rw [lintegral_smul_measure, smul_eq_mul]

/-- The objective of a submeasure with finite entropy, as a real number. -/
theorem objective_eq_ofReal {μ τ : Measure Gap} [IsProbabilityMeasure μ] (hτ : τ ≤ μ)
    {ρ B γ : ℝ} (hρ : 0 ≤ ρ) (hγ0 : 0 ≤ γ) (hγ : gamma τ = ENNReal.ofReal γ) :
    selectionObjective μ ρ B τ = ENNReal.ofReal (1 / Real.sqrt B * Real.sqrt (ρ * γ) +
      ((tailCost μ (1 / Real.sqrt B)).toReal - (tailCost τ (1 / Real.sqrt B)).toReal)) := by
  have : IsFiniteMeasure τ := isFiniteMeasure_of_le μ hτ
  have hTτ : tailCost τ (1 / Real.sqrt B) ≠ ∞ :=
    ne_top_of_le_ne_top (measure_ne_top τ _) (tailCost_le_mass _ _)
  have hTμ : tailCost μ (1 / Real.sqrt B) ≠ ∞ :=
    ne_top_of_le_ne_top (measure_ne_top μ _) (tailCost_le_mass _ _)
  have hadd := tailCost_sub_add hτ (1 / Real.sqrt B)
  have hle : (tailCost τ (1 / Real.sqrt B)).toReal ≤ (tailCost μ (1 / Real.sqrt B)).toReal := by
    rw [← hadd] at hTμ ⊢
    exact ENNReal.toReal_mono hTμ le_add_self
  have hh : 0 ≤ 1 / Real.sqrt B := by positivity
  unfold selectionObjective
  rw [hγ, entropyTerm_ofReal hh hρ hγ0,
    ENNReal.ofReal_add (mul_nonneg hh (Real.sqrt_nonneg _)) (sub_nonneg.2 hle),
    ENNReal.ofReal_sub _ ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hTμ,
    ENNReal.ofReal_toReal hTτ]
  congr 1
  exact ENNReal.eq_sub_of_add_eq hTτ hadd

/-! ### Dyadic layers -/

/-- The layer `{f ≥ (k+1)/N}`. -/
def layer (f : Gap → ℝ≥0∞) (N k : ℕ) : Set Gap := {x | ((k + 1 : ℕ) : ℝ≥0∞) / N ≤ f x}

/-- The density `N⁻¹ #{k < N : f ≥ (k+1)/N}`. -/
def layerDensity (f : Gap → ℝ≥0∞) (N : ℕ) (x : Gap) : ℝ≥0∞ :=
  ∑ k ∈ Finset.range N, (layer f N k).indicator (fun _ => ENNReal.ofReal (1 / N)) x

/-- The hard-selection mixture `N⁻¹ Σ_{k<N} μ|{f ≥ (k+1)/N}`. -/
def layerMixture (μ : Measure Gap) (f : Gap → ℝ≥0∞) (N : ℕ) : Measure Gap :=
  ∑ k ∈ Finset.range N, ENNReal.ofReal (1 / N) • μ.restrict (layer f N k)

theorem measurableSet_layer {f : Gap → ℝ≥0∞} (hf : Measurable f) (N k : ℕ) :
    MeasurableSet (layer f N k) :=
  measurableSet_le measurable_const hf

/-- Where `f ≤ 1`, the layer density lies in `[f - 1/N, f]`. -/
theorem layerDensity_bounds {f : Gap → ℝ≥0∞} {N : ℕ} (hN : 0 < N) {x : Gap} (hx : f x ≤ 1) :
    layerDensity f N x ≤ f x ∧ f x ≤ layerDensity f N x + ENNReal.ofReal (1 / N) := by
  have hNr : (0 : ℝ) < N := Nat.cast_pos.2 hN
  have hfx : f x = ENNReal.ofReal (f x).toReal :=
    (ENNReal.ofReal_toReal (ne_top_of_le_ne_top ENNReal.one_ne_top hx)).symm
  have hr0 : 0 ≤ (f x).toReal := ENNReal.toReal_nonneg
  have hr1 : (f x).toReal ≤ 1 := by simpa using ENNReal.toReal_mono ENNReal.one_ne_top hx
  generalize (f x).toReal = r at hfx hr0 hr1
  have hrN : 0 ≤ r * N := mul_nonneg hr0 hNr.le
  have hmN : ⌊r * N⌋₊ ≤ N := by
    have h1 : r * N ≤ N := by nlinarith
    calc ⌊r * N⌋₊ ≤ ⌊(N : ℝ)⌋₊ := Nat.floor_le_floor h1
      _ = N := Nat.floor_natCast N
  have hmem : ∀ k, x ∈ layer f N k ↔ k < ⌊r * N⌋₊ := by
    intro k
    simp only [layer, Set.mem_ofPred_eq, hfx]
    rw [show ((k + 1 : ℕ) : ℝ≥0∞) / N = ENNReal.ofReal (((k + 1 : ℕ) : ℝ) / N) by
        rw [ENNReal.ofReal_div_of_pos hNr, ENNReal.ofReal_natCast, ENNReal.ofReal_natCast],
      ENNReal.ofReal_le_ofReal_iff hr0, div_le_iff₀ hNr, ← Nat.le_floor_iff hrN]
    omega
  have hsum : layerDensity f N x = ENNReal.ofReal (⌊r * N⌋₊ / N) := by
    unfold layerDensity
    have hite : ∀ k ∈ Finset.range N,
        (layer f N k).indicator (fun _ => ENNReal.ofReal (1 / N)) x =
          if k < ⌊r * N⌋₊ then ENNReal.ofReal (1 / N) else 0 := fun k _ => by
      by_cases hk : x ∈ layer f N k
      · rw [Set.indicator_of_mem hk, ite_eq_left ((hmem k).1 hk)]
      · rw [Set.indicator_of_notMem hk, ite_eq_right fun h => hk ((hmem k).2 h)]
    rw [Finset.sum_congr rfl hite, ← Finset.sum_filter]
    have hfil : (Finset.range N).filter (fun k => k < ⌊r * N⌋₊) = Finset.range ⌊r * N⌋₊ := by
      ext k
      simp only [Finset.mem_filter, Finset.mem_range]
      omega
    rw [hfil, Finset.sum_const, Finset.card_range, nsmul_eq_mul, ← ENNReal.ofReal_natCast,
      ← ENNReal.ofReal_mul (Nat.cast_nonneg _), mul_one_div]
  rw [hsum, hfx]
  constructor
  · refine ENNReal.ofReal_le_ofReal ?_
    rw [div_le_iff₀ hNr]
    exact Nat.floor_le hrN
  · rw [← ENNReal.ofReal_add (div_nonneg (Nat.cast_nonneg _) hNr.le) (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [← add_div, le_div_iff₀ hNr]
    exact (Nat.lt_floor_add_one (r * N)).le

theorem lintegral_layerMixture (μ : Measure Gap) {f : Gap → ℝ≥0∞} (hf : Measurable f) (N : ℕ)
    {φ : Gap → ℝ≥0∞} (hφ : Measurable φ) :
    ∫⁻ x, φ x ∂(layerMixture μ f N) = ∫⁻ x, layerDensity f N x * φ x ∂μ := by
  classical
  have hL := measurableSet_layer hf N
  unfold layerMixture layerDensity
  rw [lintegral_finsetSum_measure]
  simp_rw [Finset.sum_mul]
  rw [lintegral_finsetSum]
  swap
  · exact fun k _ => (measurable_const.indicator (hL k)).mul hφ
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [lintegral_smul_measure, smul_eq_mul, ← lintegral_const_mul _ hφ,
    ← lintegral_indicator (hL k)]
  refine lintegral_congr fun x => ?_
  simp only [Set.indicator_apply]
  split_ifs <;> simp

theorem measurable_layerDensity {f : Gap → ℝ≥0∞} (hf : Measurable f) (N : ℕ) :
    Measurable (layerDensity f N) :=
  Finset.measurable_sum _ fun k _ => measurable_const.indicator (measurableSet_layer hf N k)

/-! ### Averaging over the layers -/

theorem sum_mul_sqrt_le {ι : Type*} (s : Finset ι) (w x : ι → ℝ) (hw : ∀ k ∈ s, 0 ≤ w k)
    (h1 : ∑ k ∈ s, w k = 1) (hx : ∀ k ∈ s, 0 ≤ x k) :
    ∑ k ∈ s, w k * Real.sqrt (x k) ≤ Real.sqrt (∑ k ∈ s, w k * x k) := by
  simpa only [smul_eq_mul] using
    Real.strictConcaveOn_sqrt.concaveOn.le_map_sum hw h1 fun k hk => Set.mem_Ici.2 (hx k hk)

/-- At dyadic level `N`, some hard selection is within `1/N` of `σ`. -/
theorem hard_le_objective_add {μ σ : Measure Gap} [IsProbabilityMeasure μ] (hσ : σ ≤ μ)
    {ρ B : ℝ} (hρ : 0 < ρ) (hB : 0 < B) {N : ℕ} (hN : 0 < N) :
    (⨅ (S : Set Gap) (_ : MeasurableSet S), selectionObjective μ ρ B (μ.restrict S)) ≤
      selectionObjective μ ρ B σ + ENNReal.ofReal (1 / N) := by
  have : IsFiniteMeasure σ := isFiniteMeasure_of_le μ hσ
  obtain ⟨f, hfm, rfl, hf1⟩ : ∃ f : Gap → ℝ≥0∞, Measurable f ∧ μ.withDensity f = σ ∧
      ∀ᵐ x ∂μ, f x ≤ 1 :=
    ⟨σ.rnDeriv μ, Measure.measurable_rnDeriv σ μ,
      Measure.withDensity_rnDeriv_eq σ μ (Measure.absolutelyContinuous_of_le hσ),
      Measure.rnDeriv_le_one_of_le hσ⟩
  have : IsFiniteMeasure (μ.withDensity f) := isFiniteMeasure_of_le μ hσ
  have hh : 0 < 1 / Real.sqrt B := one_div_pos.2 (Real.sqrt_pos.2 hB)
  have hNr : (0 : ℝ) < N := Nat.cast_pos.2 hN
  have hc : 0 < 1 / (N : ℝ) := one_div_pos.2 hNr
  have hL := measurableSet_layer hfm N
  have hgf : ∀ᵐ x ∂μ, layerDensity f N x ≤ f x ∧
      f x ≤ layerDensity f N x + ENNReal.ofReal (1 / N) := by
    filter_upwards [hf1] with x hx
    exact layerDensity_bounds hN hx
  -- the layer mixture lies below `σ`
  have hmix_le : layerMixture μ f N ≤ μ.withDensity f := by
    rw [Measure.le_iff]
    intro A hA
    rw [← lintegral_indicator_one hA, ← lintegral_indicator_one hA,
      lintegral_withDensity_eq_lintegral_mul μ hfm (measurable_one.indicator hA),
      lintegral_layerMixture μ hfm N (measurable_one.indicator hA)]
    refine lintegral_mono_ae ?_
    filter_upwards [hgf] with x hx
    exact mul_le_mul_left hx.1 _
  -- its remainder cost is at most `1/N` larger
  have hw := measurable_tailWeight (1 / Real.sqrt B)
  have htail : tailCost (μ.withDensity f) (1 / Real.sqrt B) ≤
      tailCost (layerMixture μ f N) (1 / Real.sqrt B) + ENNReal.ofReal (1 / N) := by
    have hμw : tailCost μ (1 / Real.sqrt B) ≤ 1 := (tailCost_le_mass μ _).trans (by simp)
    unfold tailCost at hμw ⊢
    rw [lintegral_withDensity_eq_lintegral_mul μ hfm hw, lintegral_layerMixture μ hfm N hw]
    calc ∫⁻ x, (f * fun d : Gap => ENNReal.ofReal (min 1 (1 / Real.sqrt B / (d : ℝ)))) x ∂μ
        ≤ ∫⁻ x, (layerDensity f N x + ENNReal.ofReal (1 / N)) *
            ENNReal.ofReal (min 1 (1 / Real.sqrt B / (x : ℝ))) ∂μ := by
          refine lintegral_mono_ae ?_
          filter_upwards [hgf] with x hx
          exact mul_le_mul_left hx.2 _
      _ = ∫⁻ x, layerDensity f N x * ENNReal.ofReal (min 1 (1 / Real.sqrt B / (x : ℝ))) ∂μ +
            ENNReal.ofReal (1 / N) *
              ∫⁻ x, ENNReal.ofReal (min 1 (1 / Real.sqrt B / (x : ℝ))) ∂μ := by
          simp_rw [add_mul]
          rw [lintegral_add_left, lintegral_const_mul _ hw]
          exact (measurable_layerDensity hfm N).mul hw
      _ ≤ _ := by
          gcongr
          calc ENNReal.ofReal (1 / N) *
                ∫⁻ x, ENNReal.ofReal (min 1 (1 / Real.sqrt B / (x : ℝ))) ∂μ
              ≤ ENNReal.ofReal (1 / N) * 1 := mul_le_mul_right hμw _
            _ = ENNReal.ofReal (1 / N) := mul_one _
  -- entropies
  have : ∀ k, IsFiniteMeasure (μ.restrict (layer f N k)) := fun k => inferInstance
  have hmixΓ : ∑ k ∈ Finset.range N, ENNReal.ofReal (1 / N) * gamma (μ.restrict (layer f N k)) ≤
      gamma (μ.withDensity f) :=
    (sum_smul_gamma_le (Finset.range N) (fun _ => 1 / (N : ℝ)) (fun _ => hc.le)
      (fun k => μ.restrict (layer f N k))).trans (gamma_mono hmix_le)
  rcases eq_or_ne (gamma (μ.withDensity f)) ∞ with hinf | hfin
  · have htop : selectionObjective μ ρ B (μ.withDensity f) = ∞ := by
      unfold selectionObjective
      rw [hinf, ENNReal.mul_top (ENNReal.ofReal_pos.2 hρ).ne',
        ENNReal.top_rpow_of_pos (by norm_num), ENNReal.mul_top (ENNReal.ofReal_pos.2 hh).ne',
        top_add]
    rw [htop, top_add]
    exact le_top
  -- real quantities
  have hγk : ∀ k ∈ Finset.range N, gamma (μ.restrict (layer f N k)) ≠ ∞ := by
    intro k hk htop
    have hle : ENNReal.ofReal (1 / N) * gamma (μ.restrict (layer f N k)) ≤
        gamma (μ.withDensity f) :=
      (Finset.single_le_sum (f := fun i => ENNReal.ofReal (1 / N) *
        gamma (μ.restrict (layer f N i))) (fun i _ => zero_le) hk).trans hmixΓ
    rw [htop, ENNReal.mul_top (ENNReal.ofReal_pos.2 hc).ne', top_le_iff] at hle
    exact hfin hle
  set T : Measure Gap → ℝ := fun ν => (tailCost ν (1 / Real.sqrt B)).toReal with hT
  have hTfin : ∀ ν : Measure Gap, IsFiniteMeasure ν → tailCost ν (1 / Real.sqrt B) ≠ ∞ :=
    fun ν _ => ne_top_of_le_ne_top (measure_ne_top ν _) (tailCost_le_mass _ _)
  have hobjk : ∀ k ∈ Finset.range N, selectionObjective μ ρ B (μ.restrict (layer f N k)) =
      ENNReal.ofReal (1 / Real.sqrt B * Real.sqrt (ρ * (gamma (μ.restrict (layer f N k))).toReal) +
        (T μ - T (μ.restrict (layer f N k)))) := fun k hk =>
    objective_eq_ofReal Measure.restrict_le_self hρ.le ENNReal.toReal_nonneg
      (ENNReal.ofReal_toReal (hγk k hk)).symm
  have hobjσ : selectionObjective μ ρ B (μ.withDensity f) =
      ENNReal.ofReal (1 / Real.sqrt B * Real.sqrt (ρ * (gamma (μ.withDensity f)).toReal) +
        (T μ - T (μ.withDensity f))) :=
    objective_eq_ofReal hσ hρ.le ENNReal.toReal_nonneg (ENNReal.ofReal_toReal hfin).symm
  -- the average over layers
  have hΓreal : ∑ k ∈ Finset.range N, 1 / (N : ℝ) * (gamma (μ.restrict (layer f N k))).toReal ≤
      (gamma (μ.withDensity f)).toReal := by
    rw [← ENNReal.ofReal_le_ofReal_iff ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hfin,
      ENNReal.ofReal_sum_of_nonneg fun k _ => mul_nonneg hc.le ENNReal.toReal_nonneg]
    refine le_trans (le_of_eq (Finset.sum_congr rfl fun k hk => ?_)) hmixΓ
    rw [ENNReal.ofReal_mul hc.le, ENNReal.ofReal_toReal (hγk k hk)]
  have hTmix : T (layerMixture μ f N) =
      ∑ k ∈ Finset.range N, 1 / (N : ℝ) * T (μ.restrict (layer f N k)) := by
    simp only [hT]
    unfold layerMixture
    rw [tailCost_sum_smul, ENNReal.toReal_sum fun k _ =>
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hTfin (μ.restrict (layer f N k)) inferInstance)]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hc.le]
  have hTσ : T (μ.withDensity f) ≤ T (layerMixture μ f N) + 1 / N := by
    have : IsFiniteMeasure (layerMixture μ f N) := isFiniteMeasure_of_le _ hmix_le
    have h1 := hTfin (μ.withDensity f) inferInstance
    have h2 := hTfin (layerMixture μ f N) inferInstance
    simp only [hT]
    rw [← ENNReal.ofReal_le_ofReal_iff (by positivity), ENNReal.ofReal_toReal h1,
      ENNReal.ofReal_add ENNReal.toReal_nonneg hc.le, ENNReal.ofReal_toReal h2]
    exact htail
  have hTle : ∀ ν : Measure Gap, ν ≤ μ → T ν ≤ T μ := by
    intro ν hν
    have : IsFiniteMeasure ν := isFiniteMeasure_of_le μ hν
    simp only [hT]
    have hadd := tailCost_sub_add hν (1 / Real.sqrt B)
    have hfin' := hTfin μ inferInstance
    rw [← hadd] at hfin' ⊢
    exact ENNReal.toReal_mono hfin' le_add_self
  have hwsum : ∑ _k ∈ Finset.range N, 1 / (N : ℝ) = 1 := by
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one_div, div_self hNr.ne']
  have hreal : ∑ k ∈ Finset.range N, 1 / (N : ℝ) *
        (1 / Real.sqrt B * Real.sqrt (ρ * (gamma (μ.restrict (layer f N k))).toReal) +
          (T μ - T (μ.restrict (layer f N k)))) ≤
      1 / Real.sqrt B * Real.sqrt (ρ * (gamma (μ.withDensity f)).toReal) +
        (T μ - T (μ.withDensity f)) + 1 / N := by
    have hsq : ∑ k ∈ Finset.range N, 1 / (N : ℝ) *
        Real.sqrt (gamma (μ.restrict (layer f N k))).toReal ≤
        Real.sqrt (∑ k ∈ Finset.range N, 1 / (N : ℝ) *
          (gamma (μ.restrict (layer f N k))).toReal) :=
      sum_mul_sqrt_le (Finset.range N) (fun _ => 1 / (N : ℝ))
        (fun k => (gamma (μ.restrict (layer f N k))).toReal) (fun _ _ => hc.le) hwsum
        (fun _ _ => ENNReal.toReal_nonneg)
    have hmono := Real.sqrt_le_sqrt hΓreal
    have hsplit : ∀ x : ℝ, 0 ≤ x → Real.sqrt (ρ * x) = Real.sqrt ρ * Real.sqrt x :=
      fun x _ => Real.sqrt_mul hρ.le x
    simp only [mul_add, Finset.sum_add_distrib, mul_sub, Finset.sum_sub_distrib]
    simp only [hsplit _ ENNReal.toReal_nonneg]
    have h1 : ∑ k ∈ Finset.range N, 1 / (N : ℝ) * (1 / Real.sqrt B *
        (Real.sqrt ρ * Real.sqrt (gamma (μ.restrict (layer f N k))).toReal)) =
        1 / Real.sqrt B * Real.sqrt ρ * ∑ k ∈ Finset.range N,
          1 / (N : ℝ) * Real.sqrt (gamma (μ.restrict (layer f N k))).toReal := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun k _ => by ring
    have h2 : ∑ k ∈ Finset.range N, 1 / (N : ℝ) * T μ = T μ := by
      rw [← Finset.sum_mul, hwsum, one_mul]
    rw [h1, h2, ← hTmix]
    have hhr : 0 ≤ 1 / Real.sqrt B * Real.sqrt ρ := by positivity
    nlinarith [mul_le_mul_of_nonneg_left (hsq.trans hmono) hhr, hTσ]
  -- conclude
  have hI : ∀ k ∈ Finset.range N,
      (⨅ (S : Set Gap) (_ : MeasurableSet S), selectionObjective μ ρ B (μ.restrict S)) ≤
        selectionObjective μ ρ B (μ.restrict (layer f N k)) := fun k _ =>
    iInf₂_le (f := fun S (_ : MeasurableSet S) => selectionObjective μ ρ B (μ.restrict S))
      (layer f N k) (hL k)
  have hone : ∑ _k ∈ Finset.range N, ENNReal.ofReal (1 / N) = 1 := by
    rw [← ENNReal.ofReal_sum_of_nonneg fun _ _ => hc.le, hwsum, ENNReal.ofReal_one]
  calc (⨅ (S : Set Gap) (_ : MeasurableSet S), selectionObjective μ ρ B (μ.restrict S))
      = ∑ _k ∈ Finset.range N, ENNReal.ofReal (1 / N) *
          (⨅ (S : Set Gap) (_ : MeasurableSet S), selectionObjective μ ρ B (μ.restrict S)) := by
        rw [← Finset.sum_mul, hone, one_mul]
    _ ≤ ∑ k ∈ Finset.range N, ENNReal.ofReal (1 / N) *
          selectionObjective μ ρ B (μ.restrict (layer f N k)) :=
        Finset.sum_le_sum fun k hk => mul_le_mul_right (hI k hk) _
    _ = ENNReal.ofReal (∑ k ∈ Finset.range N, 1 / (N : ℝ) *
          (1 / Real.sqrt B * Real.sqrt (ρ * (gamma (μ.restrict (layer f N k))).toReal) +
            (T μ - T (μ.restrict (layer f N k))))) := by
        rw [ENNReal.ofReal_sum_of_nonneg fun k _ => mul_nonneg hc.le
          (add_nonneg (by positivity) (sub_nonneg.2 (hTle _ Measure.restrict_le_self)))]
        refine Finset.sum_congr rfl fun k hk => ?_
        rw [hobjk k hk, ← ENNReal.ofReal_mul hc.le]
    _ ≤ ENNReal.ofReal (1 / Real.sqrt B * Real.sqrt (ρ * (gamma (μ.withDensity f)).toReal) +
          (T μ - T (μ.withDensity f)) + 1 / N) := ENNReal.ofReal_le_ofReal hreal
    _ = selectionObjective μ ρ B (μ.withDensity f) + ENNReal.ofReal (1 / N) := by
        rw [hobjσ, ENNReal.ofReal_add (add_nonneg (by positivity) (sub_nonneg.2 (hTle _ hσ)))
          hc.le]

theorem hard_selection : HardSelectionStatement := by
  intro ρ B hρ _ hB μ _
  refine le_antisymm ?_ ?_
  · exact le_iInf₂ fun S _ => iInf₂_le (f := fun σ (_ : σ ≤ μ) => selectionObjective μ ρ B σ)
      (μ.restrict S) Measure.restrict_le_self
  · refine le_iInf₂ fun σ hσ => ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
    obtain ⟨N, hN⟩ := exists_nat_one_div_lt (NNReal.coe_pos.2 hε)
    refine (hard_le_objective_add hσ hρ hB (Nat.succ_pos N)).trans (add_le_add le_rfl ?_)
    rw [← ENNReal.ofReal_coe_nnreal]
    exact ENNReal.ofReal_le_ofReal (by simpa using hN.le)

end ThresholdHC.EntropyTail
