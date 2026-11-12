import ThresholdHC.KnownLawPlanner.PlanRate

/-! The rate of a plan computed from upper bounds within a factor two.

The planner does not need the exact design integrals. Let its enclosure be
tight: the bounds for `H`, the unresolved mass, the resolved error and the
ordinary work are at most twice the true quantities, and the entropy bound is
at most four times the entropy. Band costs within a factor two give an
entropy within a factor two, and a logarithm bound within a factor two gives
the second factor.

The true resolved error at the least admissible cap of level `l+1` is at most
`δ_{l+1}/8 = δ_l/128`, so twice that passes the test of level `l`. The
searched cap of level `l` is therefore at most the least admissible cap of
level `l+1`, and the price of level `l` is at most four times the level work
certificate of level `l+1`. With `δ_l = 16 δ_{l+1}` the multilevel sum of
the upper theorem at terminal level `J+1` gives

  `Σ_{l ≤ J} √(17 δ_l k_l) ≤ 8 · 28000 (√(ρ Γ) + H)`,

for a terminal level `J` with `z ≤ δ_J/128`.

The unresolved mass `z` of the design is a parameter. It is the mass of `ζ`
for a law of positive gaps, and it includes the mass at zero of a reference
law that has one. No statement here needs `σ + τ + ζ` to be a probability
measure. -/

noncomputable section
open MeasureTheory Set Real Filter
open scoped NNReal ENNReal BigOperators Topology

namespace ThresholdHC.KnownLawPlanner
open ThresholdHC.Tier6 ThresholdHC.EntropyTailQuantile ThresholdHC.EntropyTailUpper
open ThresholdHC.EntropyTailAssembly ThresholdHC.ObservableSimulation ThresholdHC.RareAboveTwo
open ThresholdHC.EntropyTailExecution

/-- The ordinary work kernel does not decrease with the cap. -/
theorem ordinaryWorkKernel_mono {M P : ℝ} (hM : 0 < M) (hMP : M ≤ P) (d : Gap) :
    ordinaryWorkKernel M (d:ℝ) ≤ ordinaryWorkKernel P (d:ℝ) := by
  have hd := d.property.1
  have hlog : log (M*(d:ℝ)^2) ≤ log (P*(d:ℝ)^2) :=
    log_le_log (by positivity) (mul_le_mul_of_nonneg_right hMP (sq_nonneg _))
  have h17 : (0:ℝ) ≤ 17*(d:ℝ)⁻¹^2 := by positivity
  unfold ordinaryWorkKernel
  exact min_le_min hMP
    (mul_le_mul_of_nonneg_left (add_le_add le_rfl (max_le_max le_rfl hlog)) h17)

/-- The ordinary work of a finite measure does not decrease with the cap. -/
theorem ordinaryCost_mono (τ : Measure Gap) [IsFiniteMeasure τ] {M P : ℝ} (hM : 0 < M)
    (hMP : M ≤ P) : ordinaryCost τ M ≤ ordinaryCost τ P :=
  integral_mono (integrable_ordinaryWorkKernel τ hM.le)
    (integrable_ordinaryWorkKernel τ (hM.le.trans hMP)) fun d => ordinaryWorkKernel_mono hM hMP d

/-- The least admissible caps do not decrease with the level. -/
theorem errorCapExponent_succ_le (ν : Measure Gap) [IsFiniteMeasure ν] {ρ : ℝ} (hρ : 0 < ρ)
    (l : ℕ) :
    errorCapExponent ν (levelAccuracy ρ l) (levelAccuracy_pos hρ l) ≤
      errorCapExponent ν (levelAccuracy ρ (l+1)) (levelAccuracy_pos hρ (l+1)) := by
  have hs := errorCapExponent_spec ν (levelAccuracy_pos hρ (l+1))
  have hδ : levelAccuracy ρ (l+1)/8 ≤ levelAccuracy ρ l/8 := by
    rw [levelAccuracy_succ]
    linarith [levelAccuracy_pos hρ l]
  exact Nat.find_min' _ ⟨hs.1, hs.2.trans hδ⟩

/-- Band costs within a factor two give a cost entropy within a factor two. -/
theorem band_entropy_enclosure {N : ℕ} {a b : Fin N → ℝ} (ha : ∀ j, 0 ≤ a j)
    (hab : ∀ j, a j ≤ b j) (hb : ∀ j, b j ≤ 2 * a j) :
    costEntropy a ≤ costEntropy b ∧ costEntropy b ≤ 2 * costEntropy a := by
  refine ⟨costEntropy_mono ha hab, ?_⟩
  rw [← costEntropy_smul]
  exact costEntropy_mono (fun j => (ha j).trans (hab j)) hb

/-- A tight enclosure. Every bound is at most twice the design integral it
bounds, and the entropy bound is at most four times the entropy. `z` is the
unresolved mass of the design. The bounds on the resolved error and the
ordinary work are needed at the powers of four only. -/
def SplitEnclosure.Tight {σ τ ζ : Measure Gap} {N : ℕ} (E : SplitEnclosure σ τ ζ N)
    (z : ℝ) : Prop :=
  E.entropy ≤ 4 * costEntropy (fun j : Fin N => bandCost σ j.val) ∧
  E.tailInverse ≤ 2 * (∫ d : Gap, (d:ℝ)⁻¹ ∂τ) ∧
  z ≤ E.unresolved ∧ E.unresolved ≤ 2 * z ∧
  (∀ k : ℕ, E.resolvedError (4 ^ k) ≤ 2 * eta (σ+τ) (4 ^ k)) ∧
  ∀ k : ℕ, E.tailWork (4 ^ k) ≤ 2 * ordinaryCost τ (4 ^ k)

/-- The exact design integrals are a tight enclosure. -/
theorem SplitEnclosure.exact_tight (σ τ ζ : Measure Gap) (N : ℕ) :
    (SplitEnclosure.exact σ τ ζ N).Tight (ζ.real univ) := by
  have hΓ := costEntropy_nonneg (fun j : Fin N => bandCost_nonneg σ j.val)
  have hH : 0 ≤ ∫ d : Gap, (d:ℝ)⁻¹ ∂τ := integral_nonneg fun d => inv_nonneg.mpr d.property.1.le
  have hz : 0 ≤ ζ.real univ := measureReal_nonneg
  refine ⟨?_, ?_, le_rfl, ?_, fun k => ?_, fun k => ?_⟩
  · change costEntropy (fun j : Fin N => bandCost σ j.val) ≤ _
    linarith
  · change (∫ d : Gap, (d:ℝ)⁻¹ ∂τ) ≤ _
    linarith
  · change ζ.real univ ≤ _
    linarith
  · change eta (σ+τ) (4 ^ k) ≤ _
    linarith [eta_nonneg (σ+τ) (4 ^ k)]
  · change ordinaryCost τ (4 ^ k) ≤ _
    linarith [ordinaryCost_nonneg τ (by positivity : (0:ℝ) ≤ 4 ^ k)]

/-- The error envelope of a tight enclosure meets the termination requirement
of the cap search. -/
theorem SplitEnclosure.Tight.vanishes {σ τ ζ : Measure Gap} [IsFiniteMeasure σ]
    [IsFiniteMeasure τ] {N : ℕ} {E : SplitEnclosure σ τ ζ N} {z : ℝ} (hE : E.Tight z) :
    EnvelopeVanishes E.resolvedError := by
  intro ε hε k₀
  obtain ⟨k, hk, hle⟩ := eta_vanishes (σ+τ) (ε/2) (by positivity) k₀
  exact ⟨k, hk, (hE.2.2.2.2.1 k).trans (by linarith)⟩

/-- The searched cap of level `l` is at most the least admissible cap of
level `l+1`. -/
theorem tight_caps_le {σ τ ζ : Measure Gap} [IsFiniteMeasure σ] [IsFiniteMeasure τ] {N : ℕ}
    {E : SplitEnclosure σ τ ζ N} {z : ℝ} (hE : E.Tight z) {ρ : ℝ} (hρ : 0 < ρ) (l : ℕ) :
    searchCaps E.resolvedError hE.vanishes hρ l ≤
      errorCapExponent (σ+τ) (levelAccuracy ρ (l+1)) (levelAccuracy_pos hρ (l+1)) := by
  have key : ∀ l : ℕ, E.resolvedError
      (4 ^ errorCapExponent (σ+τ) (levelAccuracy ρ (l+1)) (levelAccuracy_pos hρ (l+1))) ≤
      levelAccuracy ρ l/8 := by
    intro l
    have hs := (errorCapExponent_spec (σ+τ) (levelAccuracy_pos hρ (l+1))).2
    have h2 := hE.2.2.2.2.1
      (errorCapExponent (σ+τ) (levelAccuracy ρ (l+1)) (levelAccuracy_pos hρ (l+1)))
    have hsucc := levelAccuracy_succ ρ l
    linarith [levelAccuracy_pos hρ l]
  induction l with
  | zero =>
    exact Nat.find_min' _
      ⟨(errorCapExponent_spec (σ+τ) (levelAccuracy_pos hρ (0+1))).1, key 0⟩
  | succ l ih =>
    exact Nat.find_min' _ ⟨ih.trans (errorCapExponent_succ_le (σ+τ) hρ (l+1)), key (l+1)⟩

/-- The price of level `l` of a tight enclosure, at its searched cap, is at
most four times the level work certificate of level `l+1`. -/
theorem tight_price_le {σ τ ζ : Measure Gap} [IsFiniteMeasure σ] [IsFiniteMeasure τ] {N : ℕ}
    {E : SplitEnclosure σ τ ζ N} {z : ℝ} (hE : E.Tight z) {ρ : ℝ} (hρ : 0 < ρ) (l : ℕ) :
    E.price ρ l (searchCaps E.resolvedError hE.vanishes hρ l) ≤
      4 * levelWorkCertificate σ τ ρ (costEntropy (fun j : Fin N => bandCost σ j.val)) z hρ
        (l+1) := by
  obtain ⟨hΓ4, hH2, hzE, hz2, -, hO2⟩ := hE
  have hcap := tight_caps_le (E := E) (z := z) ⟨hΓ4, hH2, hzE, hz2, ‹_›, hO2⟩ hρ l
  set κ := searchCaps E.resolvedError _ hρ l with hκ
  set k := errorCapExponent (σ+τ) (levelAccuracy ρ (l+1)) (levelAccuracy_pos hρ (l+1)) with hk
  have hΓ := costEntropy_nonneg (fun j : Fin N => bandCost_nonneg σ j.val)
  have hH : 0 ≤ ∫ d : Gap, (d:ℝ)⁻¹ ∂τ := integral_nonneg fun d => inv_nonneg.mpr d.property.1.le
  have hz0 : 0 ≤ z := by linarith
  have hH0 : 0 ≤ E.tailInverse := hH.trans E.tailInverse_le
  have h4κ : (0:ℝ) < 4 ^ κ := by positivity
  have h4 : (4:ℝ) ^ κ ≤ 4 ^ k := pow_le_pow_right₀ (by norm_num) hcap
  have hO := ordinaryCost_mono τ h4κ h4
  have hOk := ordinaryCost_nonneg τ (h4κ.le.trans h4)
  have hl : (0:ℝ) ≤ 128*((l:ℝ)+1) := by positivity
  have h1 : 128*((l:ℝ)+1)*E.entropy ≤
      4*(128*((l:ℝ)+1+1)*costEntropy (fun j : Fin N => bandCost σ j.val)) := by
    nlinarith [mul_le_mul_of_nonneg_left hΓ4 hl]
  have h2 : 6*E.tailInverse^2/ρ ≤ 4*(6*(∫ d : Gap, (d:ℝ)⁻¹ ∂τ)^2/ρ) := by
    have hsq : E.tailInverse^2 ≤ (2*∫ d : Gap, (d:ℝ)⁻¹ ∂τ)^2 := pow_le_pow_left₀ hH0 hH2 2
    rw [← mul_div_assoc]
    exact div_le_div_of_nonneg_right (by nlinarith) hρ.le
  have h3 : 2*E.tailWork (4 ^ κ) ≤ 4*(2*ordinaryCost τ (4 ^ k)) := by
    linarith [hO2 κ]
  have h5 : 2*E.unresolved*4 ^ κ ≤ 4*(2*z*4 ^ k) := by
    have ha : E.unresolved*4 ^ κ ≤ 2*z*4 ^ k :=
      mul_le_mul hz2 h4 h4κ.le (by linarith)
    nlinarith [mul_nonneg hz0 (h4κ.le.trans h4)]
  unfold SplitEnclosure.price levelWorkCertificate
  refine (min_le_right _ _).trans ?_
  push_cast
  linarith

/-- Every level price of an enclosure is positive when the resolved part has
positive mass. -/
theorem SplitEnclosure.price_pos {σ τ ζ : Measure Gap} [IsFiniteMeasure σ] [IsFiniteMeasure τ]
    {N : ℕ} (E : SplitEnclosure σ τ ζ N) {t ρ : ℝ} (ht : 0 < t)
    (hs : ∀ᵐ d : Gap ∂σ, t ≤ (d:ℝ)) (hN : bandEdge N < t) (hρ : 0 < ρ)
    (hm : 0 < (σ+τ).real univ) (l k : ℕ) : 0 < E.price ρ l k := by
  have hσ := inverseSquare_integrable_of_support σ ht hs
  have hΓ : (∫ d : Gap, (d:ℝ)⁻¹^2 ∂σ) ≤ costEntropy (fun j : Fin N => bandCost σ j.val) := by
    rw [inverseSquare_eq_band_total σ hs hN]
    exact costTotal_le_costEntropy (fun j => bandCost_nonneg σ j.val)
  have h4 : (1:ℝ) ≤ 4 ^ k := one_le_pow₀ (by norm_num)
  have hinv : ∀ d : Gap, (1:ℝ) ≤ (d:ℝ)⁻¹^2 := fun d => by
    have hd1 : (1:ℝ) ≤ (d:ℝ)⁻¹ := (one_le_inv₀ d.property.1).mpr (by linarith [d.property.2])
    nlinarith
  have hA : σ.real univ ≤ ∫ d : Gap, (d:ℝ)⁻¹^2 ∂σ := by
    have h := integral_mono (integrable_const (1:ℝ)) hσ hinv
    simpa using h
  have hO : τ.real univ ≤ ordinaryCost τ (4 ^ k) := by
    have h := integral_mono (integrable_const (1:ℝ))
      (integrable_ordinaryWorkKernel τ (by positivity : (0:ℝ) ≤ 4 ^ k)) (fun d : Gap => by
        show (1:ℝ) ≤ ordinaryWorkKernel (4 ^ k) (d:ℝ)
        unfold ordinaryWorkKernel
        refine le_min h4 ?_
        have hmax := le_max_left (0:ℝ) (log (4 ^ k*(d:ℝ)^2))
        nlinarith [hinv d])
    simpa [ordinaryCost] using h
  have hsum : (σ+τ).real univ = σ.real univ + τ.real univ := measureReal_add_apply
  have hz0 : 0 ≤ E.unresolved := measureReal_nonneg.trans E.unresolved_le
  have hE0 : 0 ≤ E.entropy := (hA.trans hΓ).trans E.entropy_le |> le_trans measureReal_nonneg
  have hl : σ.real univ ≤ 128*((l:ℝ)+1)*E.entropy := by
    have h1 : E.entropy ≤ 128*((l:ℝ)+1)*E.entropy := by
      nlinarith [Nat.cast_nonneg (α := ℝ) l]
    linarith [E.entropy_le]
  have hH0 : 0 ≤ 6*E.tailInverse^2/ρ := by positivity
  unfold SplitEnclosure.price
  refine lt_min (by positivity) ?_
  have hτ0 : 0 ≤ τ.real univ := measureReal_nonneg
  nlinarith [E.tailWork_le (4 ^ k), mul_nonneg hz0 (by positivity : (0:ℝ) ≤ 4 ^ k)]

/-- The multilevel sum of a plan computed from a tight enclosure:
`Σ_{l ≤ J} √(17 δ_l k_l) ≤ 8 · 28000 (√(ρ Γ) + H)`, for a terminal level with
`z ≤ δ_J/128`. -/
theorem tight_plan_spread (σ τ ζ : Measure Gap) [IsFiniteMeasure σ] [IsFiniteMeasure τ]
    {t ρ z : ℝ} {N : ℕ} (ht : 0 < t) (hs : ∀ᵐ d : Gap ∂σ, t ≤ (d:ℝ)) (hN : bandEdge N < t)
    (hτ : Integrable (fun d : Gap => (d:ℝ)⁻¹) τ) (hρ : 0 < ρ)
    (hm : ρ/128 < (σ+τ).real univ) (E : SplitEnclosure σ τ ζ N) (hE : E.Tight z) (J : ℕ)
    (hzJ : z ≤ levelAccuracy ρ J/128) :
    allocationCertificate (fun i : Fin (J+1) => 17*levelAccuracy ρ i.val)
        (planCost E ρ (searchCaps E.resolvedError hE.vanishes hρ) J) ≤
      224000*(sqrt (ρ*costEntropy (fun j : Fin N => bandCost σ j.val)) +
        ∫ d : Gap, (d:ℝ)⁻¹ ∂τ) := by
  have hz0 : 0 ≤ z := by linarith [hE.2.2.1, hE.2.2.2.1]
  have hΓ0 := costEntropy_nonneg (fun j : Fin N => bandCost_nonneg σ j.val)
  have hAΓ : (∫ d : Gap, (d:ℝ)⁻¹^2 ∂σ) ≤ costEntropy (fun j : Fin N => bandCost σ j.val) := by
    rw [inverseSquare_eq_band_total σ hs hN]
    exact costTotal_le_costEntropy (fun j => bandCost_nonneg σ j.val)
  have hzJ' : z ≤ levelAccuracy ρ (J+1)/8 := by
    rw [levelAccuracy_succ]
    linarith
  have h := multilevel_budget_certificate σ τ (inverseSquare_integrable_of_support σ ht hs) hτ
    hρ hΓ0 hz0 hAΓ hm (J+1) hzJ'
  set C := levelWorkCertificate σ τ ρ (costEntropy (fun j : Fin N => bandCost σ j.val)) z hρ
    with hC
  have hC0 : ∀ l, 0 ≤ C l := levelWorkCertificate_nonneg σ τ hρ hΓ0 hz0
  have hprice : ∀ l, E.price ρ l (searchCaps E.resolvedError hE.vanishes hρ l) ≤ 4 * C (l+1) :=
    fun l => tight_price_le hE hρ l
  have hterm : ∀ i : Fin (J+1),
      sqrt (17*levelAccuracy ρ i.val *
        planCost E ρ (searchCaps E.resolvedError hE.vanishes hρ) J i) ≤
      8 * sqrt (17*levelAccuracy ρ (i.val+1) * adjacentCost C (i.val+1)) := by
    intro i
    have hcost : planCost E ρ (searchCaps E.resolvedError hE.vanishes hρ) J i ≤
        4 * adjacentCost C (i.val+1) := by
      have hadj : adjacentCost C (i.val+1) = C (i.val+1) + C i.val := by
        simp [adjacentCost]
      rw [hadj]
      unfold planCost adjacentCost
      split_ifs with h0
      · have h1 := hprice i.val
        rw [h0] at h1 ⊢
        linarith [hC0 0]
      · have h1 := hprice i.val
        have h2 := hprice (i.val-1)
        have he : i.val - 1 + 1 = i.val := by omega
        rw [he] at h2
        linarith
    have hδ := (levelAccuracy_pos hρ (i.val+1)).le
    have h8 : (8:ℝ) = sqrt 64 := by
      rw [show (64:ℝ) = 8^2 by norm_num, sqrt_sq (by norm_num)]
    rw [h8, ← sqrt_mul (by norm_num)]
    apply sqrt_le_sqrt
    rw [levelAccuracy_succ] at hδ ⊢
    have hv : (0:ℝ) ≤ 17*levelAccuracy ρ i.val := by linarith
    nlinarith [mul_le_mul_of_nonneg_left hcost hv]
  unfold allocationCertificate
  calc ∑ i : Fin (J+1), sqrt (17*levelAccuracy ρ i.val *
        planCost E ρ (searchCaps E.resolvedError hE.vanishes hρ) J i)
      ≤ ∑ i : Fin (J+1), 8 * sqrt (17*levelAccuracy ρ (i.val+1) * adjacentCost C (i.val+1)) :=
        Finset.sum_le_sum fun i _ => hterm i
    _ = 8 * ∑ l ∈ Finset.range (J+1),
          sqrt (17*levelAccuracy ρ (l+1) * adjacentCost C (l+1)) := by
        rw [← Finset.mul_sum, Fin.sum_univ_eq_sum_range
          (fun l : ℕ => sqrt (17*levelAccuracy ρ (l+1) * adjacentCost C (l+1))) (J+1)]
    _ ≤ 8 * ∑ l ∈ Finset.range (J+1+1), sqrt (17*levelAccuracy ρ l * adjacentCost C l) := by
        rw [Finset.sum_range_succ' _ (J+1)]
        linarith [sqrt_nonneg (17*levelAccuracy ρ 0 * adjacentCost C 0)]
    _ ≤ 224000*(sqrt (ρ*costEntropy (fun j : Fin N => bandCost σ j.val)) +
          ∫ d : Gap, (d:ℝ)⁻¹ ∂τ) := by linarith

/-- The certified risk of a plan from a bound on its multilevel sum. With
weights within a factor `θ` of the optimal ones and `Σ_i √(17 δ_i k_i) ≤ S`,
the square root of the certificate is at most `δ_J + √θ · S/√B`. -/
theorem plan_rms_of_spread {ρ B θ S : ℝ} (hρ : 0 < ρ) (hB : 0 < B) (hθ : 0 ≤ θ) {J : ℕ}
    {k w : Fin (J+1) → ℝ} (hk : ∀ i, 0 < k i)
    (hlow : ∀ i, sqrt (17*levelAccuracy ρ i.val / k i) ≤ w i)
    (hup : ∀ i, w i ≤ θ * sqrt (17*levelAccuracy ρ i.val / k i))
    (hS : allocationCertificate (fun i : Fin (J+1) => 17*levelAccuracy ρ i.val) k ≤ S) :
    sqrt (planCertificate ρ (planRates B k w)) ≤ levelAccuracy ρ J + sqrt θ * S / sqrt B := by
  have hcert := planCertificate_le_of_weights hρ hB hk hlow hup
  have hS0 : 0 ≤ allocationCertificate (fun i : Fin (J+1) => 17*levelAccuracy ρ i.val) k :=
    Finset.sum_nonneg fun i _ => sqrt_nonneg _
  have hX0 := hS0.trans hS
  have hδ := (levelAccuracy_pos hρ J).le
  have hsB : 0 < sqrt B := sqrt_pos.mpr hB
  refine sqrt_le_iff.mpr ⟨by positivity, hcert.trans ?_⟩
  have hsq := pow_le_pow_left₀ hS0 hS 2
  have hterm : θ * (allocationCertificate (fun i : Fin (J+1) => 17*levelAccuracy ρ i.val) k) ^ 2
      / B ≤ (sqrt θ * S / sqrt B) ^ 2 := by
    rw [div_pow, mul_pow, sq_sqrt hθ, sq_sqrt hB.le]
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hsq hθ) hB.le
  nlinarith [mul_nonneg hδ (div_nonneg (mul_nonneg (sqrt_nonneg θ) hX0) hsB.le)]

/-- The certified risk of a plan computed from a tight enclosure, in the
design integrals: at most `δ_J + √θ · 224000 (√(ρ Γ) + H)/√B`. -/
theorem tight_plan_rms_le (σ τ ζ : Measure Gap) [IsFiniteMeasure σ] [IsFiniteMeasure τ]
    {t ρ B θ z : ℝ} {N : ℕ} (ht : 0 < t) (hs : ∀ᵐ d : Gap ∂σ, t ≤ (d:ℝ)) (hN : bandEdge N < t)
    (hτ : Integrable (fun d : Gap => (d:ℝ)⁻¹) τ) (hρ : 0 < ρ) (hB : 0 < B) (hθ : 0 ≤ θ)
    (hm : ρ/128 < (σ+τ).real univ) (E : SplitEnclosure σ τ ζ N) (hE : E.Tight z) (J : ℕ)
    (hzJ : z ≤ levelAccuracy ρ J/128) (w : Fin (J+1) → ℝ)
    (hlow : ∀ i, sqrt (17*levelAccuracy ρ i.val /
      planCost E ρ (searchCaps E.resolvedError hE.vanishes hρ) J i) ≤ w i)
    (hup : ∀ i, w i ≤ θ * sqrt (17*levelAccuracy ρ i.val /
      planCost E ρ (searchCaps E.resolvedError hE.vanishes hρ) J i)) :
    sqrt (planCertificate ρ (planRates B
        (planCost E ρ (searchCaps E.resolvedError hE.vanishes hρ) J) w)) ≤
      levelAccuracy ρ J + sqrt θ * (224000*(sqrt (ρ*costEntropy
        (fun j : Fin N => bandCost σ j.val)) + ∫ d : Gap, (d:ℝ)⁻¹ ∂τ)) / sqrt B := by
  have hm0 : 0 < (σ+τ).real univ := lt_trans (by positivity) hm
  have hk : ∀ i, 0 < planCost E ρ (searchCaps E.resolvedError hE.vanishes hρ) J i := by
    intro i
    unfold planCost adjacentCost
    split_ifs
    · exact E.price_pos ht hs hN hρ hm0 _ _
    · exact add_pos (E.price_pos ht hs hN hρ hm0 _ _) (E.price_pos ht hs hN hρ hm0 _ _)
  exact plan_rms_of_spread hρ hB hθ hk hlow hup
    (tight_plan_spread σ τ ζ ht hs hN hτ hρ hm E hE J hzJ)

/-- The terminal level chosen from the enclosure's unresolved mass. Outside
the constant fallback, `2048 z̄ ≤ ρ`, it covers the unresolved mass of the
design, `z ≤ δ_J/128`, and `δ_J < 4096 z + ρ/(1 + √B)`. -/
theorem tight_planTerminal {σ τ ζ : Measure Gap} {N : ℕ} {E : SplitEnclosure σ τ ζ N} {z : ℝ}
    (hE : E.Tight z) {ρ : ℝ} (hρ : 0 < ρ) (B : ℝ) (hz : 2048*E.unresolved ≤ ρ) :
    z ≤ levelAccuracy ρ (planTerminal hρ B E.unresolved)/128 ∧
      levelAccuracy ρ (planTerminal hρ B E.unresolved) < 4096*z + ρ/(1+sqrt B) := by
  obtain ⟨-, -, hzE, hz2, -, -⟩ := hE
  have hz0 : 0 ≤ E.unresolved := by linarith
  exact ⟨hzE.trans (planTerminal_unresolved hρ B hz),
    lt_of_lt_of_le (planTerminal_accuracy_lt hρ B hz0) (by linarith)⟩

end ThresholdHC.KnownLawPlanner
