import ThresholdHC.GlobalCut.Specification
import ThresholdHC.EntropyTail.HardSelection
import ThresholdHC.EntropyTail.Bridge
import ThresholdHC.EntropyTailQuantile.CutDecomposition
import ThresholdHC.EntropyTailQuantile.QuantileFeasible
import ThresholdHC.QuantileSelection.Full

/-! Proof of Corollary 6 and of the identification of `V` on finite laws.
Every cut is an admissible selection, so `K ≤ V`. The quantile core is the
convex combination `r μ|{t < d} + (1-r) μ|{t ≤ d}` of two cuts at the
quantile threshold `t`, with `r` the quantile boundary fraction. The entropy
dominates the mixture of entropies, the square root is concave and the
remainder cost is affine, so the core objective is at least the same
combination of the two cut objectives, hence at least their minimum. -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace ThresholdHC.GlobalCut
open ThresholdHC.Tier6 (Gap)
open ThresholdHC.EntropyTail

/-- Every cut is an admissible selection: `K ≤ V` for every measure. -/
theorem selection_le_globalCutValue (μ : Measure Gap) (ρ B : ℝ) :
    selection μ ρ B ≤ globalCutValue μ ρ B := by
  unfold selection globalCutValue
  apply min_le_min_left
  refine le_iInf fun t => ?_
  refine le_min ?_ ?_
  · exact iInf₂_le (μ.restrict {d : Gap | t < (d : ℝ)})
      (Measure.restrict_le_self (μ := μ))
  · exact iInf₂_le (μ.restrict {d : Gap | t ≤ (d : ℝ)})
      (Measure.restrict_le_self (μ := μ))

/-- Concavity of the square root on `[0,∞]`, for a two-point mixture. -/
theorem rpow_half_mix {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (x y : ℝ≥0∞) :
    ENNReal.ofReal r * x ^ (1/2 : ℝ) + ENNReal.ofReal (1-r) * y ^ (1/2 : ℝ) ≤
      (ENNReal.ofReal r * x + ENNReal.ofReal (1-r) * y) ^ (1/2 : ℝ) := by
  rcases eq_or_ne x ⊤ with rfl | hx
  · rcases hr0.eq_or_lt with h0 | hpos
    · subst h0
      simp
    · rw [ENNReal.mul_top (ENNReal.ofReal_pos.2 hpos).ne', top_add,
        ENNReal.top_rpow_of_pos (by norm_num)]
      exact le_top
  rcases eq_or_ne y ⊤ with rfl | hy
  · rcases (sub_nonneg.2 hr1).eq_or_lt with h0 | hpos
    · have h1 : r = 1 := by linarith
      subst h1
      simp
    · rw [ENNReal.mul_top (ENNReal.ofReal_pos.2 hpos).ne', add_top,
        ENNReal.top_rpow_of_pos (by norm_num)]
      exact le_top
  have hs : 0 ≤ 1 - r := sub_nonneg.2 hr1
  have key : ∀ c z : ℝ, 0 ≤ c → 0 ≤ z →
      ENNReal.ofReal c * ENNReal.ofReal z ^ (1/2 : ℝ) = ENNReal.ofReal (c * Real.sqrt z) :=
    fun c z hc hz => by
      rw [ENNReal.ofReal_rpow_of_nonneg hz (by norm_num), ← Real.sqrt_eq_rpow,
        ← ENNReal.ofReal_mul hc]
  rw [← ENNReal.ofReal_toReal hx, ← ENNReal.ofReal_toReal hy,
    key r _ hr0 ENNReal.toReal_nonneg, key (1-r) _ hs ENNReal.toReal_nonneg,
    ← ENNReal.ofReal_mul hr0, ← ENNReal.ofReal_mul hs,
    ← ENNReal.ofReal_add (mul_nonneg hr0 ENNReal.toReal_nonneg)
      (mul_nonneg hs ENNReal.toReal_nonneg),
    ENNReal.ofReal_rpow_of_nonneg (add_nonneg (mul_nonneg hr0 ENNReal.toReal_nonneg)
      (mul_nonneg hs ENNReal.toReal_nonneg)) (by norm_num), ← Real.sqrt_eq_rpow,
    ← ENNReal.ofReal_add (mul_nonneg hr0 (Real.sqrt_nonneg _))
      (mul_nonneg hs (Real.sqrt_nonneg _))]
  refine ENNReal.ofReal_le_ofReal ?_
  simpa only [smul_eq_mul] using Real.strictConcaveOn_sqrt.concaveOn.2
    (Set.mem_Ici.2 (ENNReal.toReal_nonneg : 0 ≤ x.toReal))
    (Set.mem_Ici.2 (ENNReal.toReal_nonneg : 0 ≤ y.toReal)) hr0 hs (by ring)

/-- The quantile core objective dominates the smaller of the two cuts at the
quantile threshold: `V ≤ Q` for every probability law. -/
theorem globalCutValue_le_closedQuantileValue (μ : Measure Gap) [IsProbabilityMeasure μ]
    {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (B : ℝ) :
    globalCutValue μ ρ B ≤ EntropyTailQuantile.closedQuantileValue μ ρ B := by
  obtain ⟨hr0, hr1, -⟩ := EntropyTailQuantile.quantileBoundaryFraction_properties μ hρ hρ1
  have hs : 0 ≤ 1 - EntropyTailQuantile.quantileBoundaryFraction μ ρ := sub_nonneg.2 hr1
  generalize ht : EntropyTailQuantile.quantileThreshold μ ρ = t
  generalize hr : EntropyTailQuantile.quantileBoundaryFraction μ ρ = r at hr0 hr1 hs
  generalize hc : EntropyTailQuantile.quantileCore μ ρ = c
  have hcore : c = EntropyTailQuantile.upperCut t r μ := by
    rw [← hc, ← ht, ← hr]
    exact EntropyTailQuantile.quantileCore_eq_upperCut μ hρ hρ1
  have hcμ : c ≤ μ := hc ▸ Measure.sub_le
  have : IsFiniteMeasure c := isFiniteMeasure_of_le μ hcμ
  have : IsFiniteMeasure (μ - c) := isFiniteMeasure_of_le μ Measure.sub_le
  set h : ℝ := 1 / Real.sqrt B with h_def
  set σ₀ := μ.restrict {d : Gap | t < (d : ℝ)} with hσ₀
  set σ₁ := μ.restrict {d : Gap | t ≤ (d : ℝ)} with hσ₁
  set a := ENNReal.ofReal r with ha
  set b := ENNReal.ofReal (1 - r) with hb
  have hab : a + b = 1 := by
    rw [ha, hb, ← ENNReal.ofReal_add hr0 hs]
    simp
  -- the closed cut adds the boundary atom to the open cut
  have h₁ : σ₁ = σ₀ + μ.restrict {d : Gap | (d : ℝ) = t} := by
    rw [hσ₁, hσ₀, ← Measure.restrict_union _
      (measurableSet_eq_fun measurable_subtype_coe measurable_const)]
    · congr 1
      ext d
      simp only [mem_ofPred_eq, mem_union]
      rw [le_iff_lt_or_eq, eq_comm]
    · rw [Set.disjoint_left]
      intro d h₁ h₂
      exact (ne_of_gt h₁) h₂
  -- the quantile core is a two-point mixture of cuts
  have hmix : c = a • σ₀ + b • σ₁ := by
    rw [hcore, h₁, smul_add, ← add_assoc, ← add_smul, hab, one_smul]
    rfl
  -- entropy of the mixture
  have hΓ : a * gamma σ₀ + b * gamma σ₁ ≤ gamma c := by
    have : ∀ k : Fin 2, IsFiniteMeasure (![σ₀, σ₁] k) := fun k => by
      fin_cases k <;> simp only [Fin.zero_eta, Fin.mk_one, Matrix.cons_val_zero,
        Matrix.cons_val_one] <;> infer_instance
    have hw : ∀ k : Fin 2, 0 ≤ (![r, 1 - r] : Fin 2 → ℝ) k := fun k => by
      fin_cases k
      · exact hr0
      · exact hs
    have := sum_smul_gamma_le Finset.univ ![r, 1 - r] hw ![σ₀, σ₁]
    simpa only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, ← hmix,
      ← ha, ← hb] using this
  -- the remainder cost is affine
  have hT : tailCost (μ - c) h = a * tailCost (μ - σ₀) h + b * tailCost (μ - σ₁) h := by
    have hcT : tailCost c h = a * tailCost σ₀ h + b * tailCost σ₁ h := by
      rw [hmix]
      unfold tailCost
      rw [lintegral_add_measure, lintegral_smul_measure, lintegral_smul_measure]
      rfl
    have e₀ := tailCost_sub_add (Measure.restrict_le_self : σ₀ ≤ μ) h
    have e₁ := tailCost_sub_add (Measure.restrict_le_self : σ₁ ≤ μ) h
    have ec := tailCost_sub_add hcμ h
    have hfin : tailCost c h ≠ ⊤ :=
      ne_top_of_le_ne_top (measure_ne_top c univ) (tailCost_le_mass c h)
    apply (ENNReal.add_left_inj hfin).1
    rw [ec, hcT]
    calc tailCost μ h = (a + b) * tailCost μ h := by rw [hab, one_mul]
      _ = a * (tailCost (μ - σ₀) h + tailCost σ₀ h) +
          b * (tailCost (μ - σ₁) h + tailCost σ₁ h) := by rw [e₀, e₁]; ring
      _ = _ := by ring
  -- `Q` is the capped objective of the quantile core
  have hΓc : EntropyTailQuantile.measureCostEntropy c = gamma c :=
    le_antisymm (quantile_measureCostEntropy_le c) (gamma_le_quantile_measureCostEntropy c)
  have hQ : EntropyTailQuantile.closedQuantileValue μ ρ B =
      min (ENNReal.ofReal ρ) (selectionObjective μ ρ B c) := by
    unfold EntropyTailQuantile.closedQuantileValue selectionObjective
    rw [← EntropyTailQuantile.sub_quantileCore μ hρ hρ1, hc,
      quantile_tailModulus_eq (μ - c) (by unfold EntropyTailQuantile.budgetScale; positivity),
      hΓc, add_comm]
    unfold EntropyTailQuantile.budgetScale
    rw [show (Real.sqrt B)⁻¹ = 1 / Real.sqrt B from (one_div _).symm]
  rw [hQ]
  refine min_le_min_left _ ((iInf_le _ t).trans ?_)
  set m := min (selectionObjective μ ρ B σ₀) (selectionObjective μ ρ B σ₁)
  calc m = a * m + b * m := by rw [← add_mul, hab, one_mul]
    _ ≤ a * selectionObjective μ ρ B σ₀ + b * selectionObjective μ ρ B σ₁ := by
        gcongr
        · exact min_le_left _ _
        · exact min_le_right _ _
    _ = ENNReal.ofReal h * (a * (ENNReal.ofReal ρ * gamma σ₀) ^ (1/2 : ℝ) +
          b * (ENNReal.ofReal ρ * gamma σ₁) ^ (1/2 : ℝ)) +
        (a * tailCost (μ - σ₀) h + b * tailCost (μ - σ₁) h) := by
        unfold selectionObjective
        rw [← h_def]
        ring
    _ ≤ ENNReal.ofReal h * (a * (ENNReal.ofReal ρ * gamma σ₀) +
          b * (ENNReal.ofReal ρ * gamma σ₁)) ^ (1/2 : ℝ) + tailCost (μ - c) h := by
        rw [hT]
        gcongr
        exact rpow_half_mix hr0 hr1 _ _
    _ ≤ ENNReal.ofReal h * (ENNReal.ofReal ρ * gamma c) ^ (1/2 : ℝ) + tailCost (μ - c) h := by
        gcongr
        calc a * (ENNReal.ofReal ρ * gamma σ₀) + b * (ENNReal.ofReal ρ * gamma σ₁) =
            ENNReal.ofReal ρ * (a * gamma σ₀ + b * gamma σ₁) := by ring
          _ ≤ ENNReal.ofReal ρ * gamma c := by gcongr
    _ = selectionObjective μ ρ B c := by
        unfold selectionObjective
        rw [← h_def]

/-- Corollary 6 of the certified-selection note: `K ≤ V ≤ Q ≤ (8/5) K`. -/
theorem global_cut : GlobalCutStatement := by
  intro μ _ ρ B hρ hρ4 hB
  exact ⟨selection_le_globalCutValue μ ρ B,
    globalCutValue_le_closedQuantileValue μ hρ (by linarith) B,
    (QuantileSelection.locked_selection_comparison μ hρ hρ4 hB).2⟩

/-! ### Finite laws -/

/-- An upward-closed predicate on `Fin n` holds exactly on a top segment. -/
theorem upward_iff_card {n : ℕ} (P : Fin n → Prop) [DecidablePred P]
    (hP : ∀ i j, i ≤ j → P i → P j) (i : Fin n) :
    P i ↔ n ≤ i.val + (Finset.univ.filter P).card := by
  constructor
  · intro hi
    have hsub : Finset.Ici i ⊆ Finset.univ.filter P := by
      intro j hj
      rw [Finset.mem_Ici] at hj
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ j, hP i j hj hi⟩
    have := Finset.card_le_card hsub
    rw [Fin.card_Ici] at this
    omega
  · intro hi
    by_contra hni
    have hsub : Finset.univ.filter P ⊆ Finset.Ioi i := by
      intro j hj
      rw [Finset.mem_filter] at hj
      rw [Finset.mem_Ioi]
      by_contra hji
      exact hni (hP j i (not_lt.1 hji) hj.2)
    have := Finset.card_le_card hsub
    rw [Fin.card_Ioi] at this
    have := i.isLt
    omega

/-- Restricting a finite atomic measure keeps the atoms inside the set. -/
theorem restrict_atoms {n : ℕ} (d : Fin n → Gap) (w : Fin n → ℝ≥0∞) (S : Set Gap)
    [DecidablePred (· ∈ S)] :
    (∑ i, w i • Measure.dirac (d i)).restrict S =
      ∑ i, (if d i ∈ S then w i else 0) • Measure.dirac (d i) := by
  rw [← Measure.sum_fintype, Measure.restrict_sum_of_countable, Measure.sum_fintype]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases hi : d i ∈ S <;> simp [Measure.restrict_smul, restrict_dirac, hi]

/-- On `n` atoms in increasing gap order, the open and closed threshold cuts are
exactly the `n+1` top-`k` selections scanned by the toolkit. -/
theorem finite_cut : FiniteCutStatement := by
  intro n d w hd ρ B
  have hdle : ∀ i j : Fin n, ((d i : ℝ) ≤ (d j : ℝ) ↔ i ≤ j) := fun i j => by
    rw [Subtype.coe_le_coe, hd.le_iff_le]
  -- every upward-closed cut of the gaps is a top-`k` selection
  have hup : ∀ (P : Gap → Prop) [DecidablePred P],
      (∀ x y : Gap, (x : ℝ) ≤ y → P x → P y) →
      ∃ k : Fin (n+1), (∑ i, w i • Measure.dirac (d i)).restrict {x | P x} =
        ∑ i : Fin n, (if n ≤ i.val + k.val then w i else 0) • Measure.dirac (d i) := by
    intro P _ hP
    have hQ : ∀ i j : Fin n, i ≤ j → P (d i) → P (d j) :=
      fun i j hij => hP _ _ ((hdle i j).2 hij)
    refine ⟨⟨(Finset.univ.filter fun i => P (d i)).card, ?_⟩, ?_⟩
    · have := Finset.card_filter_le (Finset.univ : Finset (Fin n)) fun i => P (d i)
      rw [Finset.card_univ, Fintype.card_fin] at this
      omega
    · rw [restrict_atoms]
      refine Finset.sum_congr rfl fun i _ => ?_
      have hi := upward_iff_card (fun i => P (d i)) hQ i
      by_cases hp : P (d i)
      · have := hi.1 hp
        simp [hp, this]
      · have : ¬ n ≤ i.val + (Finset.univ.filter fun i => P (d i)).card := fun h => hp (hi.2 h)
        simp [hp, this]
  unfold globalCutValue
  congr 1
  apply le_antisymm
  · refine le_iInf fun k => ?_
    by_cases hk : k.val = 0
    · refine (iInf_le _ (1 : ℝ)).trans ((min_le_left _ _).trans (le_of_eq ?_))
      congr 1
      rw [restrict_atoms]
      refine Finset.sum_congr rfl fun i _ => ?_
      have h1 : ¬ (1 : ℝ) < (d i : ℝ) := not_lt.2 ((d i).2.2.trans (by norm_num))
      have h2 : ¬ n ≤ i.val + k.val := by have := i.isLt; omega
      simp [h1, h2]
    · let i₀ : Fin n := ⟨n - k.val, by have := k.isLt; omega⟩
      refine (iInf_le _ (d i₀ : ℝ)).trans ((min_le_right _ _).trans (le_of_eq ?_))
      congr 1
      rw [restrict_atoms]
      refine Finset.sum_congr rfl fun i _ => ?_
      have hiff : (d i₀ : ℝ) ≤ (d i : ℝ) ↔ n ≤ i.val + k.val := by
        rw [hdle, Fin.le_iff_val_le_val]
        have := k.isLt
        simp only [i₀]
        omega
      simp only [mem_ofPred_eq]
      by_cases hp : n ≤ i.val + k.val
      · rw [ite_eq_left (hiff.2 hp), ite_eq_left hp]
      · rw [ite_eq_right (fun h => hp (hiff.1 h)), ite_eq_right hp]
  · refine le_iInf fun t => le_min ?_ ?_
    · obtain ⟨k, hk⟩ := hup (fun x => t < (x : ℝ)) (fun x y hxy h => h.trans_le hxy)
      rw [hk]
      exact iInf_le _ k
    · obtain ⟨k, hk⟩ := hup (fun x => t ≤ (x : ℝ)) (fun x y hxy h => h.trans hxy)
      rw [hk]
      exact iInf_le _ k

end ThresholdHC.GlobalCut
