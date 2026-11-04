import ThresholdHC.BandwiseSuffix.Packets

noncomputable section
open MeasureTheory Set Real
open scoped ENNReal
namespace ThresholdHC.BandwiseSuffix
open ThresholdHC.Tier6 (Gap)
open ThresholdHC.EntropyTail

/-- Exchange two packets with identical band costs but different ordinary savings. -/
theorem improving_exchange {μ σ A C : Measure Gap} [IsFiniteMeasure μ]
    {ρ B : ℝ} (hσ : σ ≤ μ) (hA : A ≤ σ) (hC : C ≤ μ-σ)
    (hcost : ∀ j, bandCost A j = bandCost C j)
    (hgain : tailCost A (1 / sqrt B) < tailCost C (1 / sqrt B))
    (hfinite : selectionObjective μ ρ B σ ≠ ⊤) :
    ∃ τ : Measure Gap, τ ≤ μ ∧ selectionObjective μ ρ B τ < selectionObjective μ ρ B σ := by
  let V := σ - A
  let U := (μ - σ) - C
  have : IsFiniteMeasure σ := isFiniteMeasure_of_le μ hσ
  have : IsFiniteMeasure A := isFiniteMeasure_of_le σ hA
  have : IsFiniteMeasure C := isFiniteMeasure_of_le (μ-σ) hC
  have hV : V + A = σ := Measure.sub_add_cancel_of_le hA
  have hU : U + C = μ-σ := Measure.sub_add_cancel_of_le hC
  have htotal : (U+A) + (V+C) = μ := by
    calc
      _ = (U+C) + (V+A) := by abel
      _ = μ := by rw [hU,hV,Measure.sub_add_cancel_of_le hσ]
  have hfeas : V+C ≤ μ := calc
    V+C ≤ (U+A)+(V+C) := le_add_of_nonneg_left bot_le
    _ = μ := htotal
  have : IsFiniteMeasure (V+C) := isFiniteMeasure_of_le μ hfeas
  have hres : μ - (V+C) = U+A := by rw [← htotal, Measure.add_sub_cancel]
  have hband (ν ξ : Measure Gap) (j : ℕ) : bandCost (ν+ξ) j = bandCost ν j + bandCost ξ j := by
    simp only [bandCost, Measure.restrict_add, lintegral_add_measure]
  have heq (j : ℕ) : bandCost (V+C) j = bandCost σ j := by
    rw [← hV, hband, hband, hcost]
  have hgamma : gamma (V+C) = gamma σ := by simp only [gamma, heq]
  have htail (ν ξ : Measure Gap) (h : ℝ) : tailCost (ν+ξ) h = tailCost ν h + tailCost ξ h := by
    simp only [tailCost, lintegral_add_measure]
  have hUfin : tailCost U (1 / sqrt B) ≠ ⊤ :=
    ne_top_of_le_ne_top (measure_ne_top U _) (tailCost_le_mass _ _)
  refine ⟨V+C, hfeas, ?_⟩
  unfold selectionObjective at hfinite ⊢
  rw [hgamma,hres, ← hU,htail,htail]
  exact ENNReal.add_lt_add_left (ne_top_of_le_ne_top hfinite le_self_add)
    (ENNReal.add_lt_add_left hUfin hgain)

/-- Within one dyadic band a skipped larger atom strictly improves any finite hard objective. -/
theorem improve_inversion (μ : Measure Gap) [IsProbabilityMeasure μ] (S : Finset Gap)
    {ρ B : ℝ} (hB : 0 < B) {j : ℕ} {x y : Gap} (hxy : x < y)
    (hx : x ∈ S) (hy : y ∉ S) (hxj : x ∈ band j) (hyj : y ∈ band j)
    (hmx : 0 < μ {x}) (hmy : 0 < μ {y})
    (hfinite : selectionObjective μ ρ B (μ.restrict S) ≠ ⊤) :
    ∃ τ : Measure Gap, τ ≤ μ ∧ selectionObjective μ ρ B τ < selectionObjective μ ρ B (μ.restrict S) := by
  let e := min (μ.real {x} / (x:ℝ)^2) (μ.real {y} / (y:ℝ)^2)
  have he : 0 < e := lt_min
    (div_pos (ENNReal.toReal_pos hmx.ne' (measure_ne_top _ _)) (pow_pos x.property.1 _))
    (div_pos (ENNReal.toReal_pos hmy.ne' (measure_ne_top _ _)) (pow_pos y.property.1 _))
  have hres : μ - μ.restrict S = μ.restrict (S : Set Gap)ᶜ := by
    conv_lhs => lhs; rw [← Measure.restrict_compl_add_restrict S.measurableSet (μ := μ)]
    exact Measure.add_sub_cancel
  apply improving_exchange Measure.restrict_le_self
    (packet_le_restrict (μ := μ) (s := (S : Set Gap)) hx (min_le_left ..)) (A := packet e x)
    (C := packet e y)
  · rw [hres]
    exact packet_le_restrict hy (min_le_right ..)
  · intro k
    rw [packet_bandCost he.le, packet_bandCost he.le]
    by_cases hk : j = k
    · subst k; simp [hxj,hyj]
    · have hxk := Set.disjoint_left.mp (band_disjoint hk) hxj
      have hyk := Set.disjoint_left.mp (band_disjoint hk) hyj
      simp [hxk,hyk]
  · exact packet_strict_gain he (one_div_pos.mpr (sqrt_pos.mpr hB)) hxy
  · exact hfinite

end ThresholdHC.BandwiseSuffix
