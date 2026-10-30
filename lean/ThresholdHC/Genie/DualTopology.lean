import ThresholdHC.Genie.InformationTopology

/-! A finite continuous numerator divided by a positive lower-semicontinuous
extended denominator is upper semicontinuous, including infinite information. -/

noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace ThresholdHC.Genie
open ThresholdHC.Tier6 (Gap signMean)
open ThresholdHC.StoppingProgram

theorem upperSemicontinuous_information_quotient {X : Type*} [TopologicalSpace X]
    (a K : X → ℝ≥0∞) (ha : Continuous a) (haf : ∀ x, a x ≠ ⊤)
    (hK : LowerSemicontinuous K) (B : ℝ) :
    UpperSemicontinuous (fun x => a x/(4+ENNReal.ofReal B*K x)) := by
  have hden : LowerSemicontinuous (fun x => (4:ℝ≥0∞)+ENNReal.ofReal B*K x) := by
    have hm := (ENNReal.continuous_const_mul (a := ENNReal.ofReal B) ENNReal.ofReal_ne_top).comp_lowerSemicontinuous
      hK (fun _ _ h => mul_le_mul_right h _)
    exact lowerSemicontinuous_const.add hm
  have hden0 (x : X) : (4:ℝ≥0∞)+ENNReal.ofReal B*K x ≠ 0 := by simp
  have hfin (x : X) : a x/(4+ENNReal.ofReal B*K x) ≠ ⊤ :=
    ENNReal.div_ne_top (haf x) (hden0 x)
  rw [upperSemicontinuous_iff_isClosed_preimage]
  intro z
  by_cases hz : z = ⊤
  · have he : (fun x => a x/(4+ENNReal.ofReal B*K x)) ⁻¹' Ici z = ∅ := by
      ext x
      simp [hz,hfin x]
    rw [he]
    exact isClosed_empty
  · have hmult : LowerSemicontinuous (fun x => z*(4+ENNReal.ofReal B*K x)) :=
      (ENNReal.continuous_const_mul hz).comp_lowerSemicontinuous hden
        (fun _ _ h => mul_le_mul_right h z)
    have he : (fun x => a x/(4+ENNReal.ofReal B*K x)) ⁻¹' Ici z =
        {x | z*(4+ENNReal.ofReal B*K x) ≤ a x} := by
      ext x
      exact ENNReal.le_div_iff_mul_le (Or.inl (hden0 x)) (Or.inr (haf x))
    rw [he]
    exact hmult.isClosed_epigraph.preimage (continuous_id.prodMk ha)

theorem dualRatio_upperSemicontinuous {X : Type*} [TopologicalSpace X]
    (μ : Measure Gap) [IsProbabilityMeasure μ] (B : ℝ) (N : ℕ) (Q : X → FourPriors)
    (hmeanL : Continuous (fun x => signMean μ (Q x).low.val))
    (hmeanH : Continuous (fun x => signMean μ (Q x).high.val))
    (hl : ∀ s : CountState N, Continuous (fun x => countCoefficient μ (Q x).low s))
    (hh : ∀ s : CountState N, Continuous (fun x => countCoefficient μ (Q x).high s))
    (hv : ∀ s : CountState N, Continuous (fun x => countCoefficient μ (Q x).variance s))
    (hw : ∀ s : CountState N, Continuous (fun x => countCoefficient μ (Q x).work s)) :
    UpperSemicontinuous (fun x => dualRatio μ B N (Q x)) := by
  have hnum : Continuous (fun x => ENNReal.ofReal (signMean μ (Q x).high.val-signMean μ (Q x).low.val)^2) := by
    have he : (fun x => ENNReal.ofReal (signMean μ (Q x).high.val-signMean μ (Q x).low.val)^2) =
        fun x => ENNReal.ofReal ((max 0 (signMean μ (Q x).high.val-signMean μ (Q x).low.val))^2) := by
      funext x
      rw [ENNReal.ofReal_pow (le_max_left _ _),ENNReal.ofReal_max,ENNReal.ofReal_zero]
      simp
    rw [he]
    exact ENNReal.continuous_ofReal.comp ((continuous_const.max (hmeanH.sub hmeanL)).pow 2)
  exact upperSemicontinuous_information_quotient _ _ hnum
    (fun _ => ENNReal.pow_ne_top ENNReal.ofReal_ne_top)
    (informationRatio_lowerSemicontinuous μ N Q hl hh hv hw) B

end ThresholdHC.Genie
