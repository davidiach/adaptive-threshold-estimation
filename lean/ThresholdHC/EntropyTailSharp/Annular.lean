import ThresholdHC.EntropyTailLower.GatedAnnular

/-! Retain the actual maximum of the three gate estimates. The common coefficient is 4096 times exp(48). -/
noncomputable section
open MeasureTheory Set Real
open scoped BigOperators ENNReal
namespace ThresholdHC.EntropyTailSharp
open ThresholdHC.EntropyTailLower
open ProbabilityTheory ThresholdHC.Tier2 ThresholdHC.CriticalEntropy ThresholdHC.BlindUpper

theorem population_gated_annular_saturation_sharp {R : Type} [MeasurableSpace R]
    (μ : Measure EntropyGap) [IsProbabilityMeasure μ]
    (ν : Measure R) [IsProbabilityMeasure ν] (A : StoppedProcedure R ℝ)
    (ρ : unitInterval) (hρ : 0 < (ρ:ℝ)) (hρ4 : (ρ:ℝ) ≤ 1/4)
    (m : ℝ) (hm : 0 ≤ m)
    (hguar : CappedPopulationGuarantee μ ν (fun d => signParameter d false)
      (fun d => signParameter d true) A (ρ:ℝ) m)
    (a : ℝ) (ha : 0 < a) (ha4 : a ≤ 1/4) (hclose : ∀ᵐ (d : EntropyGap) ∂μ, (d:ℝ) ≤ a)
    {K : ℕ} (I : Fin K → Set EntropyGap) (b : Fin K → ℝ)
    (hb : ∀ i, 0 < b i) (hI : ∀ i, MeasurableSet (I i))
    (hdisjoint : Pairwise (fun i j => Disjoint (I i) (I j)))
    (hband : ∀ i d, d ∈ I i → b i/2 < (d:ℝ) ∧ (d:ℝ) ≤ b i)
    (hsep : ∀ i j, j.val = i.val+1 → 4*b j ≤ b i)
    (s : ℝ) (hs1 : s ≤ 1) (hmass : ∀ i, s ≤ μ.real (I i)) :
    min (s/a^2) ((ρ:ℝ)*ThresholdHC.EntropyTailQuantile.costEntropy (fun i => μ.real (I i)/(b i)^2)) ≤
      4096*exp 48*m*(populationExpectedWork μ ν (fun d => signParameter d false)
        (fun d => signParameter d true) (fun _ => 0) A).toReal := by
  let W := (populationExpectedWork μ ν (fun d => signParameter d false)
    (fun d => signParameter d true) (fun _ => 0) A).toReal
  let T := m*W
  have hT : 0 ≤ T := mul_nonneg hm ENNReal.toReal_nonneg
  have h12 : exp 12 ≤ exp 48 := exp_le_exp.mpr (by norm_num)
  have h24 : exp 24 ≤ exp 48 := exp_le_exp.mpr (by norm_num)
  have h1 : 1 ≤ exp 48 := one_le_exp (by norm_num)
  have he : exp 12*exp 12 = exp 24 := by rw [← exp_add]; norm_num
  have h36 : (32768:ℝ) ≤ exp 36 := by
    calc
      _ ≤ (2:ℝ)^36 := by norm_num
      _ ≤ exp 1 ^ 36 := pow_le_pow_left₀ (by norm_num) exp_one_gt_two.le _
      _ = exp 36 := by rw [← exp_nat_mul]; norm_num
  have he36 : exp 12 * exp 36 = exp 48 := by rw [← exp_add]; norm_num
  have hC₂ : 288*exp 12*(1+exp 12) ≤ 4096*exp 48 := by nlinarith
  have hC₃ : 67108864*(1+exp 12) ≤ 4096*exp 48 := by
    nlinarith only [mul_le_mul_of_nonneg_left h36 (exp_pos (12:ℝ)).le, he36,
      one_le_exp (by norm_num : (0:ℝ) ≤ 12)]
  have ha2 := sq_pos_of_pos ha
  suffices min (s/a^2) ((ρ:ℝ)*ThresholdHC.EntropyTailQuantile.costEntropy
      (fun i => μ.real (I i)/(b i)^2)) ≤ (4096*exp 48)*T by
    convert this using 1
    dsimp [T,W]
    ring
  by_cases hsmall : 64*exp 48*a^2*m*W ≤ 1/64
  · by_cases hmassSmall : s ≤ 288*exp 12*(1+exp 12)*a^2*m*W
    · have hd : s/a^2 ≤ (288*exp 12*(1+exp 12))*T := by
        apply (div_le_iff₀ ha2).mpr
        convert hmassSmall using 1
        dsimp [T]
        ring
      exact (min_le_left _ _).trans (hd.trans (mul_le_mul_of_nonneg_right hC₂ hT))
    · have hmass' (i : Fin K) : 288*exp 12*(1+exp 12)*a^2*m*W ≤ μ.real (I i) :=
        (not_le.mp hmassSmall).le.trans (hmass i)
      have hAnn := population_gated_annular_entropy μ ν A ρ hρ hρ4 m hm hguar a ha ha4 hclose
        hsmall I b hb hI hdisjoint hband hsep hmass'
      have hAnn' : (ρ:ℝ)*ThresholdHC.EntropyTailQuantile.costEntropy (fun i => μ.real (I i)/(b i)^2) ≤
          (67108864*(1+exp 12))*T := by
        convert hAnn using 1
        dsimp [T,W]
        ring
      exact (min_le_right _ _).trans (hAnn'.trans (mul_le_mul_of_nonneg_right hC₃ hT))
  · have hbig : 1/64 ≤ 64*exp 48*a^2*m*W := (not_le.mp hsmall).le
    have hd : 1/a^2 ≤ (4096*exp 48)*T := by
      apply (div_le_iff₀ ha2).mpr
      dsimp [T]
      nlinarith only [hbig]
    exact (min_le_left _ _).trans ((div_le_div_of_nonneg_right hs1 ha2.le).trans
      hd)

end ThresholdHC.EntropyTailSharp
