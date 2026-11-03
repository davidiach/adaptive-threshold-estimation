import ThresholdHC.EntropyTailLower.GateMomentFloor
import ThresholdHC.EntropyTailLower.PopulationAnnular

/-! Gated annular entropy and saturation for arbitrary laws on small gaps.
The saturation theorem eliminates the auxiliary small-work and large-band
mass assumptions by keeping the minimum of the entropy and mass terms. -/

noncomputable section
open MeasureTheory ProbabilityTheory Set Real
open scoped ENNReal
namespace ThresholdHC.EntropyTailLower
open ThresholdHC.Tier2 ThresholdHC.CriticalEntropy ThresholdHC.BlindUpper

theorem gate_restart_count_bounds (r : ℝ) (hr : (1:ℝ)/2 ≤ r) :
    0 < ⌈512*(1+r)⌉₊ ∧ 160*(1/64+2*r) ≤ (⌈512*(1+r)⌉₊:ℝ) ∧
      (⌈512*(1+r)⌉₊:ℝ) ≤ 2048*r := by
  have hl : 512*(1+r) ≤ (⌈512*(1+r)⌉₊:ℝ) := Nat.le_ceil _
  have hh : (⌈512*(1+r)⌉₊:ℝ) < 512*(1+r)+1 := Nat.ceil_lt_add_one (by linarith)
  have hp : (0:ℝ) < (⌈512*(1+r)⌉₊:ℝ) := by linarith
  exact ⟨by exact_mod_cast hp,by linarith,by linarith⟩

theorem population_annular_of_good_gaps {R : Type} [MeasurableSpace R]
    (μ : Measure EntropyGap) [IsProbabilityMeasure μ]
    (ν : Measure R) [IsProbabilityMeasure ν] (A : StoppedProcedure R ℝ)
    (ρ : unitInterval) (hρ : 0 < (ρ:ℝ)) (m : ℝ) (hm : (ρ:ℝ)/2 ≤ m)
    (hnull : populationExpectedWork μ ν (fun d => signParameter d false)
      (fun d => signParameter d true) (fun _ => 0) A ≠ ∞)
    {K : ℕ} (I : Fin K → Set EntropyGap) (b : Fin K → ℝ)
    (hb : ∀ i, 0 < b i) (hI : ∀ i, MeasurableSet (I i))
    (hdisjoint : Pairwise (fun i j => Disjoint (I i) (I j)))
    (hband : ∀ i d, d ∈ I i → b i/2 < (d:ℝ) ∧ (d:ℝ) ≤ b i)
    (hsep : ∀ i j, j.val = i.val+1 → 4*b j ≤ b i)
    (hmass : ∀ i, 144*m ≤ μ.real (I i))
    (G : Set EntropyGap) (hG : MeasurableSet G) (hGbad : μ.real Gᶜ ≤ 72*m)
    (hGgood : ∀ d ∈ G, PopulationGoodGap ν (fun d => signParameter d false)
      (fun d => signParameter d true) A (ρ:ℝ) m d) :
    (ρ:ℝ)*ThresholdHC.EntropyTailQuantile.costEntropy (fun i => μ.real (I i)/(b i)^2) ≤
      33554432*m*(populationExpectedWork μ ν (fun d => signParameter d false)
        (fun d => signParameter d true) (fun _ => 0) A).toReal := by
  let p₀ := fun d : EntropyGap => signParameter d false
  let p₁ := fun d : EntropyGap => signParameter d true
  have hp₀ : Measurable p₀ := measurable_entropy_signParameter false
  have hp₁ : Measurable p₁ := measurable_entropy_signParameter true
  have hmpos : 0 < m := by linarith
  obtain ⟨hw,hwint⟩ := population_negative_work_integral μ ν p₀ p₁ hp₀ hp₁ A hnull
  let n := ⌈512*(1+m/(ρ:ℝ))⌉₊
  have hr : (1:ℝ)/2 ≤ m/(ρ:ℝ) := (le_div_iff₀ hρ).mpr (by linarith)
  have hn := gate_restart_count_bounds (m/(ρ:ℝ)) hr
  have hfinite : ∀ d ∈ G, ∀ s, expectedStoppedProcedureWork ν (signParameter d s) A ≠ ∞ := by
    intro d hd s
    obtain ⟨_,_,hw₀,hw₁,_,_,_,_⟩ := hGgood d hd
    cases s
    · exact hw₀
    · exact hw₁
  have hmem : ∀ d ∈ G, ∀ s, MemLp id 2
      ((ν.prod (Tier2.tapeMeasure (signParameter d s))).map A.output) := by
    intro d hd s
    obtain ⟨hM₀,hM₁,_,_,_,_,_,_⟩ := hGgood d hd
    apply (conditionalSecondMoment_finite_iff ν _ A).mp
    cases s
    · exact hM₀
    · exact hM₁
  have hmoment : ∀ d ∈ G, ∀ s, (∫ x : ℝ, x^2
      ∂(ν.prod (Tier2.tapeMeasure (signParameter d s))).map A.output) ≤ 1/64+2*m/(ρ:ℝ) := by
    intro d hd s
    obtain ⟨hM₀,hM₁,_,_,_,_,hbound₀,hbound₁⟩ := hGgood d hd
    cases s
    · rw [conditionalSecondMoment_output_law ν _ A hM₀]
      have hratio : 0 ≤ 2*m/(ρ:ℝ) := by positivity
      linarith
    · rw [conditionalSecondMoment_output_law ν _ A hM₁]
      exact hbound₁
  have hminus : ∀ d ∈ G, (∫ x : ℝ, x
      ∂(ν.prod (Tier2.tapeMeasure (signParameter d false))).map A.output) ≤ 3/8-1/4 := by
    intro d hd
    rw [conditionalMean_output_law]
    have h := (abs_le.mp (hGgood d hd).2.2.2.2.1).2
    convert h using 1; norm_num
  have hplus : ∀ d ∈ G, 3/8+1/4 ≤ (∫ x : ℝ, x
      ∂(ν.prod (Tier2.tapeMeasure (signParameter d true))).map A.output) := by
    intro d hd
    rw [conditionalMean_output_law]
    have h := (hGgood d hd).2.2.2.2.2.1
    convert h using 1; norm_num
  have hnM : 10*(1/64+2*m/(ρ:ℝ)) ≤ (n:ℝ)*(1/4)^2 := by
    have h : 160*(1/64+2*m/(ρ:ℝ)) ≤ (n:ℝ) := by
      convert hn.2.1 using 1; ring
    linarith only [h]
  have hs := annular_estimation_entropy ν A μ I b hb hI hdisjoint
    (fun i => by linarith [hmass i]) hband hsep G hG
    (fun i => by linarith [hmass i]) n hn.1 (1/64+2*m/(ρ:ℝ)) (3/8) (1/4)
    (by norm_num) hnM hw hfinite hmem hmoment hminus hplus
  rw [hwint] at hs
  have hnr : (n:ℝ)*(ρ:ℝ) ≤ 2048*m := by
    apply (le_div_iff₀ hρ).mp
    convert hn.2.2 using 1
    ring
  calc
    _ ≤ (ρ:ℝ)*(16384*(n:ℝ)*(populationExpectedWork μ ν p₀ p₁ (fun _ => 0) A).toReal) :=
      mul_le_mul_of_nonneg_left hs hρ.le
    _ = 16384*(populationExpectedWork μ ν p₀ p₁ (fun _ => 0) A).toReal*((n:ℝ)*(ρ:ℝ)) := by ring
    _ ≤ 16384*(populationExpectedWork μ ν p₀ p₁ (fun _ => 0) A).toReal*(2048*m) :=
      mul_le_mul_of_nonneg_left hnr (by positivity)
    _ = _ := by ring

theorem population_gated_annular_entropy {R : Type} [MeasurableSpace R]
    (μ : Measure EntropyGap) [IsProbabilityMeasure μ]
    (ν : Measure R) [IsProbabilityMeasure ν] (A : StoppedProcedure R ℝ)
    (ρ : unitInterval) (hρ : 0 < (ρ:ℝ)) (hρ4 : (ρ:ℝ) ≤ 1/4)
    (m : ℝ) (hm : 0 ≤ m)
    (hguar : CappedPopulationGuarantee μ ν (fun d => signParameter d false)
      (fun d => signParameter d true) A (ρ:ℝ) m)
    (a : ℝ) (ha : 0 < a) (ha4 : a ≤ 1/4) (hclose : ∀ᵐ (d : EntropyGap) ∂μ, (d:ℝ) ≤ a)
    (hsmall : 64*exp 48*a^2*m*(populationExpectedWork μ ν (fun d => signParameter d false)
      (fun d => signParameter d true) (fun _ => 0) A).toReal ≤ 1/64)
    {K : ℕ} (I : Fin K → Set EntropyGap) (b : Fin K → ℝ)
    (hb : ∀ i, 0 < b i) (hI : ∀ i, MeasurableSet (I i))
    (hdisjoint : Pairwise (fun i j => Disjoint (I i) (I j)))
    (hband : ∀ i d, d ∈ I i → b i/2 < (d:ℝ) ∧ (d:ℝ) ≤ b i)
    (hsep : ∀ i j, j.val = i.val+1 → 4*b j ≤ b i)
    (hmass : ∀ i, 288*exp 12*(1+exp 12)*a^2*m*
      (populationExpectedWork μ ν (fun d => signParameter d false)
        (fun d => signParameter d true) (fun _ => 0) A).toReal ≤ μ.real (I i)) :
    (ρ:ℝ)*ThresholdHC.EntropyTailQuantile.costEntropy (fun i => μ.real (I i)/(b i)^2) ≤
      67108864*(1+exp 12)*m*(populationExpectedWork μ ν (fun d => signParameter d false)
        (fun d => signParameter d true) (fun _ => 0) A).toReal := by
  let p₀ := fun d : EntropyGap => signParameter d false
  let p₁ := fun d : EntropyGap => signParameter d true
  have hp₀ : Measurable p₀ := measurable_entropy_signParameter false
  have hp₁ : Measurable p₁ := measurable_entropy_signParameter true
  have hmpos : 0 < m := by
    have hf := capped_guarantee_moment_floor_general μ ν p₀ p₁ hp₀ hp₁ A ρ hρ hρ4 m hm hguar
    linarith
  have hcl : ∀ᵐ d ∂μ, |(p₀ d:ℝ)-1/2| ≤ a ∧ (p₀ d:ℝ)+(p₁ d:ℝ) = 1 := by
    filter_upwards [hclose] with d hd
    constructor
    · have he : (p₀ d:ℝ)-1/2 = -(d:ℝ) := by dsimp [p₀,signParameter]; ring
      rw [he,abs_neg,abs_of_pos d.property.1]
      exact hd
    · dsimp [p₀,p₁,signParameter]
      ring
  have hboth : ∀ᵐ d ∂μ, |(p₀ d:ℝ)-1/2| ≤ a ∧ |(p₁ d:ℝ)-1/2| ≤ a := by
    filter_upwards [hcl] with d hd
    refine ⟨hd.1,?_⟩
    have he : (p₁ d:ℝ)-1/2 = -((p₀ d:ℝ)-1/2) := by linarith [hd.2]
    simpa only [he,abs_neg] using hd.1
  let β := fairActivation ν A a
  let Z := gateAverage A ⌈(a^2)⁻¹⌉₊ ⌈a⁻¹⌉₊ β
  let η := Measure.pi (fun _ : Fin ((gateBatchCount β-1)+1) => ν)
  let mZ := (1+exp 12)*β*m
  obtain ⟨hβ,G,hG,hbad,hgood⟩ := population_gate_good_gaps_mass μ ν p₀ p₁ hp₀ hp₁ A ρ hρ hρ4 m hmpos hguar
    a ha ha4 hcl hsmall
  have hfloor := population_gate_moment_floor μ ν p₀ p₁ hp₀ hp₁ A ρ hρ hρ4 m hmpos hguar
    a ha ha4 hcl hsmall
  have huni := population_gateAverage_uniform μ ν p₀ p₁ hp₀ hp₁ A ρ hρ hρ4 m hguar a ha ha4 hboth hβ
  have htrade := population_gateAverage_tradeoff μ ν p₀ p₁ hp₀ hp₁ A ρ hρ hρ4 m hm hguar a ha ha4 hboth hβ
  have hc₀ := cappedPrior_const μ (ρ:ℝ) 0 (by norm_num) (by simpa using hρ.le)
  have hmassZ (i : Fin K) : 144*mZ ≤ μ.real (I i) := by
    calc
      _ ≤ 144*(2*exp 12*(1+exp 12)*a^2*m*(populationExpectedWork μ ν p₀ p₁ (fun _ => 0) A).toReal) :=
        mul_le_mul_of_nonneg_left htrade.1 (by norm_num)
      _ = 288*exp 12*(1+exp 12)*a^2*m*(populationExpectedWork μ ν p₀ p₁ (fun _ => 0) A).toReal := by ring
      _ ≤ _ := hmass i
  have hAnn := population_annular_of_good_gaps μ η Z ρ hρ mZ hfloor (huni _ hc₀).2
    I b hb hI hdisjoint hband hsep hmassZ G hG hbad hgood
  calc
    _ ≤ _ := hAnn
    _ = 33554432*(mZ*(populationExpectedWork μ η p₀ p₁ (fun _ => 0) Z).toReal) := by ring
    _ ≤ 33554432*(2*(1+exp 12)*m*(populationExpectedWork μ ν p₀ p₁ (fun _ => 0) A).toReal) :=
      mul_le_mul_of_nonneg_left htrade.2 (by norm_num)
    _ = _ := by ring

theorem population_gated_annular_saturation {R : Type} [MeasurableSpace R]
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
      1073741824*exp 48*m*(populationExpectedWork μ ν (fun d => signParameter d false)
        (fun d => signParameter d true) (fun _ => 0) A).toReal := by
  let W := (populationExpectedWork μ ν (fun d => signParameter d false)
    (fun d => signParameter d true) (fun _ => 0) A).toReal
  let T := m*W
  have hT : 0 ≤ T := mul_nonneg hm ENNReal.toReal_nonneg
  have h12 : exp 12 ≤ exp 48 := exp_le_exp.mpr (by norm_num)
  have h24 : exp 24 ≤ exp 48 := exp_le_exp.mpr (by norm_num)
  have h1 : 1 ≤ exp 48 := one_le_exp (by norm_num)
  have he : exp 12*exp 12 = exp 24 := by rw [← exp_add]; norm_num
  have hC₁ : 4096*exp 48 ≤ 1073741824*exp 48 := by nlinarith [exp_pos (48:ℝ)]
  have hC₂ : 288*exp 12*(1+exp 12) ≤ 1073741824*exp 48 := by nlinarith
  have hC₃ : 67108864*(1+exp 12) ≤ 1073741824*exp 48 := by nlinarith
  have ha2 := sq_pos_of_pos ha
  suffices min (s/a^2) ((ρ:ℝ)*ThresholdHC.EntropyTailQuantile.costEntropy
      (fun i => μ.real (I i)/(b i)^2)) ≤ (1073741824*exp 48)*T by
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
      (hd.trans (mul_le_mul_of_nonneg_right hC₁ hT)))

end ThresholdHC.EntropyTailLower
