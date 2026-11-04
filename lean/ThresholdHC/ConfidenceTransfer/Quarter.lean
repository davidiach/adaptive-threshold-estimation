import ThresholdHC.ConfidenceTransfer.Specification

noncomputable section
open MeasureTheory InformationTheory
open scoped ENNReal NNReal
namespace ThresholdHC.ConfidenceTransfer

/-- A pointwise bound on the KL integrand after smoothing. -/
theorem quarter_kl_density {p q a b : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q)
    (hs : p+q = 1) (ha : a = (3*p+q)/4) (hb : b = (p+3*q)/4) :
    b * klFun (a/b) + (8/3) * Real.sqrt (p*q) ≤ 4/3 := by
  have ha' : 0 < a := by linarith
  have hb' : 0 < b := by linarith
  have hlog := Real.log_le_sub_one_of_pos (div_pos ha' hb')
  have hχ : b * klFun (a/b) ≤ (a-b)^2/b := by
    unfold klFun
    apply (le_div_iff₀ hb').2
    have hl := mul_le_mul_of_nonneg_left hlog ha'.le
    field_simp [ne_of_gt hb'] at hl ⊢
    nlinarith
  let x := Real.sqrt p
  let y := Real.sqrt q
  have hx : x^2=p := Real.sq_sqrt hp
  have hy : y^2=q := Real.sq_sqrt hq
  rw [Real.sqrt_mul hp]
  change b * klFun (a/b) + 8/3*(x*y) ≤ 4/3
  have hsq : (a-b)^2/b ≤ (4/3)*(x-y)^2 := by
    apply (div_le_iff₀ hb').2
    rw [ha,hb,←hx,←hy]
    nlinarith only [sq_nonneg ((x-y)*(x-3*y))]
  nlinarith only [hχ,hsq,hx,hy,hs]

variable {Ω : Type} [MeasurableSpace Ω]

instance (P Q : Measure Ω) [IsFiniteMeasure P] [IsFiniteMeasure Q] :
    IsFiniteMeasure (quarterMix P Q) := by unfold quarterMix; infer_instance

private theorem mix_density (P Q M : Measure Ω) [IsFiniteMeasure P] [IsFiniteMeasure Q]
    [IsFiniteMeasure M] :
    ∀ᵐ x ∂M, ((quarterMix P Q).rnDeriv M x).toReal =
      (3*(P.rnDeriv M x).toReal + (Q.rnDeriv M x).toReal)/4 := by
  unfold quarterMix
  filter_upwards [Measure.rnDeriv_add' ((3/4 : ℝ≥0) • P) ((1/4 : ℝ≥0) • Q) M,
    Measure.rnDeriv_smul_left P M (3/4), Measure.rnDeriv_smul_left Q M (1/4),
    Measure.rnDeriv_ne_top P M, Measure.rnDeriv_ne_top Q M] with x ha hp hq hp' hq'
  simp only [Pi.add_apply,Pi.smul_apply] at ha hp hq
  rw [ha,hp,hq]
  simp only [ENNReal.smul_def,smul_eq_mul]
  rw [ENNReal.toReal_add (ENNReal.mul_ne_top (by finiteness) hp')
    (ENNReal.mul_ne_top (by finiteness) hq')]
  simp only [ENNReal.toReal_mul,ENNReal.coe_toReal,NNReal.coe_div,NNReal.coe_ofNat,NNReal.coe_one]
  ring

/-- Lemma 1 of the confidence-transfer note. The initial pair may be singular. -/
theorem quarter_smoothing (P Q : Measure Ω) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] :
    klDiv (quarterMix P Q) (quarterMix Q P) ≤
      ENNReal.ofReal ((8/3) * (1 - (CriticalEntropy.hellingerAffinity P Q).toReal)) := by
  let M := P + Q
  let A := quarterMix P Q
  let C := quarterMix Q P
  have hPQ : P ≪ M := Measure.AbsolutelyContinuous.rfl.add_right Q
  have hQM : Q ≪ M := Measure.AbsolutelyContinuous.rfl.add_right' P
  have hCM : C ≪ M := (hQM.smul_left (3/4 : ℝ≥0)).add_left (hPQ.smul_left (1/4 : ℝ≥0))
  have hAC : A ≪ C := by
    intro s hs
    change (quarterMix Q P) s = 0 at hs
    change (quarterMix P Q) s = 0
    norm_num [quarterMix, Measure.add_apply, Measure.smul_apply, ENNReal.smul_def,
      smul_eq_mul] at hs ⊢
    exact ⟨hs.2, hs.1⟩
  let f := fun x => C.rnDeriv M x * ENNReal.ofReal (klFun (A.rnDeriv C x).toReal)
  let g := fun x => (P.rnDeriv M x * Q.rnDeriv M x)^(1/2 : ℝ)
  have hf : Measurable f := by dsimp [f]; fun_prop
  have hg : Measurable g := by dsimp [g]; fun_prop
  have hkl : klDiv A C = ∫⁻ x, f x ∂M := by
    rw [klDiv_eq_lintegral_klFun_of_ac hAC]
    let ψ := fun x => ENNReal.ofReal (klFun (A.rnDeriv C x).toReal)
    calc
      _ = ∫⁻ x, ψ x ∂M.withDensity (C.rnDeriv M) := by
        rw [Measure.withDensity_rnDeriv_eq C M hCM]
      _ = _ := lintegral_withDensity_eq_lintegral_mul M (Measure.measurable_rnDeriv C M)
        (show Measurable ψ by dsimp [ψ]; fun_prop)
  have hpt : ∀ᵐ x ∂M, f x + (8/3 : ℝ≥0∞) * g x ≤ 4/3 := by
    filter_upwards [Measure.rnDeriv_add' P Q M, Measure.rnDeriv_self M,
      mix_density P Q M, mix_density Q P M, Measure.rnDeriv_mul_rnDeriv (κ := M) hAC,
      Measure.rnDeriv_ne_top P M, Measure.rnDeriv_ne_top Q M, Measure.rnDeriv_ne_top C M]
      with x hs h1 ha hc hr hp hq hc'
    have hs' : (P.rnDeriv M x).toReal + (Q.rnDeriv M x).toReal = 1 := by
      rw [← ENNReal.toReal_add hp hq]
      change M.rnDeriv M x = P.rnDeriv M x + Q.rnDeriv M x at hs
      rw [← hs, h1, ENNReal.toReal_one]
    have hpos : 0 < (C.rnDeriv M x).toReal := by
      dsimp [C]
      nlinarith [ENNReal.toReal_nonneg (a := Q.rnDeriv M x), ENNReal.toReal_nonneg (a := P.rnDeriv M x)]
    have he : (A.rnDeriv C x).toReal = (A.rnDeriv M x).toReal / (C.rnDeriv M x).toReal := by
      apply (eq_div_iff (ne_of_gt hpos)).2
      simpa only [Pi.mul_apply, ENNReal.toReal_mul] using congrArg ENNReal.toReal hr
    have hh := quarter_kl_density ENNReal.toReal_nonneg ENNReal.toReal_nonneg hs' ha
      (by dsimp [C]; linarith [hc] : (C.rnDeriv M x).toReal = _)
    have hg' : g x ≠ ∞ := ENNReal.rpow_ne_top_of_nonneg (by norm_num) (ENNReal.mul_ne_top hp hq)
    have hf' : f x ≠ ∞ := ENNReal.mul_ne_top hc' ENNReal.ofReal_ne_top
    apply (ENNReal.toReal_le_toReal
      (ENNReal.add_ne_top.mpr ⟨hf',ENNReal.mul_ne_top (by finiteness) hg'⟩) (by finiteness)).mp
    rw [ENNReal.toReal_add hf' (ENNReal.mul_ne_top (by finiteness) hg')]
    simp only [f,g,ENNReal.toReal_mul,← ENNReal.toReal_rpow,← Real.sqrt_eq_rpow]
    rw [ENNReal.toReal_ofReal (klFun_nonneg ENNReal.toReal_nonneg), he]
    norm_num [Real.sqrt_mul ENNReal.toReal_nonneg] at hh ⊢
    exact hh
  have hi := lintegral_mono_ae hpt
  rw [lintegral_add_left hf,lintegral_const_mul _ hg,lintegral_const] at hi
  change (∫⁻ x, f x ∂M) + (8/3 : ℝ≥0∞) * CriticalEntropy.hellingerAffinity P Q ≤ _ at hi
  rw [← hkl] at hi
  have h : klDiv A C + (8/3 : ℝ≥0∞)*CriticalEntropy.hellingerAffinity P Q ≤ 8/3 := by
    convert hi using 1
    norm_num [M, Measure.add_apply, div_eq_mul_inv]
    ring
  have hfinite := lt_of_le_of_lt h (by finiteness : (8/3 : ℝ≥0∞) < ∞)
  obtain ⟨hk,hgfin⟩ := ENNReal.add_ne_top.mp hfinite.ne
  have hh := (ENNReal.toReal_le_toReal hfinite.ne (by finiteness)).mpr h
  rw [ENNReal.toReal_add hk hgfin,ENNReal.toReal_mul] at hh
  norm_num at hh
  rw [← ENNReal.ofReal_toReal hk]
  apply ENNReal.ofReal_le_ofReal
  linarith

/-- The same squared Hellinger distance bounds KL in both directions. -/
theorem quarter_smoothing_both : QuarterSmoothingStatement := by
  intro Ω _ P Q _ _
  have hsym : CriticalEntropy.hellingerAffinity Q P = CriticalEntropy.hellingerAffinity P Q := by
    unfold CriticalEntropy.hellingerAffinity
    rw [add_comm Q P]
    simp_rw [mul_comm (Q.rnDeriv (P+Q) _) (P.rnDeriv (P+Q) _)]
  exact max_le (quarter_smoothing P Q) (hsym ▸ quarter_smoothing Q P)

end ThresholdHC.ConfidenceTransfer
