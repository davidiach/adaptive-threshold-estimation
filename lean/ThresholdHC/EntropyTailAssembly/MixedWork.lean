import ThresholdHC.EntropyTailAssembly.AccuracySchedule
import ThresholdHC.EntropyTailAssembly.DyadicKernelSum

/-! Mixed selected/resolved-tail work across distinct selected caps. The
summable additive envelope avoids any logarithmic loss in the number of levels. -/

noncomputable section
open MeasureTheory Set Real
open scoped BigOperators

namespace ThresholdHC.EntropyTailAssembly
open ThresholdHC.Tier6

theorem mixed_scalar_bound {δ M O A H ρ p : ℝ}
    (hδ : 0 ≤ δ) (_hM : 0 ≤ M) (hA : 0 ≤ A) (hH : 0 ≤ H) (hρ : 0 ≤ ρ) (hp : 0 ≤ p)
    (hcap : δ*M ≤ 256*A) (hwork : O ≤ 34*H*sqrt M)
    (hscale : sqrt δ = sqrt ρ*p^2) :
    sqrt (δ*O) ≤ 12*(H+sqrt (ρ*A))*p := by
  have hs : sqrt (δ*M) ≤ 16*sqrt A := by
    apply sqrt_le_iff.mpr
    refine ⟨by positivity, ?_⟩
    nlinarith [sq_sqrt hA]
  have he : sqrt δ*sqrt (δ*M) = δ*sqrt M := by
    rw [sqrt_mul hδ]
    rw [← mul_assoc, ← sq, sq_sqrt hδ]
  have h1 := mul_le_mul_of_nonneg_left hs (sqrt_nonneg δ)
  rw [he] at h1
  have he2 : sqrt δ*(16*sqrt A) = 16*sqrt (ρ*A)*p^2 := by
    rw [hscale, sqrt_mul hρ]
    ring
  rw [he2] at h1
  have h2 := mul_le_mul_of_nonneg_left hwork hδ
  have h3 := mul_le_mul_of_nonneg_left h1 (show 0 ≤ 34*H by positivity)
  have hb : δ*O ≤ 544*H*sqrt (ρ*A)*p^2 := by nlinarith only [h2, h3]
  apply sqrt_le_iff.mpr
  refine ⟨by positivity, ?_⟩
  have hsq := mul_nonneg (sq_nonneg (H-sqrt (ρ*A))) (sq_nonneg p)
  have hpos : 0 ≤ H*sqrt (ρ*A)*p^2 := by positivity
  nlinarith

theorem half_geometric_tail_sum (n : ℕ) :
    ∑ l ∈ Finset.range n, (1/2:ℝ)^(l+1) ≤ 1 := by
  have h : HasSum (fun l : ℕ => (1/2:ℝ)^(l+1)) 1 := by
    have hh := (hasSum_geometric_of_lt_one (by norm_num : (0:ℝ) ≤ 1/2)
      (by norm_num : (1/2:ℝ) < 1)).mul_left (1/2:ℝ)
    convert hh using 1
    · ext l; rw [pow_succ']
    · norm_num
  exact sum_le_hasSum _ (fun _ _ => by positivity) h

theorem sqrt_levelAccuracy_half {ρ : ℝ} (hρ : 0 ≤ ρ) (l : ℕ) :
    sqrt (levelAccuracy ρ l) = sqrt ρ*((1/2:ℝ)^(l+1))^2 := by
  rw [sqrt_levelAccuracy hρ]
  congr 1
  rw [← pow_mul, Nat.mul_comm, pow_mul]
  norm_num

theorem cap_dichotomy (σ τ : Measure Gap) [IsFiniteMeasure σ] [IsFiniteMeasure τ]
    (hσ : Integrable (fun d : Gap => (d:ℝ)⁻¹^2) σ) {δ M : ℝ}
    (hM : 0 < M) (he : δ/128 < eta (σ+τ) M) :
    δ ≤ 256*eta τ M ∨ δ*M ≤ 256*(∫ d : Gap, (d:ℝ)⁻¹^2 ∂σ) := by
  rw [eta_add] at he
  by_cases h : eta σ M ≤ eta τ M
  · exact Or.inl (by linarith)
  · right
    have hδ : δ ≤ 256*eta σ M := by linarith
    have hI := eta_le_inverseSquare σ hσ hM
    have hb : δ ≤ (256*(∫ d : Gap, (d:ℝ)⁻¹^2 ∂σ))/M := by
      exact hδ.trans ((mul_le_mul_of_nonneg_left hI (by norm_num : (0:ℝ) ≤ 256)).trans_eq (by ring))
    exact (le_div_iff₀ hM).mp hb

theorem mixed_level_envelope (σ τ : Measure Gap) [IsFiniteMeasure σ] [IsFiniteMeasure τ]
    (hσ : Integrable (fun d : Gap => (d:ℝ)⁻¹^2) σ)
    (hτ : Integrable (fun d : Gap => (d:ℝ)⁻¹) τ) {ρ : ℝ}
    (hρ : 0 < ρ) (hm : ρ/128 < (σ+τ).real univ) (l : ℕ) :
    let k := errorCapExponent (σ+τ) (levelAccuracy ρ l) (levelAccuracy_pos hρ l)
    sqrt (levelAccuracy ρ l*ordinaryCost τ (4^k)) ≤
      16*sqrt (eta τ (4^k)*ordinaryCost τ (4^k)) +
      12*((∫ d : Gap, (d:ℝ)⁻¹ ∂τ)+sqrt (ρ*(∫ d : Gap, (d:ℝ)⁻¹^2 ∂σ)))*(1/2:ℝ)^(l+1) := by
  dsimp only
  let k := errorCapExponent (σ+τ) (levelAccuracy ρ l) (levelAccuracy_pos hρ l)
  have hM : (0:ℝ) < 4^k := by positivity
  have hO := ordinaryCost_nonneg τ hM.le
  have hδ := levelAccuracy_pos hρ l
  have hA : 0 ≤ ∫ d : Gap, (d:ℝ)⁻¹^2 ∂σ := integral_nonneg (fun _ => sq_nonneg _)
  have hH : 0 ≤ ∫ d : Gap, (d:ℝ)⁻¹ ∂τ := integral_nonneg (fun d => inv_nonneg.mpr d.property.1.le)
  have hmass : levelAccuracy ρ l/8 < (σ+τ).real univ := by
    have h := levelAccuracy_le_first hρ.le l
    linarith
  have he := errorCapExponent_error_lower (σ+τ) hδ hmass
  rcases cap_dichotomy σ τ hσ hM he with ht | hs
  · have hb : sqrt (levelAccuracy ρ l*ordinaryCost τ (4^k)) ≤
        16*sqrt (eta τ (4^k)*ordinaryCost τ (4^k)) := by
      calc
        _ ≤ sqrt (256*(eta τ (4^k)*ordinaryCost τ (4^k))) :=
          sqrt_le_sqrt (by nlinarith [mul_le_mul_of_nonneg_right ht hO])
        _ = _ := by rw [sqrt_mul (by norm_num : (0:ℝ) ≤ 256)]; norm_num
    exact hb.trans (le_add_of_nonneg_right (by positivity))
  · have hb := mixed_scalar_bound hδ.le hM.le hA hH hρ.le
      (by positivity : (0:ℝ) ≤ (1/2:ℝ)^(l+1)) hs
      (by simpa [mul_comm, mul_left_comm, mul_assoc] using ordinaryCost_le_inverse τ hτ hM)
      (sqrt_levelAccuracy_half hρ.le l)
    exact hb.trans (le_add_of_nonneg_left (by positivity))

theorem mixed_work_sum (σ τ : Measure Gap) [IsFiniteMeasure σ] [IsFiniteMeasure τ]
    (hσ : Integrable (fun d : Gap => (d:ℝ)⁻¹^2) σ)
    (hτ : Integrable (fun d : Gap => (d:ℝ)⁻¹) τ) {ρ : ℝ}
    (hρ : 0 < ρ) (hm : ρ/128 < (σ+τ).real univ) (J : ℕ) :
    (∑ l ∈ Finset.range (J+1), sqrt (levelAccuracy ρ l*ordinaryCost τ
      (4^(errorCapExponent (σ+τ) (levelAccuracy ρ l) (levelAccuracy_pos hρ l))))) ≤
      3340*(∫ d : Gap, (d:ℝ)⁻¹ ∂τ)+12*sqrt (ρ*(∫ d : Gap, (d:ℝ)⁻¹^2 ∂σ)) := by
  let k := fun l => errorCapExponent (σ+τ) (levelAccuracy ρ l) (levelAccuracy_pos hρ l)
  let H := ∫ d : Gap, (d:ℝ)⁻¹ ∂τ
  let C := sqrt (ρ*(∫ d : Gap, (d:ℝ)⁻¹^2 ∂σ))
  have hH : 0 ≤ H := integral_nonneg (fun d => inv_nonneg.mpr d.property.1.le)
  have hC : 0 ≤ C := sqrt_nonneg _
  have hinj : Function.Injective k := (schedule_caps_strict (σ+τ) hρ hm).injective
  have hsum : (∑ l ∈ Finset.range (J+1), sqrt (eta τ (4^(k l))*ordinaryCost τ (4^(k l)))) ≤ 208*H := by
    rw [← Finset.sum_image (f := fun m => sqrt (eta τ (4^m)*ordinaryCost τ (4^m)))
      (fun _ _ _ _ he => hinj he)]
    exact dyadic_kernel_finset_inverse τ hτ _
  have h := Finset.sum_le_sum (s := Finset.range (J+1)) (fun l _ => mixed_level_envelope σ τ hσ hτ hρ hm l)
  change (∑ l ∈ Finset.range (J+1), sqrt (levelAccuracy ρ l*ordinaryCost τ (4^(k l)))) ≤
    ∑ l ∈ Finset.range (J+1), (16*sqrt (eta τ (4^(k l))*ordinaryCost τ (4^(k l)))+
      12*(H+C)*(1/2:ℝ)^(l+1)) at h
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum] at h
  have hp := mul_le_mul_of_nonneg_left (half_geometric_tail_sum (J+1))
    (show 0 ≤ 12*(H+C) by positivity)
  change (∑ l ∈ Finset.range (J+1), sqrt (levelAccuracy ρ l*ordinaryCost τ (4^(k l)))) ≤ 3340*H+12*C
  linarith

end ThresholdHC.EntropyTailAssembly
