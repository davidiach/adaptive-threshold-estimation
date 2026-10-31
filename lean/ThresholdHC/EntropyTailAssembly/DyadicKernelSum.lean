import ThresholdHC.EntropyTailAssembly.DyadicKernelPointwise

/-! The paper's homogeneous kernel estimate, first for finite cap sets.
The bound integrates a bounded truncated inverse gap, so it also applies
when the original inverse moment is infinite. -/

noncomputable section
open MeasureTheory Set Real
open scoped BigOperators

namespace ThresholdHC.EntropyTailAssembly
open ThresholdHC.Tier6 ThresholdHC.EntropyTailUpper ThresholdHC.EntropyTail

theorem dyadic_power_sum (n : ℕ) : ∑ k ∈ Finset.range n, (2:ℝ)^k = 2^n-1 := by
  induction n with
  | zero => simp
  | succ n ih => rw [Finset.sum_range_succ, ih, pow_succ]; ring

theorem hasSum_dyadic_linear_tail :
    HasSum (fun r : ℕ => (1/2:ℝ)^(r+1)*(1+(r+1:ℕ))) 3 := by
  have hg := hasSum_geometric_of_lt_one (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num : (1/2:ℝ) < 1)
  have hn := hasSum_coe_mul_geometric_of_norm_lt_one (by norm_num : ‖(1/2:ℝ)‖ < 1)
  have h := ((hg.mul_left 2).add hn).mul_left (1/2:ℝ)
  convert h using 1
  · ext r
    push_cast
    rw [pow_succ]
    ring
  · norm_num

theorem hasSum_dyadic_cubic_tail : HasSum (fun r : ℕ => (1/8:ℝ)^(r+1)) (1/7) := by
  have h := (hasSum_geometric_of_lt_one (by norm_num : (0:ℝ) ≤ 1/8)
    (by norm_num : (1/8:ℝ) < 1)).mul_left (1/8:ℝ)
  convert h using 1
  · ext r
    rw [pow_succ']
  · norm_num

theorem large_envelope_sum (n : ℕ) :
    ∑ r ∈ Finset.range n,
      (8*(1/8:ℝ)^(r+1)+68*(1/2:ℝ)^(r+1)*(1+(r+1:ℕ))) ≤ 206 := by
  have h := (hasSum_dyadic_cubic_tail.mul_left 8).add (hasSum_dyadic_linear_tail.mul_left 68)
  have hb := sum_le_hasSum (Finset.range n) (fun r _ => by positivity) h
  simp only [Finset.sum_add_distrib, mul_assoc] at hb ⊢
  linarith

theorem band_scale_le_inverse (j : ℕ) (d : Gap) (hd : d ∈ band j) :
    (2:ℝ)^(j+1) ≤ (d:ℝ)⁻¹ := by
  have h := band_scaled_gap_le_one j d hd
  rw [inv_eq_one_div]
  exact (le_div_iff₀ d.property.1).mpr h

theorem scaledKernel_sum_band (K j : ℕ) (d : Gap) (hd : d ∈ band j) :
    ∑ k ∈ Finset.range (K+1), scaledKernel k (d:ℝ) ≤ 208 * min ((2:ℝ)^K) (d:ℝ)⁻¹ := by
  have hd0 : 0 ≤ (d:ℝ)⁻¹ := by positivity [d.property.1]
  have hm := band_scale_le_inverse j d hd
  by_cases hK : K ≤ j+1
  · have hpow : (2:ℝ)^K ≤ 2^(j+1) := by gcongr; norm_num
    rw [min_eq_left (hpow.trans hm)]
    have h := Finset.sum_le_sum (s := Finset.range (K+1)) (fun k _ => scaledKernel_le_cap k (d:ℝ))
    rw [dyadic_power_sum, pow_succ] at h
    nlinarith [show (0:ℝ) ≤ 2^K by positivity]
  · have hK' : j+1 ≤ K := by omega
    have hp : (2:ℝ)^(j+1) ≤ 2^K := by gcongr; norm_num
    have hs : ∑ k ∈ Finset.range (j+2), scaledKernel k (d:ℝ) ≤ 2*2^(j+1) := by
      have h := Finset.sum_le_sum (s := Finset.range (j+2)) (fun k _ => scaledKernel_le_cap k (d:ℝ))
      rw [dyadic_power_sum, show j+2 = (j+1)+1 by omega, pow_succ] at h
      linarith
    have ht : ∑ r ∈ Finset.range (K-(j+1)), scaledKernel (j+2+r) (d:ℝ) ≤ 206*2^(j+1) := by
      calc
        _ ≤ ∑ r ∈ Finset.range (K-(j+1)), (2:ℝ)^(j+1) *
            (8*(1/8:ℝ)^(r+1)+68*(1/2:ℝ)^(r+1)*(1+(r+1:ℕ))) := by
          apply Finset.sum_le_sum
          intro r _
          rw [show j+2+r = j+1+(r+1) by omega]
          exact band_large_scaledKernel j r d hd
        _ ≤ (2:ℝ)^(j+1)*206 := by
          rw [← Finset.mul_sum]
          exact mul_le_mul_of_nonneg_left (large_envelope_sum _) (by positivity)
        _ = _ := by ring
    have he : K+1 = (j+2)+(K-(j+1)) := by omega
    rw [he, Finset.sum_range_add]
    calc
      _ ≤ 2*2^(j+1)+206*2^(j+1) := add_le_add hs ht
      _ = 208*(2:ℝ)^(j+1) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (le_min hp hm) (by norm_num)

theorem scaledKernel_sum (K : ℕ) (d : Gap) :
    ∑ k ∈ Finset.range (K+1), scaledKernel k (d:ℝ) ≤ 208 * min ((2:ℝ)^K) (d:ℝ)⁻¹ := by
  have hd : d ∈ ⋃ j : ℕ, band j := by rw [iUnion_band]; trivial
  obtain ⟨j, hj⟩ := mem_iUnion.mp hd
  exact scaledKernel_sum_band K j d hj

theorem sqrt_kernel_le_scaled (ξ : Measure Gap) [IsFiniteMeasure ξ] (k : ℕ) :
    sqrt (eta ξ (4^k)*ordinaryCost ξ (4^k)) ≤ ∫ d : Gap, scaledKernel k (d:ℝ) ∂ξ := by
  have he := eta_nonneg ξ ((4:ℝ)^k)
  have hw := ordinaryCost_nonneg ξ (by positivity : (0:ℝ) ≤ 4^k)
  have hsa := sq_sqrt (mul_nonneg he hw)
  have hz := sqrt_nonneg (eta ξ (4^k)*ordinaryCost ξ (4^k))
  have hp : (0:ℝ) < 2^k := by positivity
  have hi : (2:ℝ)^k*(2:ℝ)⁻¹^k = 1 := by simp [inv_pow]
  have hf : (∫ d : Gap, scaledKernel k (d:ℝ) ∂ξ) =
      ((2:ℝ)^k*eta ξ (4^k)+(2:ℝ)⁻¹^k*ordinaryCost ξ (4^k))/2 := by
    unfold scaledKernel eta ordinaryCost
    rw [integral_div, integral_add ((integrable_ordinaryErrorKernel ξ _).const_mul _)
      ((integrable_ordinaryWorkKernel ξ (by positivity)).const_mul _),
      integral_const_mul, integral_const_mul]
  rw [hf]
  have hprod : ((2:ℝ)^k*eta ξ (4^k))*((2:ℝ)⁻¹^k*ordinaryCost ξ (4^k)) =
      eta ξ (4^k)*ordinaryCost ξ (4^k) := by
    calc
      _ = ((2:ℝ)^k*(2:ℝ)⁻¹^k)*(eta ξ (4^k)*ordinaryCost ξ (4^k)) := by ring
      _ = _ := by rw [hi, one_mul]
  have hn1 : 0 ≤ (2:ℝ)^k*eta ξ (4^k) := mul_nonneg hp.le he
  have hn2 : 0 ≤ (2:ℝ)⁻¹^k*ordinaryCost ξ (4^k) := mul_nonneg (by positivity) hw
  nlinarith [sq_nonneg ((2:ℝ)^k*eta ξ (4^k)-(2:ℝ)⁻¹^k*ordinaryCost ξ (4^k))]

theorem integrable_scaledKernel (ξ : Measure Gap) [IsFiniteMeasure ξ] (k : ℕ) :
    Integrable (fun d : Gap => scaledKernel k (d:ℝ)) ξ :=
  (((integrable_ordinaryErrorKernel ξ _).const_mul _).add
    ((integrable_ordinaryWorkKernel ξ (by positivity)).const_mul _)).div_const 2

theorem integrable_truncated_inverse (ξ : Measure Gap) [IsFiniteMeasure ξ] (K : ℕ) :
    Integrable (fun d : Gap => min ((2:ℝ)^K) (d:ℝ)⁻¹) ξ := by
  have hm : Measurable (fun d : Gap => min ((2:ℝ)^K) (d:ℝ)⁻¹) := by fun_prop
  apply Integrable.of_bound hm.aestronglyMeasurable (2^K)
  exact ae_of_all _ (fun d => by
    rw [Real.norm_of_nonneg (by positivity [d.property.1])]
    exact min_le_left _ _)

theorem dyadic_kernel_sum (ξ : Measure Gap) [IsFiniteMeasure ξ] (K : ℕ) :
    ∑ k ∈ Finset.range (K+1), sqrt (eta ξ (4^k)*ordinaryCost ξ (4^k)) ≤
      208 * ∫ d : Gap, min ((2:ℝ)^K) (d:ℝ)⁻¹ ∂ξ := by
  calc
    _ ≤ ∑ k ∈ Finset.range (K+1), ∫ d : Gap, scaledKernel k (d:ℝ) ∂ξ :=
      Finset.sum_le_sum (fun k _ => sqrt_kernel_le_scaled ξ k)
    _ = ∫ d : Gap, ∑ k ∈ Finset.range (K+1), scaledKernel k (d:ℝ) ∂ξ :=
      (integral_finsetSum _ (fun k _ => integrable_scaledKernel ξ k)).symm
    _ ≤ ∫ d : Gap, 208 * min ((2:ℝ)^K) (d:ℝ)⁻¹ ∂ξ :=
      integral_mono (integrable_finsetSum _ (fun k _ => integrable_scaledKernel ξ k))
        ((integrable_truncated_inverse ξ K).const_mul 208) (scaledKernel_sum K)
    _ = _ := integral_const_mul _ _

theorem dyadic_kernel_sum_inverse (ξ : Measure Gap) [IsFiniteMeasure ξ]
    (hI : Integrable (fun d : Gap => (d:ℝ)⁻¹) ξ) (K : ℕ) :
    ∑ k ∈ Finset.range (K+1), sqrt (eta ξ (4^k)*ordinaryCost ξ (4^k)) ≤
      208 * ∫ d : Gap, (d:ℝ)⁻¹ ∂ξ := by
  exact (dyadic_kernel_sum ξ K).trans (mul_le_mul_of_nonneg_left
    (integral_mono (integrable_truncated_inverse ξ K) hI (fun _ => min_le_right _ _))
    (by norm_num))

theorem dyadic_kernel_finset_inverse (ξ : Measure Gap) [IsFiniteMeasure ξ]
    (hI : Integrable (fun d : Gap => (d:ℝ)⁻¹) ξ) (s : Finset ℕ) :
    ∑ k ∈ s, sqrt (eta ξ (4^k)*ordinaryCost ξ (4^k)) ≤
      208 * ∫ d : Gap, (d:ℝ)⁻¹ ∂ξ := by
  have hs : s ⊆ Finset.range (s.sup id+1) := by
    intro k hk
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Finset.le_sup (f := id) hk))
  exact (Finset.sum_le_sum_of_subset_of_nonneg hs (fun _ _ _ => sqrt_nonneg _)).trans
    (dyadic_kernel_sum_inverse ξ hI (s.sup id))

theorem dyadic_kernel_sum_extended (ξ : Measure Gap) [IsFiniteMeasure ξ] (K : ℕ) :
    ∑ k ∈ Finset.range (K+1), ENNReal.ofReal (sqrt (eta ξ (4^k)*ordinaryCost ξ (4^k))) ≤
      ENNReal.ofReal 208 * ∫⁻ d : Gap, ENNReal.ofReal (d:ℝ)⁻¹ ∂ξ := by
  rw [← ENNReal.ofReal_sum_of_nonneg (fun _ _ => sqrt_nonneg _)]
  calc
    _ ≤ ENNReal.ofReal (208 * ∫ d : Gap, min ((2:ℝ)^K) (d:ℝ)⁻¹ ∂ξ) :=
      ENNReal.ofReal_le_ofReal (dyadic_kernel_sum ξ K)
    _ = ENNReal.ofReal 208 * ∫⁻ d : Gap, ENNReal.ofReal (min ((2:ℝ)^K) (d:ℝ)⁻¹) ∂ξ := by
      rw [ENNReal.ofReal_mul (by norm_num), ofReal_integral_eq_lintegral_ofReal
        (integrable_truncated_inverse ξ K) (ae_of_all _ (fun d => by positivity [d.property.1]))]
    _ ≤ _ := by
      apply mul_le_mul_right
      apply lintegral_mono
      intro d
      exact ENNReal.ofReal_le_ofReal (min_le_right _ _)

theorem dyadic_kernel_tsum_extended (ξ : Measure Gap) [IsFiniteMeasure ξ] :
    (∑' k : ℕ, ENNReal.ofReal (sqrt (eta ξ (4^k)*ordinaryCost ξ (4^k)))) ≤
      ENNReal.ofReal 208 * ∫⁻ d : Gap, ENNReal.ofReal (d:ℝ)⁻¹ ∂ξ := by
  apply ENNReal.tsum_le_of_sum_range_le
  intro n
  exact (Finset.sum_le_sum_of_subset (Finset.range_mono (Nat.le_succ n))).trans
    (dyadic_kernel_sum_extended ξ n)

end ThresholdHC.EntropyTailAssembly
