import ThresholdHC.RadialUpper.Ruin
import ThresholdHC.RadialUpper.GapIntegrals
import ThresholdHC.RadialUpper.Call

/-! Calibration constants of the radial call and their bounds.

With `M = ceil(2/b)`, upper boundary `K = M+1` and flip cap `N = ceil(50/b^2)`:
the averaged negative-coin hit probability is `F <= (9/8) b^2`, the slope of the hit
probability along the submodel is `d0 >= 4 b^2`, the hit probability under `q_eta`
is exactly `F + (1+eta) d0`, and the expected number of flips under `q_eta` is at
most `4 + (3/2) K rho <= 115/4 < 29`. -/

noncomputable section
namespace ThresholdHC.RadialUpper
open MeasureTheory Set ThresholdHC.Tier6 ThresholdHC.ObservableSimulation
open ThresholdHC.ConfidenceTransfer (criticalPositiveLaw)

/-- The upper boundary `K = M+1`, with `M = ceil(2/b)`. -/
def radialTop (b : ℝ) : ℕ := ⌈2/b⌉₊ + 1

/-- The flip cap `N = ceil(50/b^2)`. -/
def radialCap (b : ℝ) : ℕ := ⌈50/b^2⌉₊

def upHit (K N : ℕ) (x : ℝ) : ℝ := walkSum (1/2+x) K N 1 (fun r => walkHit K r.2)
def downHit (K N : ℕ) (x : ℝ) : ℝ := walkSum (1/2-x) K N 1 (fun r => walkHit K r.2)
def upCost (K N : ℕ) (x : ℝ) : ℝ := walkSum (1/2+x) K N 1 (fun r => (r.1 : ℝ))
def downCost (K N : ℕ) (x : ℝ) : ℝ := walkSum (1/2-x) K N 1 (fun r => (r.1 : ℝ))

/-- `F`: the upper-hit probability of a negative coin, averaged over the gap law. -/
def radialMiss (b : ℝ) : ℝ :=
  ∫ d, downHit (radialTop b) (radialCap b) d ∂criticalPositiveLaw

/-- `d0`: the slope of the upper-hit probability along the radial submodel. -/
def radialSlope (b : ℝ) : ℝ :=
  ∫ d, radialWeight b d / 2 *
    (upHit (radialTop b) (radialCap b) d - downHit (radialTop b) (radialCap b) d) ∂criticalPositiveLaw

theorem radialTop_two {b : ℝ} (hb : 0 < b) : 2 ≤ radialTop b := by
  have : 0 < ⌈2/b⌉₊ := Nat.ceil_pos.mpr (by positivity)
  unfold radialTop; omega

theorem radialTop_bounds {b : ℝ} (hb : 0 < b) :
    2/b ≤ ((radialTop b : ℕ) : ℝ) - 1 ∧ ((radialTop b : ℕ) : ℝ) ≤ 2/b + 2 := by
  unfold radialTop
  push_cast
  have h1 := Nat.le_ceil (2/b)
  have h2 := Nat.ceil_lt_add_one (show 0 ≤ 2/b by positivity)
  constructor <;> linarith

theorem radialCap_bounds {b : ℝ} (hb : 0 < b) :
    0 < radialCap b ∧ 50/b^2 ≤ (radialCap b : ℝ) :=
  ⟨Nat.ceil_pos.mpr (by positivity), Nat.le_ceil _⟩

theorem continuous_upHit (K N : ℕ) : Continuous (upHit K N) :=
  (continuous_walkSum K N 1 _).comp (continuous_const.add continuous_id)
theorem continuous_downHit (K N : ℕ) : Continuous (downHit K N) :=
  (continuous_walkSum K N 1 _).comp (continuous_const.sub continuous_id)
theorem continuous_upCost (K N : ℕ) : Continuous (upCost K N) :=
  (continuous_walkSum K N 1 _).comp (continuous_const.add continuous_id)
theorem continuous_downCost (K N : ℕ) : Continuous (downCost K N) :=
  (continuous_walkSum K N 1 _).comp (continuous_const.sub continuous_id)

theorem measurable_radialWeight (b : ℝ) : Measurable (radialWeight b) := by
  unfold radialWeight; fun_prop

theorem radialWeight_nonneg (b : ℝ) (d : Gap) : 0 ≤ radialWeight b d :=
  le_min zero_le_one (by positivity)

theorem radialWeight_le_one (b : ℝ) (d : Gap) : radialWeight b d ≤ 1 := min_le_left _ _

theorem radialSign_val (b : ℝ) (η : RadialIndex) (d : Gap) :
    (radialSign b η).val d = (1+(η:ℝ))/2 * radialWeight b d := rfl

theorem stat_hit_bounds {p : ℝ} (h0 : 0 ≤ p) (h1 : p ≤ 1) (K N : ℕ) :
    0 ≤ walkSum p K N 1 (fun r => walkHit K r.2) ∧ walkSum p K N 1 (fun r => walkHit K r.2) ≤ 1 :=
  ⟨walkSum_nonneg h0 h1 K N 1 (fun _ => walkHit_nonneg _ _),
    walkSum_le_const h0 h1 K N 1 (fun _ => walkHit_le_one _ _)⟩

theorem stat_cost_bounds {p : ℝ} (h0 : 0 ≤ p) (h1 : p ≤ 1) (K N : ℕ) :
    0 ≤ walkSum p K N 1 (fun r => (r.1 : ℝ)) ∧ walkSum p K N 1 (fun r => (r.1 : ℝ)) ≤ N := by
  refine ⟨walkSum_nonneg h0 h1 K N 1 (fun r => Nat.cast_nonneg _), ?_⟩
  have h := walkSum_mono h0 h1 K N 1 (g := fun r => (r.1 : ℝ)) (h := fun _ => (N : ℝ))
    (fun w => Nat.cast_le.mpr (walkRun_steps_le K N 1 w))
  rwa [walkSum_const] at h

theorem gap_up_range (d : Gap) : 0 ≤ 1/2+(d:ℝ) ∧ 1/2+(d:ℝ) ≤ 1 :=
  ⟨by linarith [d.2.1], by linarith [d.2.2]⟩

theorem gap_down_range (d : Gap) : 0 ≤ 1/2-(d:ℝ) ∧ 1/2-(d:ℝ) ≤ 1 :=
  ⟨by linarith [d.2.2], by linarith [d.2.1]⟩

theorem gap_integrable {f : Gap → ℝ} (hf : Measurable f) (C : ℝ) (hC : ∀ d, |f d| ≤ C) :
    Integrable f criticalPositiveLaw :=
  Integrable.of_bound hf.aestronglyMeasurable C
    (ae_of_all _ fun d => by rw [Real.norm_eq_abs]; exact hC d)

theorem integrable_downHit (K N : ℕ) :
    Integrable (fun d : Gap => downHit K N d) criticalPositiveLaw := by
  refine gap_integrable ((continuous_downHit K N).measurable.comp measurable_subtype_coe) 1
    (fun d => ?_)
  have h := stat_hit_bounds (gap_down_range d).1 (gap_down_range d).2 K N
  rw [abs_le]; constructor <;> unfold downHit <;> linarith [h.1, h.2]

theorem integrable_slope (b : ℝ) (K N : ℕ) :
    Integrable (fun d : Gap => radialWeight b d / 2 * (upHit K N d - downHit K N d))
      criticalPositiveLaw := by
  refine gap_integrable (((measurable_radialWeight b).div_const 2).mul
    (((continuous_upHit K N).measurable.comp measurable_subtype_coe).sub
      ((continuous_downHit K N).measurable.comp measurable_subtype_coe))) 1 (fun d => ?_)
  have hu := stat_hit_bounds (gap_up_range d).1 (gap_up_range d).2 K N
  have hv := stat_hit_bounds (gap_down_range d).1 (gap_down_range d).2 K N
  have hw0 := radialWeight_nonneg b d
  have hw1 := radialWeight_le_one b d
  change |radialWeight b d / 2 * (walkSum _ K N 1 _ - walkSum _ K N 1 _)| ≤ 1
  rw [abs_le]
  constructor <;> nlinarith [hu.1, hu.2, hv.1, hv.2]

/-- The hit probability along the submodel is affine: `z_eta = F + (1+eta) d0`. -/
theorem radial_hit_formula (b : ℝ) (η : RadialIndex) (K N : ℕ) :
    (∫ ω, walkHit K (walkRun K N 1 (Tier2.tapePrefix N ω)).2
        ∂originalPopulationTapeLaw criticalPositiveLaw (radialSign b η)) =
      (∫ d, downHit K N d ∂criticalPositiveLaw) + (1+(η:ℝ)) *
        ∫ d, radialWeight b d / 2 * (upHit K N d - downHit K N d) ∂criticalPositiveLaw := by
  rw [walk_population_integral criticalPositiveLaw (radialSign b η) K N (fun r => walkHit K r.2)]
  have he : (fun d : Gap => (radialSign b η).val d * walkSum (1/2+(d:ℝ)) K N 1 (fun r => walkHit K r.2) +
      (1-(radialSign b η).val d) * walkSum (1/2-(d:ℝ)) K N 1 (fun r => walkHit K r.2)) =
      fun d : Gap => downHit K N d + (1+(η:ℝ)) * (radialWeight b d / 2 * (upHit K N d - downHit K N d)) := by
    funext d
    rw [radialSign_val]
    unfold upHit downHit
    ring
  rw [he, integral_add (integrable_downHit K N) ((integrable_slope b K N).const_mul _),
    integral_const_mul]

theorem radialSign_mean {ρ b : ℝ} (h : RadialCalibrated ρ b) (η : RadialIndex) :
    signMean criticalPositiveLaw (radialSign b η).val = (1+(η:ℝ))/2 * ρ := by
  unfold signMean
  simp only [radialSign_val]
  rw [integral_const_mul]
  exact congrArg _ h.2.2

theorem walkRatio_le_exp {d : ℝ} (hd0 : 0 ≤ d) (hd : d ≤ 1/4) :
    walkRatio d ≤ Real.exp (-(8/3*d)) := by
  have h1 : walkRatio d = -(2*d/(1/2+d)) + 1 := by rw [← one_sub_walkRatio hd0]; ring
  have h2 : 8/3*d ≤ 2*d/(1/2+d) := by rw [le_div_iff₀ (by linarith)]; nlinarith
  rw [h1]
  exact (Real.add_one_le_exp _).trans (Real.exp_le_exp.mpr (by linarith))

theorem eight_thirds_le_one_sub {d : ℝ} (hd0 : 0 ≤ d) (hd : d ≤ 1/4) :
    8/3*d ≤ 1 - walkRatio d := by
  rw [one_sub_walkRatio hd0, le_div_iff₀ (by linarith)]
  nlinarith

/-- `F <= (9/8) b^2`. -/
theorem radialMiss_le {b : ℝ} (hb : 0 < b) : radialMiss b ≤ 9/8*b^2 := by
  set M : ℕ := ⌈2/b⌉₊
  have hM : 2/b ≤ (M : ℝ) := Nat.le_ceil _
  have hM0 : 0 < (M : ℝ) := lt_of_lt_of_le (by positivity) hM
  set l : ℝ := 8/3*M with hl
  have hl0 : 0 < l := by positivity
  have hexp : Integrable (fun d : Gap => Real.exp (-(l*(d:ℝ)))) criticalPositiveLaw :=
    gap_integrable (by fun_prop) 1 (fun d => by
      rw [abs_of_nonneg (Real.exp_pos _).le, Real.exp_le_one_iff]
      have := d.2.1; nlinarith)
  have hle : radialMiss b ≤ ∫ d, Real.exp (-(l*(d:ℝ))) ∂criticalPositiveLaw := by
    apply integral_mono_ae (integrable_downHit _ _) hexp
    filter_upwards [radial_support] with d hd
    have hd0 : 0 ≤ (d:ℝ) := d.2.1.le
    have h1 := down_hit_upper hd0 d.2.2 (radialTop b) (radialCap b)
    have h2 : radialTop b - 1 = M := by unfold radialTop; omega
    rw [h2] at h1
    have h3 := pow_le_pow_left₀ (walkRatio_nonneg hd0 d.2.2) (walkRatio_le_exp hd0 hd) M
    rw [← Real.exp_nat_mul] at h3
    have h4 : (M : ℝ) * -(8/3*(d:ℝ)) = -(l*d) := by rw [hl]; ring
    rw [h4] at h3
    exact h1.trans h3
  have hint := positive_integral_density (fun x => Real.exp (-(l*x))) (by fun_prop)
  refine hle.trans ?_
  rw [hint]
  refine (density_exp_le hl0).trans ?_
  rw [div_le_iff₀ (by positivity)]
  have hlb : 16/3 ≤ l*b := by
    rw [hl]
    have : 2 ≤ (M:ℝ)*b := by rwa [div_le_iff₀ hb] at hM
    nlinarith
  nlinarith

/-- `d0 >= 4 b^2`, from the ruin lower bound, the cap, and `E[w_b D] >= 4 b^2`. -/
theorem radialSlope_ge {ρ b : ℝ} (hρ : 0 < ρ) (hρq : ρ ≤ 1/4) (h : RadialCalibrated ρ b) :
    4*b^2 ≤ radialSlope b := by
  obtain ⟨hb0, hb8, _, hρ8, _⟩ := calibrated_facts hρ hρq h
  set K := radialTop b with hK
  set N := radialCap b with hN
  have hKb := radialTop_bounds hb0
  have hNb := radialCap_bounds hb0
  rw [← hK] at hKb
  rw [← hN] at hNb
  have hNr : (0 : ℝ) < N := Nat.cast_pos.mpr hNb.1
  have hK1 : 1 ≤ K := by have := radialTop_two hb0; omega
  have hw : Integrable (radialWeight b) criticalPositiveLaw :=
    gap_integrable (measurable_radialWeight b) 1 (fun d => by
      rw [abs_of_nonneg (radialWeight_nonneg b d)]; exact radialWeight_le_one b d)
  have hwd : Integrable (fun d : Gap => radialWeight b d * d) criticalPositiveLaw :=
    gap_integrable ((measurable_radialWeight b).mul measurable_subtype_coe) 1 (fun d => by
      have := radialWeight_nonneg b d; have := radialWeight_le_one b d
      have := d.2.1; have := d.2.2
      rw [abs_of_nonneg (by positivity)]; nlinarith)
  have hup : Integrable (fun d : Gap => radialWeight b d / 2 * upHit K N d) criticalPositiveLaw :=
    gap_integrable (((measurable_radialWeight b).div_const 2).mul
      ((continuous_upHit K N).measurable.comp measurable_subtype_coe)) 1 (fun d => by
      have hu := stat_hit_bounds (gap_up_range d).1 (gap_up_range d).2 K N
      have := radialWeight_nonneg b d; have := radialWeight_le_one b d
      change |radialWeight b d / 2 * walkSum _ K N 1 _| ≤ 1
      rw [abs_of_nonneg (by nlinarith [hu.1])]; nlinarith [hu.1, hu.2])
  have hdn : Integrable (fun d : Gap => radialWeight b d / 2 * downHit K N d) criticalPositiveLaw :=
    gap_integrable (((measurable_radialWeight b).div_const 2).mul
      ((continuous_downHit K N).measurable.comp measurable_subtype_coe)) 1 (fun d => by
      have hu := stat_hit_bounds (gap_down_range d).1 (gap_down_range d).2 K N
      have := radialWeight_nonneg b d; have := radialWeight_le_one b d
      change |radialWeight b d / 2 * walkSum _ K N 1 _| ≤ 1
      rw [abs_of_nonneg (by nlinarith [hu.1])]; nlinarith [hu.1, hu.2])
  have hsplit : radialSlope b = (∫ d, radialWeight b d / 2 * upHit K N d ∂criticalPositiveLaw) -
      ∫ d, radialWeight b d / 2 * downHit K N d ∂criticalPositiveLaw := by
    rw [← integral_sub hup hdn]
    unfold radialSlope
    congr 1
    funext d
    ring
  have hlow : (∫ d, (4/3*(radialWeight b d * d) - (K/N) * radialWeight b d) ∂criticalPositiveLaw) ≤
      ∫ d, radialWeight b d / 2 * upHit K N d ∂criticalPositiveLaw := by
    apply integral_mono_ae ((hwd.const_mul _).sub (hw.const_mul _)) hup
    filter_upwards [radial_support] with d hd
    have hd0 : 0 ≤ (d:ℝ) := d.2.1.le
    have h1 := up_hit_lower hd0 d.2.2 K N hNb.1
    have h2 := up_cost_le d.2.1 d.2.2 K N hK1
    have h3 := eight_thirds_le_one_sub hd0 hd
    have h4 : walkSum (1/2+(d:ℝ)) K N 1 (fun r => (r.1 : ℝ)) / N ≤ 2*K/N :=
      div_le_div_of_nonneg_right h2 hNr.le
    have hw0 := radialWeight_nonneg b d
    change 4/3*(radialWeight b d * d) - (K/N) * radialWeight b d ≤
      radialWeight b d / 2 * walkSum (1/2+(d:ℝ)) K N 1 (fun r => walkHit K r.2)
    have h5 : 8/3*(d:ℝ) - 2*K/N ≤ walkSum (1/2+(d:ℝ)) K N 1 (fun r => walkHit K r.2) := by linarith
    have h6 := mul_le_mul_of_nonneg_left h5 (by linarith : 0 ≤ radialWeight b d / 2)
    have h7 : radialWeight b d / 2 * (8/3*(d:ℝ) - 2*K/N) =
        4/3*(radialWeight b d * d) - (K/N) * radialWeight b d := by ring
    linarith
  have hlowv : (∫ d, (4/3*(radialWeight b d * d) - (K/N) * radialWeight b d) ∂criticalPositiveLaw) =
      4/3*(∫ d, radialWeight b d * d ∂criticalPositiveLaw) - (K/N) * ρ := by
    rw [integral_sub (hwd.const_mul _) (hw.const_mul _), integral_const_mul, integral_const_mul]
    congr 2
    exact h.2.2
  have hhigh : (∫ d, radialWeight b d / 2 * downHit K N d ∂criticalPositiveLaw) ≤ radialMiss b / 2 := by
    have : radialMiss b / 2 = ∫ d, (1/2 : ℝ) * downHit K N d ∂criticalPositiveLaw := by
      rw [integral_const_mul]; unfold radialMiss; ring
    rw [this]
    apply integral_mono_ae hdn ((integrable_downHit K N).const_mul _)
    filter_upwards [] with d
    have hu := stat_hit_bounds (gap_down_range d).1 (gap_down_range d).2 K N
    have := radialWeight_le_one b d
    change radialWeight b d / 2 * walkSum _ K N 1 _ ≤ 1/2 * walkSum _ K N 1 _
    nlinarith [hu.1]
  have hF := radialMiss_le hb0
  have hm := weight_moment_lower hb0 hb8
  have hKρ : (K : ℝ) * ρ ≤ 33/2 := by
    have : (2/b) * ρ ≤ 16 := by rw [div_mul_eq_mul_div, div_le_iff₀ hb0]; linarith
    nlinarith
  have hKN : (K/N) * ρ ≤ 33/100*b^2 := by
    rw [div_mul_eq_mul_div, div_le_iff₀ hNr]
    have : 33/2 ≤ 33/100*b^2*N := by
      have h50 : 50 ≤ b^2 * N := by
        have := hNb.2
        rwa [div_le_iff₀ (by positivity), mul_comm] at this
      nlinarith
    linarith
  rw [hsplit]
  nlinarith [sq_nonneg b]

/-- The expected number of flips under `q_eta` is at most `115/4`. -/
theorem radial_cost_le {ρ b : ℝ} (hρ : 0 < ρ) (hρq : ρ ≤ 1/4) (h : RadialCalibrated ρ b)
    (η : RadialIndex) :
    (∫ ω, ((walkRun (radialTop b) (radialCap b) 1 (Tier2.tapePrefix (radialCap b) ω)).1 : ℝ)
        ∂originalPopulationTapeLaw criticalPositiveLaw (radialSign b η)) ≤ 115/4 := by
  obtain ⟨hb0, _, _, hρ8, _⟩ := calibrated_facts hρ hρq h
  set K := radialTop b with hK
  set N := radialCap b with hN
  have hKb := radialTop_bounds hb0
  rw [← hK] at hKb
  have hK1 : 1 ≤ K := by have := radialTop_two hb0; omega
  rw [walk_population_integral criticalPositiveLaw (radialSign b η) K N (fun r => (r.1 : ℝ))]
  have hη := η.2
  have hq : Integrable (fun d : Gap => (radialSign b η).val d * (2*K)) criticalPositiveLaw :=
    gap_integrable ((radialSign b η).2.1.mul_const _) (2*K) (fun d => by
      have := ((radialSign b η).2.2 d)
      rw [abs_of_nonneg (by nlinarith [this.1])]; nlinarith [this.2])
  have hc : Integrable (fun d : Gap => downCost K N d) criticalPositiveLaw :=
    gap_integrable ((continuous_downCost K N).measurable.comp measurable_subtype_coe) N (fun d => by
      have hu := stat_cost_bounds (gap_down_range d).1 (gap_down_range d).2 K N
      change |walkSum _ K N 1 _| ≤ N
      rw [abs_of_nonneg hu.1]; exact hu.2)
  have hlhs : Integrable (fun d : Gap => (radialSign b η).val d * walkSum (1/2+(d:ℝ)) K N 1
      (fun r => (r.1 : ℝ)) + (1-(radialSign b η).val d) * walkSum (1/2-(d:ℝ)) K N 1
      (fun r => (r.1 : ℝ))) criticalPositiveLaw := by
    refine gap_integrable ?_ (N+N) (fun d => ?_)
    · exact ((radialSign b η).2.1.mul ((continuous_upCost K N).measurable.comp
        measurable_subtype_coe)).add ((measurable_const.sub (radialSign b η).2.1).mul
        ((continuous_downCost K N).measurable.comp measurable_subtype_coe))
    · have hu := stat_cost_bounds (gap_up_range d).1 (gap_up_range d).2 K N
      have hv := stat_cost_bounds (gap_down_range d).1 (gap_down_range d).2 K N
      have hq := (radialSign b η).2.2 d
      rw [abs_le]; constructor <;> nlinarith [hu.1, hu.2, hv.1, hv.2, hq.1, hq.2]
  have hle : (∫ d, ((radialSign b η).val d * walkSum (1/2+(d:ℝ)) K N 1 (fun r => (r.1 : ℝ)) +
      (1-(radialSign b η).val d) * walkSum (1/2-(d:ℝ)) K N 1 (fun r => (r.1 : ℝ)))
        ∂criticalPositiveLaw) ≤
      ∫ d, ((radialSign b η).val d * (2*K) + downCost K N d) ∂criticalPositiveLaw := by
    apply integral_mono_ae hlhs (hq.add hc)
    filter_upwards [] with d
    have hu := up_cost_le d.2.1 d.2.2 K N hK1
    have hv := stat_cost_bounds (gap_down_range d).1 (gap_down_range d).2 K N
    have hq := (radialSign b η).2.2 d
    change _ ≤ (radialSign b η).val d * (2*K) + walkSum (1/2-(d:ℝ)) K N 1 (fun r => (r.1 : ℝ))
    nlinarith [hv.1, hq.1, hq.2]
  refine hle.trans ?_
  rw [integral_add hq hc, integral_mul_const]
  have hmean := radialSign_mean h η
  unfold signMean at hmean
  rw [hmean]
  have h4 := inverse_moment_le (downCost K N) (continuous_downCost K N)
    (fun x hx hx4 => down_cost_le hx (by linarith) K N)
  have hKρ : (K : ℝ) * ρ ≤ 33/2 := by
    have : (2/b) * ρ ≤ 16 := by rw [div_mul_eq_mul_div, div_le_iff₀ hb0]; linarith
    nlinarith
  have hKρ0 : 0 ≤ (K : ℝ) * ρ := by positivity
  nlinarith [hη.1, hη.2]

end ThresholdHC.RadialUpper
