import ThresholdHC.CriticalAllSizes.Product
import ThresholdHC.CriticalEntropy.ScaleAsymptotics

noncomputable section
open MeasureTheory ProbabilityTheory Set Real
open scoped ENNReal
namespace ThresholdHC.CriticalAllSizes
open CriticalEntropy

theorem entropy_scale_count_all (t d : ℝ) (hd : 0 < d) (ht : 2 ≤ t)
    (htd : 16*d ≤ t) (htsq : (16*d)^2 ≤ t) (htfour : 64*d ≤ t) :
    let K := ⌊t/(8*d)⌋₊
    (K : ℝ) ≤ t/(8*d) ∧ 1 ≤ log (K : ℝ) ∧
      (1+t)*(1+log (1+t)) ≤ 256*d*((K : ℝ)*log (K : ℝ)) := by
  dsimp only
  let K := ⌊t/(8*d)⌋₊
  have htwo : (2 : ℝ) ≤ t/(8*d) := (le_div_iff₀ (by positivity)).mpr (by linarith)
  have hupper : (K : ℝ) ≤ t/(8*d) := Nat.floor_le (by positivity)
  have hlower : t/(16*d) ≤ (K : ℝ) := by
    have hf := Nat.lt_floor_add_one (t/(8*d))
    change t/(8*d) < (K : ℝ)+1 at hf
    have he : t/(16*d) = (t/(8*d))/2 := by ring
    rw [he]
    linarith
  have hkpos : 0 < (K : ℝ) := (div_pos (by linarith : 0 < t) (by positivity)).trans_le hlower
  have hkfour : (4 : ℝ) ≤ K := le_trans
    ((le_div_iff₀ (by positivity : 0 < 16*d)).mpr (by linarith)) hlower
  have hklog : 1 ≤ log (K : ℝ) := by
    have hlog4 : 1 ≤ log (4 : ℝ) := by
      have he : log (4 : ℝ) = 2*log 2 := by
        convert log_pow (2 : ℝ) 2 using 1 <;> norm_num
      rw [he]
      linarith [log_two_gt_d9]
    exact hlog4.trans (log_le_log (by norm_num) hkfour)
  have hlogdiv := log_le_log (div_pos (by linarith : 0 < t) (by positivity : 0 < 16*d)) hlower
  rw [log_div (by linarith : t ≠ 0) (by positivity : 16*d ≠ 0)] at hlogdiv
  have hlogsmall : 2*log (16*d) ≤ log t := by
    have h := log_le_log (sq_pos_of_pos (by positivity : 0 < 16*d)) htsq
    simpa only [log_pow,Nat.cast_ofNat] using h
  have hloglarge : log (1+t) ≤ 2*log t := by
    have h := log_le_log (by linarith : 0 < 1+t) (show 1+t ≤ t^2 by nlinarith)
    simpa only [log_pow,Nat.cast_ofNat] using h
  have hH : 1+log (1+t) ≤ 8*log (K : ℝ) := by linarith
  have hL : 1+t ≤ 32*d*(K : ℝ) := by
    have h := (div_le_iff₀ (by positivity : 0 < 16*d)).mp hlower
    nlinarith
  have hlog₀ : 0 ≤ log (1+t) := log_nonneg (by linarith)
  refine ⟨hupper,hklog,?_⟩
  have hprod := mul_le_mul hL hH (by positivity : 0 ≤ 1+log (1+t)) (by positivity : 0 ≤ 32*d*(K : ℝ))
  nlinarith

/-- An explicit raw-moment constant. The scale cutoff is now 16384, not
a quantity containing exp 32. This is a single-coin bound, not a claim
about an explicit constant in the final population minimax theorem. -/
theorem critical_scalar_base_cost_explicit (ρ P : ℝ)
    (hρ : 0 < ρ) (hρ' : ρ ≤ 1/4) (hfloor : ρ/6 ≤ P)
    (hscales : ∀ K : ℕ,
      (∀ i : Fin K, 560*P ≤ criticalGapLaw.real (criticalAnnulus (i.val+3))) →
      ρ*((K : ℝ)*log (K : ℝ)) ≤ (21004288/3)*P) :
    (1/10000000000 : ℝ)*ρ*criticalLogFactor ρ ≤ P := by
  let d : ℝ := log 16
  let C : ℝ := 21004288/3
  let c : ℝ := 1/10000000000
  have hd : 0 < d := log_pos (by norm_num)
  have hd4 : d ≤ 4 := by
    have he : log (16 : ℝ) = 4*log 2 := by
      convert log_pow (2 : ℝ) 4 using 1 <;> norm_num
    dsimp [d]
    rw [he]
    linarith [log_two_lt_d9]
  have hc : 0 < c := by norm_num [c]
  have hc1 : c ≤ 1 := by norm_num [c]
  have hcden : c*(256*d*C) ≤ 1 := by dsimp [c,C]; nlinarith
  have hP₀ : 0 ≤ P := by linarith
  let t := log (1/ρ)
  have ht₀ : 0 ≤ t := log_nonneg ((le_div_iff₀ hρ).mpr (by linarith))
  have hlogt₀ : 0 ≤ log (1+t) := log_nonneg (by linarith)
  have hfactor₀ : 0 ≤ criticalLogFactor ρ := by
    change 0 ≤ (1+t)*(1+log (1+t)); positivity
  have hρexp : ρ = exp (-t) := by
    dsimp [t]
    rw [exp_neg,exp_log (by positivity : 0 < 1/ρ)]
    simp
  change c*ρ*criticalLogFactor ρ ≤ P
  by_cases ht : 16384 ≤ t
  · let K := ⌊t/(8*d)⌋₊
    obtain ⟨hKupper,_hKlog,hfactor⟩ := entropy_scale_count_all t d hd (by linarith)
      (by linarith) (by nlinarith [mul_nonneg hd.le (sub_nonneg.mpr hd4)]) (by linarith)
    change (K : ℝ) ≤ t/(8*d) at hKupper
    change criticalLogFactor ρ ≤ 256*d*((K : ℝ)*log (K : ℝ)) at hfactor
    by_cases hbig : exp (-t/2) ≤ P
    · have hg := entropy_logs_le_exp t (by linarith)
      change criticalLogFactor ρ ≤ exp (t/2) at hg
      calc
        _ ≤ ρ*criticalLogFactor ρ := by nlinarith [mul_nonneg hρ.le hfactor₀]
        _ ≤ ρ*exp (t/2) := mul_le_mul_of_nonneg_left hg hρ.le
        _ = exp (-t/2) := by rw [hρexp,← exp_add]; congr 1; ring
        _ ≤ P := hbig
    · have hmass := critical_annulus_mass_of_small_product t P (by linarith)
        (le_of_lt (not_le.mp hbig)) K hKupper
      have he := hscales K hmass
      have hf : ρ*criticalLogFactor ρ ≤ (256*d*C)*P := by
        calc
          _ ≤ ρ*(256*d*((K : ℝ)*log (K : ℝ))) := mul_le_mul_of_nonneg_left hfactor hρ.le
          _ = (256*d)*(ρ*((K : ℝ)*log (K : ℝ))) := by ring
          _ ≤ (256*d)*(C*P) := mul_le_mul_of_nonneg_left he (by positivity)
          _ = _ := by ring
      calc
        _ = c*(ρ*criticalLogFactor ρ) := by ring
        _ ≤ c*((256*d*C)*P) := mul_le_mul_of_nonneg_left hf hc.le
        _ = (c*(256*d*C))*P := by ring
        _ ≤ P := by simpa using mul_le_mul_of_nonneg_right hcden hP₀
  · have htT : t ≤ 16384 := (not_le.mp ht).le
    have hlog : log (1+t) ≤ t := by
      have := log_le_sub_one_of_pos (by positivity : 0 < 1+t)
      linarith
    have hgf : criticalLogFactor ρ ≤ (16385 : ℝ)^2 := by
      change (1+t)*(1+log (1+t)) ≤ _
      have hh := mul_le_mul (show 1+t ≤ 16385 by linarith)
        (show 1+log (1+t) ≤ 16385 by linarith)
        (by positivity : 0 ≤ 1+log (1+t)) (by norm_num : (0 : ℝ) ≤ 16385)
      nlinarith
    have hcG : c*(16385 : ℝ)^2 ≤ 1/6 := by norm_num [c]
    calc
      _ = ρ*(c*criticalLogFactor ρ) := by ring
      _ ≤ ρ*(c*(16385 : ℝ)^2) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hgf hc.le) hρ.le
      _ ≤ ρ*(1/6) := mul_le_mul_of_nonneg_left hcG hρ.le
      _ ≤ P := by linarith

end ThresholdHC.CriticalAllSizes

