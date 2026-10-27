import ThresholdHC.CriticalEntropy.CriticalLaw

noncomputable section
open MeasureTheory ProbabilityTheory Set Real
open scoped ENNReal
namespace ThresholdHC.CriticalEntropy

theorem entropy_scale_count (t d : ℝ) (hd : 0 < d) (ht : 2 ≤ t)
    (htd : 16*d ≤ t) (htsq : (16*d)^2 ≤ t) (htexp : 16*d*exp 32 ≤ t) :
    let K := ⌊t/(8*d)⌋₊
    (K : ℝ) ≤ t/(8*d) ∧ 32 ≤ log (K : ℝ) ∧
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
  have hkexp : exp 32 ≤ (K : ℝ) := le_trans
    ((le_div_iff₀ (by positivity : 0 < 16*d)).mpr (by nlinarith [htexp])) hlower
  have hklog : 32 ≤ log (K : ℝ) := by
    have h := log_le_log (exp_pos 32) hkexp
    simpa using h
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

theorem critical_annulus_mass_of_small_product (t P : ℝ) (ht : 8192 ≤ t)
    (hP : P ≤ exp (-t/2)) (K : ℕ) (hK : (K : ℝ) ≤ t/(8*log 16)) :
    ∀ i : Fin K, 560*P ≤ criticalGapLaw.real (criticalAnnulus (i.val+3)) := by
  intro i
  have hd : 0 < log (16 : ℝ) := log_pos (by norm_num)
  have hd' : log (16 : ℝ) ≤ 16 := (log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 16)).trans (by norm_num)
  let j := i.val+3
  have hij : (j : ℝ) ≤ (K : ℝ)+2 := by dsimp [j]; exact_mod_cast (show i.val+3 ≤ K+2 by omega)
  have hscale : (j : ℝ)*log 16 ≤ t/8+2*log 16 := by
    have h := (le_div_iff₀ (by positivity : 0 < 8*log (16 : ℝ))).mp hK
    nlinarith [mul_le_mul_of_nonneg_right hij hd.le]
  have hbig : (2240 : ℝ)/3 ≤ exp (t/2-(j : ℝ)*log 16) := by
    have h := add_one_le_exp (t/2-(j : ℝ)*log 16)
    linarith
  have hid : exp (-t/2)*(16 : ℝ)^j*exp (t/2-(j : ℝ)*log 16) = 1 := by
    have hpow : (16 : ℝ)^j = exp ((j : ℝ)*log 16) := by
      rw [exp_nat_mul,exp_log (by norm_num : (0 : ℝ) < 16)]
    rw [hpow,← exp_add,← exp_add]
    convert exp_zero using 1
    ring
  have hm := mul_le_mul_of_nonneg_left hbig (by positivity : 0 ≤ exp (-t/2)*(16 : ℝ)^j)
  rw [hid] at hm
  rw [criticalAnnulus_mass]
  apply (le_div_iff₀ (by positivity : 0 < 4*(16 : ℝ)^(i.val+3))).mpr
  have hmul := mul_le_mul_of_nonneg_right hP (by positivity : 0 ≤ (16 : ℝ)^j)
  change 560*P*(4*(16 : ℝ)^j) ≤ 3
  nlinarith

theorem entropy_logs_le_exp (t : ℝ) (ht : 64 ≤ t) :
    (1+t)*(1+log (1+t)) ≤ exp (t/2) := by
  have ht₀ : 0 ≤ t := by linarith
  have hlog : log (1+t) ≤ t := by
    have h := log_le_sub_one_of_pos (by linarith : 0 < 1+t)
    linarith
  have hexp := add_one_le_exp (t/8)
  have hs : 1+t ≤ (exp (t/8))^2 := by
    have hm := sq_le_sq₀ (by positivity : 0 ≤ 1+t/8) (exp_pos (t/8)).le
    have hsq : (1+t/8)^2 ≤ (exp (t/8))^2 := hm.mpr (by linarith)
    nlinarith
  have hquart : 1+t ≤ exp (t/4) := by
    convert hs using 1
    rw [← exp_nat_mul]
    congr 1
    ring
  have hsquare : (1+t)^2 ≤ exp (t/2) := by
    have h := (sq_le_sq₀ (by positivity : 0 ≤ 1+t) (exp_pos _).le).mpr hquart
    convert h using 1
    rw [← exp_nat_mul]
    congr 1
    ring
  have hh := mul_le_mul_of_nonneg_left hlog (by positivity : 0 ≤ 1+t)
  nlinarith

theorem critical_scalar_base_cost : ∃ c : ℝ, 0 < c ∧
    ∀ (ρ P : ℝ), 0 < ρ → ρ ≤ 1/4 → ρ/6 ≤ P →
      (∀ (K : ℕ), 32 ≤ log (K : ℝ) →
        (∀ i : Fin K, 560*P ≤ criticalGapLaw.real (criticalAnnulus (i.val+3))) →
        ρ*((K : ℝ)*log (K : ℝ)) ≤ (2625536/3)*P) →
      c*ρ*criticalLogFactor ρ ≤ P := by
  let d : ℝ := log 16
  let C : ℝ := 2625536/3
  have hd : 0 < d := log_pos (by norm_num)
  have hC : 0 < C := by norm_num [C]
  let T := 8192+16*d+(16*d)^2+16*d*exp 32
  have hn1 : 0 ≤ 16*d := by positivity
  have hn2 : 0 ≤ (16*d)^2 := sq_nonneg _
  have hn3 : 0 ≤ 16*d*exp 32 := by positivity
  have hT : 8192 ≤ T := by dsimp [T]; linarith
  have hTd : 16*d ≤ T := by dsimp [T]; linarith
  have hTsq : (16*d)^2 ≤ T := by dsimp [T]; linarith
  have hTexp : 16*d*exp 32 ≤ T := by dsimp [T]; linarith
  let G := (1+T)*(1+log (1+T))
  have hlogT : 0 ≤ log (1+T) := log_nonneg (by linarith)
  have hG : 0 < G := by dsimp [G]; positivity
  let c := min 1 (min (1/(256*d*C)) (1/(6*G)))
  have hc : 0 < c := by dsimp [c]; positivity
  have hc1 : c ≤ 1 := min_le_left _ _
  have hcd : c ≤ 1/(256*d*C) := (min_le_right _ _).trans (min_le_left _ _)
  have hcG : c ≤ 1/(6*G) := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨c,hc,?_⟩
  intro ρ P hρ hρ' hfloor hscales
  let t := log (1/ρ)
  have ht₀ : 0 ≤ t := log_nonneg ((le_div_iff₀ hρ).mpr (by linarith))
  have hlogt₀ : 0 ≤ log (1+t) := log_nonneg (by linarith)
  have hfactor₀ : 0 ≤ criticalLogFactor ρ := by change 0 ≤ (1+t)*(1+log (1+t)); positivity
  have hP₀ : 0 ≤ P := by linarith
  have hρexp : ρ = exp (-t) := by
    dsimp [t]
    rw [exp_neg,exp_log (by positivity : 0 < 1/ρ)]
    simp
  by_cases ht : T ≤ t
  · let K := ⌊t/(8*d)⌋₊
    obtain ⟨hKupper,hKlog,hfactor⟩ := entropy_scale_count t d hd (by linarith)
      (hTd.trans ht) (hTsq.trans ht) (hTexp.trans ht)
    change (K : ℝ) ≤ t/(8*d) at hKupper
    change 32 ≤ log (K : ℝ) at hKlog
    change criticalLogFactor ρ ≤ 256*d*((K : ℝ)*log (K : ℝ)) at hfactor
    by_cases hbig : exp (-t/2) ≤ P
    · have hg := entropy_logs_le_exp t (by linarith)
      change criticalLogFactor ρ ≤ exp (t/2) at hg
      calc
        _ ≤ ρ*criticalLogFactor ρ := by nlinarith [mul_nonneg hρ.le hfactor₀]
        _ ≤ ρ*exp (t/2) := mul_le_mul_of_nonneg_left hg hρ.le
        _ = exp (-t/2) := by rw [hρexp,← exp_add]; congr 1; ring
        _ ≤ P := hbig
    · have hmass := critical_annulus_mass_of_small_product t P (by linarith) (le_of_lt (not_le.mp hbig)) K hKupper
      have he := hscales K hKlog hmass
      have hf : ρ*criticalLogFactor ρ ≤ (256*d*C)*P := by
        calc
          _ ≤ ρ*(256*d*((K : ℝ)*log (K : ℝ))) := mul_le_mul_of_nonneg_left hfactor hρ.le
          _ = (256*d)*(ρ*((K : ℝ)*log (K : ℝ))) := by ring
          _ ≤ (256*d)*(C*P) := mul_le_mul_of_nonneg_left he (by positivity)
          _ = _ := by ring
      have hden : 0 < 256*d*C := by positivity
      have hcden : c*(256*d*C) ≤ 1 := (le_div_iff₀ hden).mp hcd
      calc
        _ = c*(ρ*criticalLogFactor ρ) := by ring
        _ ≤ c*((256*d*C)*P) := mul_le_mul_of_nonneg_left hf hc.le
        _ = (c*(256*d*C))*P := by ring
        _ ≤ P := by simpa using mul_le_mul_of_nonneg_right hcden hP₀
  · have htT : t ≤ T := (not_le.mp ht).le
    have hlog := log_le_log (by positivity : 0 < 1+t) (by linarith : 1+t ≤ 1+T)
    have hgf : criticalLogFactor ρ ≤ G :=
      mul_le_mul (by linarith : 1+t ≤ 1+T) (by linarith : 1+log (1+t) ≤ 1+log (1+T))
        (by positivity) (by positivity)
    have hcGb : c*(6*G) ≤ 1 := (le_div_iff₀ (by positivity : 0 < 6*G)).mp hcG
    have hcG' : c*G ≤ 1/6 := by linarith
    calc
      _ = ρ*(c*criticalLogFactor ρ) := by ring
      _ ≤ ρ*(c*G) := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hgf hc.le) hρ.le
      _ ≤ ρ*(1/6) := mul_le_mul_of_nonneg_left hcG' hρ.le
      _ ≤ P := by linarith

end ThresholdHC.CriticalEntropy
