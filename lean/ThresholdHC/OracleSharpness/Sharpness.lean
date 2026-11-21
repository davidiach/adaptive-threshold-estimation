import ThresholdHC.OracleSharpness.SignPopulation
import ThresholdHC.SharpRMS.OracleReduction

/-! Sharpness of the oracle upper coefficient one half. At a point mass the
magnitude-oracle reduction SharpRMS.oracle_gap_reduction, taken with the
target law equal to the same point mass, gives every budgeted oracle
estimator at least the ordinary single-gap minimax risk, because the modulus
of a point mass at its own gap is one. The auxiliary ordinary bound then
applies once the gap is small enough for the flip price to fit. -/
noncomputable section
namespace ThresholdHC.OracleSharpness
open MeasureTheory Real Tier6 OracleLower
open scoped ENNReal

private theorem dirac_modulus (g : Gap) (h : ℝ) (hg : g.val ≤ h) :
    modulus (Measure.dirac g) h = 1 := by
  simp only [modulus, integral_dirac, clippedGap]
  exact min_eq_left ((one_le_div g.property.1).2 hg)

/-- A lower bound on the ordinary single-gap minimax risk transfers to both
oracle minimax risks at the same point mass. -/
theorem oracle_point_lower (g : Gap) (B c : ℝ)
    (low : ENNReal.ofReal c ≤ minimaxRisk (Measure.dirac g) B) :
    ENNReal.ofReal c ≤ revealedMinimaxRisk (Measure.dirac g) B ∧
    ENNReal.ofReal c ≤ selectedMinimaxRisk (Measure.dirac g) B := by
  have all (R : Type) [MeasurableSpace R] (A : OracleEstimator R) (hb : OracleBudget A B) :
      ENNReal.ofReal c ≤ oracleRisk (Measure.dirac g) A := by
    have h := SharpRMS.oracle_gap_reduction (Measure.dirac g) g A B hb
    rw [dirac_modulus g g.val le_rfl, ENNReal.ofReal_one, one_mul] at h
    exact low.trans h
  constructor
  · apply le_sInf
    rintro x ⟨R,mR,A,hb,rfl⟩
    exact all _ (revealedOracle (Measure.dirac g) A) hb
  · apply le_sInf
    rintro x ⟨R,mR,A,hb,rfl⟩
    exact all R (selectedOracle A) hb

/-- For a flip bias at most 2/5 the inverse hyperbolic tangent is at most
11/10 of it. -/
private theorem artanh_le (s : ℝ) (hs : 0 < s) (hs' : s ≤ 2/5) : artanh s ≤ 11/10*s := by
  have hp := SharpRMS.small_bias_price s hs hs'
  rw [div_le_iff₀ hs] at hp
  nlinarith

/-- For every budget at least one and every coefficient below one half, every
point mass at a gap at most min (1/5) ((1 - 4 c'^2)/(5 B)), with c' the
midpoint of max c 0 and one half, defeats the coefficient for both oracles. -/
theorem oracle_small_gap_sharp (B c : ℝ) (hB : 1 ≤ B) (hc : c < 1/2) :
    ∃ g₀ : ℝ, 0 < g₀ ∧ ∀ g : Gap, g.val ≤ g₀ →
      ENNReal.ofReal (modulus (Measure.dirac g) (1 / Real.sqrt B) * c) <
        revealedMinimaxRisk (Measure.dirac g) B ∧
      ENNReal.ofReal (modulus (Measure.dirac g) (1 / Real.sqrt B) * c) <
        selectedMinimaxRisk (Measure.dirac g) B := by
  let c' := (max c 0 + 1/2)/2
  have hm1 := le_max_left c 0
  have hm2 := le_max_right c 0
  have hm3 : max c 0 < 1/2 := max_lt hc (by norm_num)
  have hc'0 : 0 < c' := by dsimp [c']; linarith
  have hc'1 : c' < 1/2 := by dsimp [c']; linarith
  have hcc : c < c' := by dsimp [c']; linarith
  let δ := 1 - 4*c'^2
  have hδ : 0 < δ := by dsimp [δ]; nlinarith
  have hδ1 : δ ≤ 1 := by dsimp [δ]; nlinarith [sq_nonneg c']
  have hB0 : 0 < B := by linarith
  refine ⟨min (1/5) (δ/(5*B)), lt_min (by norm_num) (by positivity), ?_⟩
  intro g hg
  have hg1 : g.val ≤ 1/5 := hg.trans (min_le_left ..)
  have hg2 : g.val ≤ δ/(5*B) := hg.trans (min_le_right ..)
  have gpos := g.property.1
  have gB : g.val * (5*B) ≤ δ := by rwa [le_div_iff₀ (by positivity)] at hg2
  have hsq : g.val ≤ 1/Real.sqrt B := by
    have h1 : 1 ≤ Real.sqrt B := by
      rw [show (1:ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]
      exact Real.sqrt_le_sqrt hB
    have hsB : Real.sqrt B ≤ B := by nlinarith [Real.sq_sqrt hB0.le]
    rw [le_div_iff₀ (by linarith)]
    nlinarith [mul_le_mul_of_nonneg_left hsB gpos.le]
  have hmod := dirac_modulus g (1/Real.sqrt B) hsq
  let s := 2*g.val
  have hs : 0 < s := by positivity
  have hart := artanh_le s hs (by dsimp [s]; linarith)
  have hbudget : 2*g.val*artanh (2*g.val)*B ≤ 1 - 4*c'^2 := by
    change s*artanh s*B ≤ δ
    have h1 : s*artanh s*B ≤ s*(11/10*s)*B :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hart hs.le) hB0.le
    have h2 : s*(11/10*s)*B = 22/25*(g.val*(g.val*(5*B))) := by dsimp [s]; ring
    have h3 : g.val*(g.val*(5*B)) ≤ g.val*δ := mul_le_mul_of_nonneg_left gB gpos.le
    have h4 : g.val*δ ≤ 1/5*δ := mul_le_mul_of_nonneg_right hg1 hδ.le
    linarith
  have low := small_gap_minimax_lower g B c' hB0.le hc'0.le (by linarith) hbudget
  obtain ⟨hr, hsl⟩ := oracle_point_lower g B c' low
  have hlt : ENNReal.ofReal (modulus (Measure.dirac g) (1 / Real.sqrt B) * c) <
      ENNReal.ofReal c' := by
    rw [hmod, one_mul]
    exact (ENNReal.ofReal_lt_ofReal_iff hc'0).2 hcc
  exact ⟨hlt.trans_le hr, hlt.trans_le hsl⟩

end ThresholdHC.OracleSharpness
