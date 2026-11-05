import ThresholdHC.CriticalEntropy.BernoulliPrefix

noncomputable section
open Real
namespace ThresholdHC.AnytimeLower
open ThresholdHC.CriticalEntropy

/-- Posterior sign mass from the likelihoods of one coin's observed flips. -/
def posteriorMass (q A B : ℝ) : ℝ := q*A/(q*A+(1-q)*B)

theorem posteriorMass_bounds {q A B : ℝ} (hq : 1/4 ≤ q ∧ q ≤ 3/4)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hs : 0 < A+B) :
    0 ≤ posteriorMass q A B ∧ posteriorMass q A B ≤ 1 := by
  have hz : 0 < q*A+(1-q)*B := by
    nlinarith only [mul_nonneg (by linarith : 0 ≤ q-1/4) hA,
      mul_nonneg (by linarith : 0 ≤ 3/4-q) hB,hs]
  exact ⟨div_nonneg (mul_nonneg (by linarith) hA) hz.le,
    (div_le_one hz).mpr (by nlinarith [mul_nonneg (by linarith : 0 ≤ 1-q) hB])⟩

/-- Central prior masses have a history-uniform posterior Lipschitz bound,
including a zero likelihood under either sign. -/
theorem posteriorMass_lipschitz {q r A B : ℝ}
    (hq : 1/4 ≤ q ∧ q ≤ 3/4) (hr : 1/4 ≤ r ∧ r ≤ 3/4)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hs : 0 < A+B) :
    |posteriorMass q A B-posteriorMass r A B| ≤ 4*|q-r| := by
  let u := q*A+(1-q)*B
  let v := r*A+(1-r)*B
  have hu : (A+B)/4 ≤ u := by
    dsimp [u]
    nlinarith only [mul_nonneg (by linarith : 0 ≤ q-1/4) hA,
      mul_nonneg (by linarith : 0 ≤ 3/4-q) hB]
  have hv : (A+B)/4 ≤ v := by
    dsimp [v]
    nlinarith only [mul_nonneg (by linarith : 0 ≤ r-1/4) hA,
      mul_nonneg (by linarith : 0 ≤ 3/4-r) hB]
  have hup : 0 < u := by linarith
  have hvp : 0 < v := by linarith
  have hprod : ((A+B)/4)*((A+B)/4) ≤ u*v :=
    mul_le_mul hu hv (by linarith) hup.le
  have hab : A*B/(u*v) ≤ 4 := by
    apply (div_le_iff₀ (mul_pos hup hvp)).mpr
    nlinarith only [hprod,sq_nonneg (A-B)]
  have he : posteriorMass q A B-posteriorMass r A B = (q-r)*(A*B/(u*v)) := by
    unfold posteriorMass
    change q*A/u-r*A/v = _
    field_simp
    dsimp [u,v]
    ring
  rw [he,abs_mul,abs_of_nonneg (div_nonneg (mul_nonneg hA hB) (mul_nonneg hup.le hvp.le))]
  nlinarith only [mul_le_mul_of_nonneg_left hab (abs_nonneg (q-r))]

def predictiveHead (q A B d : ℝ) : ℝ := 1/2+d*(2*posteriorMass q A B-1)

theorem predictiveHead_bounds {q A B d : ℝ} (hq : 1/4 ≤ q ∧ q ≤ 3/4)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hs : 0 < A+B) (hd : 0 ≤ d ∧ d ≤ 1/4) :
    1/4 ≤ predictiveHead q A B d ∧ predictiveHead q A B d ≤ 3/4 := by
  have h := posteriorMass_bounds hq hA hB hs
  unfold predictiveHead
  constructor <;> nlinarith only [mul_nonneg hd.1 h.1,mul_nonneg hd.1 (sub_nonneg.mpr h.2),hd.2]

/-- A weighted prior contrast at most epsilon/32 costs at most epsilon squared
in Bernoulli KL per physical flip at a gap at most one quarter. -/
theorem predictiveHead_kl {q r A B d ε : ℝ}
    (hq : 1/4 ≤ q ∧ q ≤ 3/4) (hr : 1/4 ≤ r ∧ r ≤ 3/4)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hs : 0 < A+B) (hd : 0 ≤ d ∧ d ≤ 1/4)
    (_he : 0 ≤ ε) (hcontrast : d*|q-r| ≤ ε/32) :
    klB (predictiveHead q A B d) (predictiveHead r A B d) ≤ ε^2 := by
  let p := predictiveHead q A B d
  let s := predictiveHead r A B d
  have hp := predictiveHead_bounds hq hA hB hs hd
  have hs' := predictiveHead_bounds hr hA hB hs hd
  have hpost := posteriorMass_lipschitz hq hr hA hB hs
  have hdiff : |p-s| ≤ ε/4 := by
    have hid : p-s = 2*d*(posteriorMass q A B-posteriorMass r A B) := by
      dsimp [p,s,predictiveHead]
      ring
    rw [hid,abs_mul,abs_of_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) hd.1)]
    nlinarith only [mul_le_mul_of_nonneg_left hpost
      (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) hd.1),hcontrast]
  have hsq : (p-s)^2 ≤ ε^2/16 := by
    have h := pow_le_pow_left₀ (abs_nonneg (p-s)) hdiff 2
    rw [sq_abs] at h
    nlinarith only [h]
  have hden : 3/16 ≤ s*(1-s) := by
    nlinarith only [mul_nonneg (sub_nonneg.mpr hs'.1) (sub_nonneg.mpr hs'.2)]
  have hkl := binary_kl_le_chisq p s (by dsimp [p]; linarith)
    (by dsimp [p]; linarith) (by dsimp [s]; linarith) (by dsimp [s]; linarith)
  apply hkl.trans
  apply (div_le_iff₀ (by linarith : 0 < s*(1-s))).mpr
  nlinarith only [hsq,mul_le_mul_of_nonneg_right hden (sq_nonneg ε),sq_nonneg ε]

end ThresholdHC.AnytimeLower
