import ThresholdHC.Statements2
import ThresholdHC.Proofs.KL

/-!
A single queried coin under two tilted sign priors.

The evidence values A and B may vanish, including at d = 1/2. If both are
positive, the existing likelihood-ratio KL bound applies. If one vanishes,
the two predictions coincide and contribute no conditional divergence.
-/

noncomputable section
namespace ThresholdHC.Proofs.Transcript
open ThresholdHC Real

def mixMass (q A B : ℝ) : ℝ := q*A+(1-q)*B
def mixPredict (d q A B : ℝ) : ℝ := pred d (q*A/mixMass q A B)
def klTerm (P Q : ℝ) : ℝ := P * Real.log (P/Q)

theorem mixMass_pos {q A B : ℝ} (hq : 0 < q) (hq1 : q < 1)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hAB : 0 < A+B) : 0 < mixMass q A B := by
  unfold mixMass
  by_cases hAz : A = 0
  · subst A
    have : 0 < B := by linarith
    positivity
  · have : 0 < A := lt_of_le_of_ne hA (Ne.symm hAz)
    positivity

theorem mixPredict_bounds {d q A B : ℝ} (hd : 0 ≤ d) (hd1 : d ≤ 1/2)
    (hq : 0 < q) (hq1 : q < 1) (hA : 0 ≤ A) (hB : 0 ≤ B) (hAB : 0 < A+B) :
    0 ≤ mixPredict d q A B ∧ mixPredict d q A B ≤ 1 := by
  have hm := mixMass_pos hq hq1 hA hB hAB
  have hr0 : 0 ≤ q*A/mixMass q A B := by positivity
  have hr1 : q*A/mixMass q A B ≤ 1 := by
    apply (div_le_one hm).2
    dsimp [mixMass]
    nlinarith [mul_nonneg (show 0 ≤ 1-q by linarith) hB]
  dsimp [mixPredict, pred]
  constructor
  · nlinarith [mul_nonneg hd hr0]
  · nlinarith [mul_nonneg hd (sub_nonneg.mpr hr1)]

theorem mixPredict_zero_left {d q B : ℝ} : mixPredict d q 0 B = 1/2-d := by
  simp [mixPredict, pred]

theorem mixPredict_zero_right {d q A : ℝ} (hq : q ≠ 0) (hA : A ≠ 0) :
    mixPredict d q A 0 = 1/2+d := by
  simp [mixPredict, mixMass, pred, hq, hA]
  ring

theorem mixPredict_interior {d q A B : ℝ} (hd : 0 < d) (hd1 : d ≤ 1/2)
    (hq : 0 < q) (hq1 : q < 1) (hA : 0 < A) (hB : 0 < B) :
    0 < mixPredict d q A B ∧ mixPredict d q A B < 1 := by
  have hm := mixMass_pos hq hq1 hA.le hB.le (by linarith)
  have hr0 : 0 < q*A/mixMass q A B := by positivity
  have hr1 : q*A/mixMass q A B < 1 := by
    apply (div_lt_one hm).2
    dsimp [mixMass]
    nlinarith [mul_pos (show 0 < 1-q by linarith) hB]
  exact ThresholdHC.Proofs.pred_mem_of_mem d _ hd hd1 hr0 hr1

theorem mixPredict_plus_ratio {d η A B : ℝ} (hB : B ≠ 0) :
    mixPredict d (1/2+η) A B = pred d (rhoPlus η (A/B)) := by
  have heq : (1/2+η)*(A/B)+(1/2-η) = mixMass (1/2+η) A B / B := by
    dsimp [mixMass]
    field_simp
    <;> ring
  unfold mixPredict rhoPlus
  rw [add_comm (1/2-η), heq, ← mul_div_assoc (1/2+η) A B, div_div_div_cancel_right₀ hB]

theorem mixPredict_minus_ratio {d η A B : ℝ} (hB : B ≠ 0) :
    mixPredict d (1/2-η) A B = pred d (rhoMinus η (A/B)) := by
  have heq : (1/2-η)*(A/B)+(1/2+η) = mixMass (1/2-η) A B / B := by
    dsimp [mixMass]
    field_simp
    <;> ring
  unfold mixPredict rhoMinus
  rw [add_comm (1/2+η), heq, ← mul_div_assoc (1/2-η) A B, div_div_div_cancel_right₀ hB]

theorem klB_self (u : ℝ) : klB u u = 0 := by
  by_cases hu : u = 0
  · simp [hu, klB]
  by_cases hu1 : u = 1
  · simp [hu1, klB]
  simp [klB, hu, sub_ne_zero.mpr (Ne.symm hu1)]

theorem bounded_eta_step_kl {d η h L : ℝ} (hd : 0 < d) (hd1 : d ≤ 1/2)
    (hη : 0 ≤ η) (hη1 : η ≤ 1/8) (hh : 0 < h) (hdη : d*η ≤ h/8) (hL : 0 < L) :
    klB (pred d (rhoPlus η L)) (pred d (rhoMinus η L)) ≤ (128/225)*h^2 := by
  have hc : 15/16 ≤ 1-4*η^2 := by nlinarith
  have hcpos : 0 < 1-4*η^2 := by linarith
  have hc2 : 225/256 ≤ (1-4*η^2)^2 := by nlinarith
  have hnum : 32*d^2*η^2 ≤ h^2/2 := by
    have hp : 0 ≤ (h-8*d*η)*(h+8*d*η) := mul_nonneg (by linarith) (by positivity)
    nlinarith
  have hb : 32*d^2*η^2/(1-4*η^2)^2 ≤ (128/225)*h^2 := by
    apply (div_le_iff₀ (pow_pos hcpos 2)).2
    calc
      _ ≤ h^2/2 := hnum
      _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_left hc2 (sq_nonneg h)]
  exact (ThresholdHC.Proofs.lemmaA_forward d η L hd hd1 hη (by linarith) hL).trans hb

theorem mixPredict_kl_bound {d η h A B : ℝ} (hd : 0 < d) (hd1 : d ≤ 1/2)
    (hη : 0 ≤ η) (hη1 : η ≤ 1/8) (hh : 0 < h) (hdη : d*η ≤ h/8)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hAB : 0 < A+B) :
    klB (mixPredict d (1/2+η) A B) (mixPredict d (1/2-η) A B) ≤ (128/225)*h^2 := by
  by_cases hAz : A = 0
  · simp only [hAz, mixPredict_zero_left, klB_self]
    positivity
  by_cases hBz : B = 0
  · rw [hBz, mixPredict_zero_right (by linarith : (1/2:ℝ)+η ≠ 0) hAz,
      mixPredict_zero_right (by linarith : (1/2:ℝ)-η ≠ 0) hAz, klB_self]
    positivity
  have hAp : 0 < A := lt_of_le_of_ne hA (Ne.symm hAz)
  have hBp : 0 < B := lt_of_le_of_ne hB (Ne.symm hBz)
  rw [mixPredict_plus_ratio hBz, mixPredict_minus_ratio hBz]
  exact bounded_eta_step_kl hd hd1 hη hη1 hh hdη (div_pos hAp hBp)

theorem mixPredict_pair {d η A B : ℝ} (hd : 0 < d) (hd1 : d ≤ 1/2)
    (hη : 0 ≤ η) (hη1 : η ≤ 1/8) (hA : 0 ≤ A) (hB : 0 ≤ B) (hAB : 0 < A+B) :
    ((0 < mixPredict d (1/2+η) A B ∧ mixPredict d (1/2+η) A B < 1) ∧
      (0 < mixPredict d (1/2-η) A B ∧ mixPredict d (1/2-η) A B < 1)) ∨
      mixPredict d (1/2+η) A B = mixPredict d (1/2-η) A B := by
  by_cases hAz : A = 0
  · right
    simp [hAz, mixPredict_zero_left]
  by_cases hBz : B = 0
  · right
    rw [hBz, mixPredict_zero_right (by linarith : (1/2:ℝ)+η ≠ 0) hAz,
      mixPredict_zero_right (by linarith : (1/2:ℝ)-η ≠ 0) hAz]
  have hAp : 0 < A := lt_of_le_of_ne hA (Ne.symm hAz)
  have hBp : 0 < B := lt_of_le_of_ne hB (Ne.symm hBz)
  left
  exact ⟨mixPredict_interior hd hd1 (by linarith) (by linarith) hAp hBp,
    mixPredict_interior hd hd1 (by linarith) (by linarith) hAp hBp⟩

theorem klTerm_scale_same (P Q c : ℝ) : klTerm (P*c) (Q*c) = c*klTerm P Q := by
  by_cases hc : c = 0
  · simp [hc, klTerm]
  unfold klTerm
  rw [mul_div_mul_right _ _ hc]
  ring

theorem klTerm_product {P Q u v : ℝ} (hP : 0 < P) (hQ : 0 < Q)
    (hu : 0 < u) (hv : 0 < v) :
    klTerm (P*u) (Q*v) = u*klTerm P Q + P*klTerm u v := by
  have heq : P*u/(Q*v) = (P/Q)*(u/v) := by ring
  unfold klTerm
  rw [heq, Real.log_mul (div_ne_zero hP.ne' hQ.ne') (div_ne_zero hu.ne' hv.ne')]
  ring

theorem binary_mass_chain {P Q u v : ℝ} (hP : 0 < P) (hQ : 0 < Q)
    (hp : ((0<u ∧ u<1) ∧ (0<v ∧ v<1)) ∨ u=v) :
    klTerm (P*u) (Q*v) + klTerm (P*(1-u)) (Q*(1-v)) = klTerm P Q + P*klB u v := by
  rcases hp with ⟨hu,hv⟩ | huv
  · rw [klTerm_product hP hQ hu.1 hv.1,
      klTerm_product hP hQ (sub_pos.mpr hu.2) (sub_pos.mpr hv.2)]
    unfold klB klTerm
    ring
  · subst v
    rw [klTerm_scale_same, klTerm_scale_same, klB_self]
    ring

end ThresholdHC.Proofs.Transcript
