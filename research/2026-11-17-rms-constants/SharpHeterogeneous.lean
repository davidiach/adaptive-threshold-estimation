import SharpSimulation
import SharpTranscript
import ThresholdHC.Tier6.Full

/-! The sign family and its finite adaptive mixture under a general gap law. -/
noncomputable section
namespace ThresholdHC.SharpRMS
open MeasureTheory Tier3 Tier5 Tier6 Proofs

def attenuatedSign (h t : ℝ) (hh : 0 ≤ h) (ht : |t| ≤ 1) : SignLaw :=
  ⟨fun d => (1+t*clippedGap h d)/2,by unfold clippedGap; fun_prop,fun d => by
    have f : clippedGap h d ∈ Set.Icc 0 1 :=
      ⟨le_min zero_le_one (div_nonneg hh d.property.1.le),min_le_left ..⟩
    have v : |t*clippedGap h d| ≤ 1 := by
      rw [abs_mul,abs_of_nonneg f.1]
      exact (mul_le_mul_of_nonneg_right ht f.1).trans (by simpa using f.2)
    constructor <;> linarith [(abs_le.mp v).1,(abs_le.mp v).2]⟩

theorem attenuated_target (μ : Measure Gap) [IsProbabilityMeasure μ] (h t : ℝ)
    (hh : 0 ≤ h) (ht : |t| ≤ 1) :
    signMean μ (attenuatedSign h t hh ht).val = (1+t*modulus μ h)/2 := by
  have hm : Measurable (clippedGap h) := by unfold clippedGap; fun_prop
  have hi : Integrable (clippedGap h) μ := (integrable_const (1:ℝ)).mono' hm.aestronglyMeasurable
    (ae_of_all _ fun d => by
      have hp : 0 ≤ clippedGap h d := le_min zero_le_one (div_nonneg hh d.property.1.le)
      rw [Real.norm_eq_abs,abs_of_nonneg hp]; exact min_le_left ..)
  change (∫ d, (1+t*clippedGap h d)/2 ∂μ) = _
  rw [integral_div,integral_add (integrable_const (1:ℝ)) (hi.const_mul t),integral_const_mul]
  simp [modulus]

def conditionalPrior (f : ℝ) (e : Bool) := if e then (1+f)/2 else (1-f)/2

/-- Conditioning on the independent signs of the critical source and then
integrating them gives exactly the target distribution of each adaptive word. -/
theorem signed_prefix_mixture {m n : ℕ} (pol : List Bool → Option (Fin m)) (d f : Fin m → ℝ)
    (t : ℝ) (w : Prefix n) :
    transcriptLaw pol d (fun i => (1+t*f i)/2) w =
      ∑ e : Fin m → Bool, (∏ i, if e i then (1+t)/2 else (1-t)/2) *
        transcriptLaw pol d (fun i => conditionalPrior (f i) (e i)) w := by
  let v := pathValidity pol w
  let a i := coinLike pol w i (1/2+d i)
  let b i := coinLike pol w i (1/2-d i)
  let c (i : Fin m) (e : Bool) := (if e then (1+t)/2 else (1-t)/2)*
    (conditionalPrior (f i) e*a i+(1-conditionalPrior (f i) e)*b i)
  have mix (i : Fin m) : (∑ e : Bool, c i e) = (1+t*f i)/2*a i+(1-(1+t*f i)/2)*b i := by
    simp [c,conditionalPrior]
    ring
  rw [transcriptLaw_factor]
  calc
    _ = v*∏ i, ∑ e : Bool, c i e := by simp_rw [mix]; rfl
    _ = v*∑ e : Fin m → Bool, ∏ i, c i (e i) := by rw [Fintype.prod_sum]
    _ = _ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro e _
      rw [transcriptLaw_factor]
      simp only [c,Finset.prod_mul_distrib]
      change v*(_*_) = _*(v*_)
      ring

/-- The zero-net-count lattice gap holds at every binary word, including
perfect coins and words with zero mixture probability. -/
theorem word_posterior_gap (a : ℝ) (ha : 0<a) (ha' : a≤1) (h l : ℕ) :
    let p := (1+a)/2
    let q := (1-a)/2
    let A := p^h*q^l
    let B := q^h*p^l
    let z := (A-B)/(A+B)
    |z| ≤ 1 ∧ (z=0 ∨ a≤|z|) := by
  let p := (1+a)/2
  let q := (1-a)/2
  have hp : 0≤p := by dsimp [p]; linarith
  have hq : 0≤q := by dsimp [q]; linarith
  have qp : q≤p := by dsimp [q,p]; linarith
  have sep (j k : ℕ) (hk : j<k) : p*(q^k*p^j) ≤ q*(p^k*q^j) := by
    obtain ⟨m,hm⟩ := Nat.exists_eq_add_of_le (show j+1≤k from hk)
    rw [hm,pow_add q (j+1) m,pow_add p (j+1) m,pow_succ q j,pow_succ p j]
    nlinarith only [mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hp hq) (pow_nonneg hp j)) (pow_nonneg hq j))
      (sub_nonneg.mpr (pow_le_pow_left₀ hq qp m))]
  let A := p^h*q^l
  let B := q^h*p^l
  have A0 : 0≤A := mul_nonneg (pow_nonneg hp _) (pow_nonneg hq _)
  have B0 : 0≤B := mul_nonneg (pow_nonneg hq _) (pow_nonneg hp _)
  change |(A-B)/(A+B)| ≤ 1 ∧ ((A-B)/(A+B)=0 ∨ a≤|(A-B)/(A+B)|)
  by_cases zero : A+B=0
  · simp [zero]
  have pos : 0<A+B := lt_of_le_of_ne (add_nonneg A0 B0) (Ne.symm zero)
  refine ⟨abs_le.mpr ⟨(le_div_iff₀ pos).mpr (by linarith),(div_le_iff₀ pos).mpr (by linarith)⟩,?_⟩
  rcases lt_trichotomy h l with hl|he|lh
  · have s : p*A ≤ q*B := by simpa [A,B,mul_comm] using sep h l hl
    right
    apply le_trans _ (neg_le_abs _)
    rw [le_neg,div_le_iff₀ pos]
    dsimp [p,q] at s
    linarith only [s]
  · subst l
    left
    simp [A,B,mul_comm]
  · have s : p*B ≤ q*A := sep l h lh
    right
    apply le_trans _ (le_abs_self _)
    apply (le_div_iff₀ pos).mpr
    dsimp [p,q] at s
    linarith only [s]

end ThresholdHC.SharpRMS
