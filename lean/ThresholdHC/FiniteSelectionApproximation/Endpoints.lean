import ThresholdHC.FiniteSelectionApproximation.Parameters
import Mathlib.Data.Finset.Max

noncomputable section
open scoped Classical
namespace ThresholdHC.FiniteSelectionApproximation

/-- Rational enclosures of the original real objective at precision `N`.
These specify certified values; execution of transcendental arithmetic is a
separate refinement boundary. -/
def lowerEndpoint (N : ℕ) (x : ℝ) : ℚ := (⌊((N:ℝ)+1)*x⌋:ℚ)/((N:ℚ)+1)

def upperEndpoint (N : ℕ) (x : ℝ) : ℚ := ((⌊((N:ℝ)+1)*x⌋:ℚ)+1)/((N:ℚ)+1)

theorem endpoint_bounds (N : ℕ) (x : ℝ) :
    x-1/((N:ℝ)+1) < (lowerEndpoint N x:ℝ) ∧ (lowerEndpoint N x:ℝ) ≤ x ∧
    x ≤ (upperEndpoint N x:ℝ) ∧ (upperEndpoint N x:ℝ) ≤ x+1/((N:ℝ)+1) := by
  have hd : (0:ℝ)<(N:ℝ)+1 := by positivity
  have hlo := Int.floor_le (((N:ℝ)+1)*x)
  have hhi := Int.lt_floor_add_one (((N:ℝ)+1)*x)
  unfold lowerEndpoint upperEndpoint
  push_cast
  constructor
  · apply (lt_div_iff₀ hd).mpr
    have he : (x-1/((N:ℝ)+1))*((N:ℝ)+1) = ((N:ℝ)+1)*x-1 := by field_simp
    rw [he]
    linarith
  constructor
  · exact (div_le_iff₀ hd).mpr (by linarith)
  constructor
  · exact (le_div_iff₀ hd).mpr (by linarith)
  · apply (div_le_iff₀ hd).mpr
    have he : (x+1/((N:ℝ)+1))*((N:ℝ)+1) = ((N:ℝ)+1)*x+1 := by field_simp
    rw [he]
    linarith

/-- A sufficient finite precision, obtained from a positive lower bound rather
than assuming refinement happens to succeed. -/
def sufficientPrecision (d b : ℝ) : ℕ := ⌈(b+1)/((b-1)*d)⌉₊+1

theorem precision_error {d b : ℝ} (hd : 0 < d) (hb : 1 < b) :
    (b+1)/((sufficientPrecision d b:ℝ)+1) ≤ (b-1)*d := by
  have ht : 0 < (b-1)*d := mul_pos (sub_pos.mpr hb) hd
  have hc := Nat.le_ceil ((b+1)/((b-1)*d))
  have hmul : b+1 ≤ (⌈(b+1)/((b-1)*d)⌉₊:ℝ)*((b-1)*d) := (div_le_iff₀ ht).mp hc
  apply (div_le_iff₀ (by positivity)).mpr
  unfold sufficientPrecision
  push_cast
  nlinarith

def upperWitness {α : Type*} (F : Finset α) (hne : F.Nonempty) (J : α → ℝ) (N : ℕ) : α :=
  Classical.choose (F.exists_min_image (fun x => upperEndpoint N (J x)) hne)

def leastLower {α : Type*} (F : Finset α) (hne : F.Nonempty) (J : α → ℝ) (N : ℕ) : ℚ :=
  (F.image (fun x => lowerEndpoint N (J x))).min' (hne.image _)

theorem upperWitness_spec {α : Type*} (F : Finset α) (hne : F.Nonempty) (J : α → ℝ) (N : ℕ) :
    upperWitness F hne J N ∈ F ∧
    ∀ x ∈ F, upperEndpoint N (J (upperWitness F hne J N)) ≤ upperEndpoint N (J x) :=
  Classical.choose_spec (F.exists_min_image (fun x => upperEndpoint N (J x)) hne)

/-- The minimum lower endpoint bounds every actual objective, and the minimum
upper endpoint has an actual feasible witness. -/
theorem endpoint_minima {α : Type*} (F : Finset α) (hne : F.Nonempty) (J : α → ℝ) (N : ℕ) :
    (∀ x ∈ F, (leastLower F hne J N:ℝ) ≤ J x) ∧
    J (upperWitness F hne J N) ≤ (upperEndpoint N (J (upperWitness F hne J N)):ℝ) := by
  constructor
  · intro x hx
    have hmin : leastLower F hne J N ≤ lowerEndpoint N (J x) :=
      Finset.min'_le _ _ (Finset.mem_image_of_mem _ hx)
    exact (show (leastLower F hne J N:ℝ) ≤ (lowerEndpoint N (J x):ℝ) by exact_mod_cast hmin).trans
      (endpoint_bounds N (J x)).2.1
  · exact (endpoint_bounds N _).2.2.1

/-- Finite precision refinement terminates for every positive finite objective
family. Endpoints enclose `J`, not a surrogate used for compression. -/
theorem refinement_terminates {α : Type*} (F : Finset α) (hne : F.Nonempty)
    (J : α → ℝ) {d b : ℝ} (hd : 0 < d) (hb : 1 < b) (hlower : ∀ x ∈ F, d ≤ J x) :
    ∃ N ≤ sufficientPrecision d b,
      (upperEndpoint N (J (upperWitness F hne J N)):ℝ) ≤ b*(leastLower F hne J N:ℝ) := by
  let N := sufficientPrecision d b
  obtain ⟨v,hv,hmin⟩ := F.exists_min_image J hne
  obtain ⟨w,hw,he⟩ := Finset.mem_image.mp (Finset.min'_mem
    (F.image (fun x => lowerEndpoint N (J x))) (hne.image _))
  have he' : lowerEndpoint N (J w) = leastLower F hne J N := he
  have hl := (endpoint_bounds N (J w)).1
  rw [he'] at hl
  have hvl := hmin w hw
  have hlow : J v-1/((N:ℝ)+1) ≤ (leastLower F hne J N:ℝ) := by linarith
  have hwu := (upperWitness_spec F hne J N).2 v hv
  have hupper : (upperEndpoint N (J (upperWitness F hne J N)):ℝ) ≤ J v+1/((N:ℝ)+1) :=
    (show (upperEndpoint N (J (upperWitness F hne J N)):ℝ) ≤ (upperEndpoint N (J v):ℝ) by
      exact_mod_cast hwu).trans (endpoint_bounds N (J v)).2.2.2
  have herr := precision_error hd hb
  have herr' : (b+1)*(1/((N:ℝ)+1)) ≤ (b-1)*d := by simpa only [div_eq_mul_inv,one_mul] using herr
  have hdv := hlower v hv
  refine ⟨N,le_refl _,?_⟩
  nlinarith [mul_nonneg (sub_nonneg.mpr hb.le) (sub_nonneg.mpr hdv),
    mul_le_mul_of_nonneg_left hlow (show 0 ≤ b by linarith)]

/-- The complete endpoint chain once the retained frontier is a `β` approximation
to the original optimum. The selected witness minimizes the upper enclosure. -/
theorem endpoint_certificate {α : Type*} (F : Finset α) (hne : F.Nonempty)
    (J : α → ℝ) {d K ε : ℝ} (hd : 0 < d) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hlower : ∀ x ∈ F, d ≤ J x) (hK : ∀ x ∈ F, K ≤ J x)
    (happrox : ∃ v ∈ F, J v ≤ beta ε*K) :
    ∃ N ≤ sufficientPrecision d (beta ε), ∃ w ∈ F, ∃ l u : ℚ,
      w = upperWitness F hne J N ∧ l = leastLower F hne J N ∧ u = upperEndpoint N (J w) ∧
      0 < (l:ℝ) ∧ (l:ℝ)/beta ε ≤ K ∧ K ≤ J w ∧ J w ≤ (u:ℝ) ∧
      (u:ℝ) ≤ (1+ε)*((l:ℝ)/beta ε) := by
  obtain ⟨hb,hb2,_⟩ := beta_bounds hε hε1
  have hb0 : 0 < beta ε := lt_trans zero_lt_one hb
  obtain ⟨N,hN,hstop⟩ := refinement_terminates F hne J hd hb hlower
  let w := upperWitness F hne J N
  let l := leastLower F hne J N
  let u := upperEndpoint N (J w)
  have hw : w ∈ F := (upperWitness_spec F hne J N).1
  have hmins := endpoint_minima F hne J N
  have hJu : J w ≤ (u:ℝ) := hmins.2
  have hdu : d ≤ (u:ℝ) := (hlower w hw).trans hJu
  have hl0 : 0 < (l:ℝ) := by
    by_contra h
    have : beta ε*(l:ℝ) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hb0.le (le_of_not_gt h)
    change (u:ℝ) ≤ beta ε*(l:ℝ) at hstop
    linarith
  obtain ⟨v,hv,hvK⟩ := happrox
  have hlK : (l:ℝ)/beta ε ≤ K := (div_le_iff₀ hb0).mpr (by
    simpa only [mul_comm] using (hmins.1 v hv).trans hvK)
  refine ⟨N,hN,w,hw,l,u,rfl,rfl,rfl,hl0,hlK,hK w hw,hJu,?_⟩
  rw [← mul_div_assoc,le_div_iff₀ hb0]
  have h1 := mul_le_mul_of_nonneg_right hstop hb0.le
  have h2 := mul_le_mul_of_nonneg_right hb2 hl0.le
  change (u:ℝ)*beta ε ≤ (1+ε)*(l:ℝ)
  nlinarith only [h1,h2]

end ThresholdHC.FiniteSelectionApproximation
