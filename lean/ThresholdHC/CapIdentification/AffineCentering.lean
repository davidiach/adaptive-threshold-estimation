import ThresholdHC.CapIdentification.AffineRecovery

/-! Centering an approximate affine recovery functional halves its maximal
residual width. The coefficient choice is uniform on the compact convex set. -/

noncomputable section
open Set
open scoped BigOperators

namespace ThresholdHC.CapIdentification

theorem compact_affine_bias {I : Type} [Fintype I]
    (K : Set (Option I → ℝ)) (hne : K.Nonempty) (hc : IsCompact K) (hv : Convex ℝ K)
    (δ : ℝ) (hδ : ∀ x ∈ K, ∀ y ∈ K, (∀ i, x (some i) = y (some i)) → x none-y none ≤ δ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ c : ℝ, ∃ w : I → ℝ, ∀ x ∈ K, |c+(∑ i, w i*x (some i))-x none| ≤ (δ+ε)/2 := by
  let D := (fun z : (Option I → ℝ) × (Option I → ℝ) => z.1-z.2) '' (K ×ˢ K)
  have hDc : IsCompact D := (hc.prod hc).image (continuous_fst.sub continuous_snd)
  have hDv : Convex ℝ D := (hv.prod hv).linear_image
    (LinearMap.fst ℝ (Option I → ℝ) (Option I → ℝ)-LinearMap.snd ℝ (Option I → ℝ) (Option I → ℝ))
  have hDn : D.Nonempty := by
    obtain ⟨x,hx⟩ := hne
    exact ⟨x-x,⟨(x,x),⟨hx,hx⟩,rfl⟩⟩
  have hDδ : ∀ z ∈ D, (∀ i, z (some i) = 0) → z none ≤ δ := by
    rintro z ⟨⟨x,y⟩,⟨hx,hy⟩,rfl⟩ hz
    exact hδ x hx y hy (fun i => sub_eq_zero.mp (hz i))
  obtain ⟨w,hw⟩ := compact_affine_recovery D hDn hDc hDv δ hDδ hε
  let e : (Option I → ℝ) → ℝ := fun x => x none-(∑ i, w i*x (some i))
  have hec : Continuous e := by dsimp only [e]; fun_prop
  obtain ⟨xH,hH,hmax⟩ := hc.exists_isMaxOn hne hec.continuousOn
  obtain ⟨xL,hL,hmin⟩ := hc.exists_isMinOn hne hec.continuousOn
  have hwidth : e xH-e xL < δ+ε := by
    have hh := hw (xH-xL) ⟨(xH,xL),⟨hH,hL⟩,rfl⟩
    have he : e xH-e xL = (xH-xL) none-∑ i, w i*(xH-xL) (some i) := by
      simp only [e,Pi.sub_apply,mul_sub,Finset.sum_sub_distrib]
      ring
    rwa [he]
  refine ⟨(e xH+e xL)/2,w,?_⟩
  intro x hx
  have hhi : e x ≤ e xH := hmax hx
  have hlo : e xL ≤ e x := hmin hx
  have he : (e xH+e xL)/2+(∑ i, w i*x (some i))-x none = (e xH+e xL)/2-e x := by
    dsimp only [e]
    ring
  rw [he]
  exact abs_le.mpr ⟨by linarith,by linarith⟩

end ThresholdHC.CapIdentification
