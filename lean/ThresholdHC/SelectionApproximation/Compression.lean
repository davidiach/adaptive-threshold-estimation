import ThresholdHC.SelectionApproximation.Model

noncomputable section
open scoped Classical
namespace ThresholdHC.SelectionApproximation
open ThresholdHC.BandCostSelection

theorem close_refl {x : ℝ} : Close 1 x x := by simp [Close]

/-- A concrete bin map witnessing that the bin certificate is inhabited. -/
theorem validBins_identity : ValidBins 1 (fun x : ℝ => x) := by
  intro x y _ _ he
  change x = y at he
  subst y
  exact close_refl

theorem close_trans {c d x y z : ℝ} (hc : 0 ≤ c) (hd : 0 ≤ d)
    (hxy : Close c x y) (hyz : Close d y z) : Close (c*d) x z := by
  constructor
  · calc
      x ≤ c*y := hxy.1
      _ ≤ c*(d*z) := mul_le_mul_of_nonneg_left hyz.1 hc
      _ = (c*d)*z := by ring
  · calc
      z ≤ d*y := hyz.2
      _ ≤ d*(c*x) := mul_le_mul_of_nonneg_left hxy.2 hd
      _ = (c*d)*x := by ring

theorem close_add_same {c x y t : ℝ} (hc : 1 ≤ c) (ht : 0 ≤ t)
    (h : Close c x y) : Close c (t+x) (t+y) := by
  have hct : t ≤ c*t := by nlinarith [mul_nonneg (sub_nonneg.mpr hc) ht]
  constructor <;> dsimp [Close] at h <;> nlinarith [h.1, h.2]

theorem close_zero {c x : ℝ} (hx : 0 ≤ x) (h : Close c 0 x) : x = 0 := by
  exact le_antisymm (by simpa using h.2) hx

theorem trace_nonneg {α : Type*} {a : α → ℝ} (ha : ∀ x, 0 ≤ a x)
    (xs : List α) : 0 ≤ traceSaved a xs := by
  induction xs with
  | nil => simp [traceSaved]
  | cons x xs ih => simpa [traceSaved] using add_nonneg (ha x) ih

theorem trimSolve_subset {α κ : Type*} (key : ℝ → κ) (a h saving : α → ℝ)
    (menus : List (Finset α)) : trimSolve key a h saving menus ⊆ enumerate menus := by
  induction menus with
  | nil => exact fun _ hx => hx
  | cons menu rest ih =>
    intro ys hy
    obtain ⟨xs, hx, x, hm, rfl⟩ := mem_extend.mp (compress_subset _ _ _ hy)
    exact mem_extend.mpr ⟨xs, ih hx, x, hm, rfl⟩

/-- The compression invariant is proved by induction through the actual finite solver. -/
theorem compression_invariant : CompressionInvariantStatement := by
  intro α κ key a h saving c hc ha hh hbins menus xs hx
  have hc0 : 0 ≤ c := le_trans zero_le_one hc
  induction menus generalizing xs with
  | nil =>
    have he : xs = [] := Finset.mem_singleton.mp hx
    subst xs
    exact ⟨[], Finset.mem_singleton_self _, Finset.mem_singleton_self _,
      le_refl _, by simpa using (close_refl (x := traceSaved a [])),
      by simpa using (close_refl (x := traceSaved h []))⟩
  | cons menu rest ih =>
    obtain ⟨tail, ht, x, hm, rfl⟩ := mem_extend.mp hx
    obtain ⟨kept, hk, _hfeas, hs, hA, hH⟩ := ih tail ht
    have hext : x :: kept ∈ extend (trimSolve key a h saving rest) menu :=
      mem_extend.mpr ⟨kept, hk, x, hm, rfl⟩
    obtain ⟨ys, hy, hkey, hsaved⟩ := compress_dominates
      (summaryKey key a h) (traceSaved saving) _ hext
    have hcstage : 1 ≤ c^rest.length := one_le_pow₀ hc
    have hAext : Close (c^rest.length) (traceSaved a (x::tail))
        (traceSaved a (x::kept)) := by
      simpa [traceSaved] using close_add_same hcstage (ha x) hA
    have hHext : Close (c^rest.length) (traceSaved h (x::tail))
        (traceSaved h (x::kept)) := by
      simpa [traceSaved] using close_add_same hcstage (hh x) hH
    have hAkey : key (traceSaved a (x::kept)) = key (traceSaved a ys) :=
      (congrArg Prod.fst hkey).symm
    have hHkey : key (traceSaved h (x::kept)) = key (traceSaved h ys) :=
      (congrArg Prod.snd hkey).symm
    have hAbin := hbins _ _ (trace_nonneg ha _) (trace_nonneg ha _) hAkey
    have hHbin := hbins _ _ (trace_nonneg hh _) (trace_nonneg hh _) hHkey
    refine ⟨ys, hy, trimSolve_subset key a h saving _ hy, ?_, ?_, ?_⟩
    · exact le_trans (by simpa [traceSaved] using add_le_add_left hs (saving x)) hsaved
    · simpa [List.length_cons, pow_succ] using
        close_trans (pow_nonneg hc0 _) hc0 hAext hAbin
    · simpa [List.length_cons, pow_succ] using
        close_trans (pow_nonneg hc0 _) hc0 hHext hHbin

/-- Equal positive bin certificates imply the required multiplicative comparison. -/
theorem interval_close {c lo hi x y : ℝ} (hc : 0 ≤ c)
    (hx : lo ≤ x ∧ x ≤ hi) (hy : lo ≤ y ∧ y ≤ hi) (hwidth : hi ≤ c*lo) :
    Close c x y := by
  exact ⟨hx.2.trans (hwidth.trans (mul_le_mul_of_nonneg_left hy.1 hc)),
    hy.2.trans (hwidth.trans (mul_le_mul_of_nonneg_left hx.1 hc))⟩

/-- The exact dyadic subintervals used by the prototype have the advertised ratio.
The scale is any positive dyadic endpoint; the index may be any nonnegative real. -/
theorem dyadic_cell_close {scale M j x y : ℝ} (hs : 0 < scale) (hM : 0 < M)
    (hj : 0 ≤ j)
    (hx : scale*(1+j/M) ≤ x ∧ x ≤ scale*(1+(j+1)/M))
    (hy : scale*(1+j/M) ≤ y ∧ y ≤ scale*(1+(j+1)/M)) :
    Close (1+1/M) x y := by
  apply interval_close (by positivity) hx hy
  have : 0 ≤ scale*j/M^2 := by positivity
  have he : (1+1/M)*(scale*(1+j/M)) - scale*(1+(j+1)/M) = scale*j/M^2 := by
    field_simp
    ring
  linarith

/-- A zero key and certified positive intervals suffice to discharge ValidBins.
This isolates the executable bucket-index calculation from the mathematical solver. -/
theorem validBins_of_intervals {κ : Type*} (key : ℝ → κ) (zero : κ)
    (lo hi : κ → ℝ) {c : ℝ} (hc : 0 ≤ c)
    (hz : ∀ x, 0 ≤ x → (key x = zero ↔ x = 0))
    (hcell : ∀ x, 0 < x → lo (key x) ≤ x ∧ x ≤ hi (key x))
    (hwidth : ∀ k, hi k ≤ c*lo k) : ValidBins c key := by
  intro x y hx hy he
  by_cases hzero : x = 0
  · have hyzero : y = 0 := (hz y hy).1 (he.symm.trans ((hz x hx).2 hzero))
    simp [hzero, hyzero, Close]
  · have hxpos : 0 < x := lt_of_le_of_ne hx (Ne.symm hzero)
    have hypos : 0 < y := by
      apply lt_of_le_of_ne hy
      intro he0
      exact hzero ((hz x hx).1 (he.trans ((hz y hy).2 he0.symm)))
    have hycell := hcell y hypos
    rw [← he] at hycell
    exact interval_close hc (hcell x hxpos) hycell (hwidth _)

end ThresholdHC.SelectionApproximation
