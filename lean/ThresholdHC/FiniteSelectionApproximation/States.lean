import ThresholdHC.FiniteSelectionApproximation.Bins
import ThresholdHC.FiniteSelectionApproximation.Traces

noncomputable section
open scoped Classical
namespace ThresholdHC.FiniteSelectionApproximation
open ThresholdHC.SelectionApproximation ThresholdHC.BandCostSelection

def positiveKeys (r V : ℝ) (M : ℕ) : Finset (Option (ℤ × ℕ)) :=
  ((Finset.range (1+⌊Real.logb 2 (V/r)⌋₊)).product (Finset.range M)).image
    (fun p => some ((p.1:ℤ),p.2))

def stateKeys (r U L : ℝ) (M : ℕ) : Finset (Option (ℤ × ℕ) × Option (ℤ × ℕ)) :=
  insert (none,none) ((positiveKeys r U M).product (positiveKeys r (L*U) M))

/-- The state bound from the note, including the single all-zero state. -/
def stateCount (R L : ℝ) (M : ℕ) : ℕ :=
  1+M^2*(1+⌊Real.logb 2 R⌋₊)*(1+⌊Real.logb 2 (L*R)⌋₊)

theorem binKey_mem_positive {r V x : ℝ} {M : ℕ} (hr : 0 < r)
    (hM : 0 < M) (hx : r ≤ x) (hV : x ≤ V) : binKey r M x ∈ positiveKeys r V M := by
  have hxp := hr.trans_le hx
  obtain ⟨k,j,hkey,hj,_,_⟩ := binKey_cell hr hM hxp
  have hk : k = Int.log 2 (x/r) := by
    have he := hkey
    simp only [binKey,hxp.not_ge,↓reduceIte,Option.some.injEq,Prod.mk.injEq] at he
    exact he.1.symm
  have hxr : 1 ≤ x/r := (le_div_iff₀ hr).mpr (by simpa using hx)
  have hVr : 1 ≤ V/r := hxr.trans (div_le_div_of_nonneg_right hV hr.le)
  have hk0 : 0 ≤ k := by
    rw [hk]
    simpa using Int.log_mono_right (b := 2) (show (0:ℝ)<1 by norm_num) hxr
  have hupper : k ≤ (⌊Real.logb 2 (V/r)⌋₊:ℤ) := by
    have he : ⌊Real.logb 2 (V/r)⌋ = Int.log 2 (V/r) := by
      simpa using Real.floor_logb_natCast (b := 2) (show 0 ≤ V/r by linarith)
    rw [Int.natCast_floor_eq_floor (Real.logb_nonneg (by norm_num) hVr),he,hk]
    exact Int.log_mono_right (div_pos hxp hr) (div_le_div_of_nonneg_right hV hr.le)
  rw [hkey]
  apply Finset.mem_image.mpr
  refine ⟨(k.toNat,j),Finset.mem_product.mpr ⟨?_,Finset.mem_range.mpr hj⟩,?_⟩
  · apply Finset.mem_range.mpr
    omega
  · simp [Int.toNat_of_nonneg hk0]

theorem positiveKeys_card (r V : ℝ) (M : ℕ) :
    (positiveKeys r V M).card ≤ (1+⌊Real.logb 2 (V/r)⌋₊)*M := by
  exact Finset.card_image_le.trans (by simp [Finset.card_product])

theorem stateKeys_card (r U L : ℝ) (M : ℕ) :
    (stateKeys r U L M).card ≤ stateCount (U/r) L M := by
  calc
    (stateKeys r U L M).card ≤ ((positiveKeys r U M).product (positiveKeys r (L*U) M)).card+1 :=
      Finset.card_insert_le _ _
    _ ≤ ((1+⌊Real.logb 2 (U/r)⌋₊)*M)*((1+⌊Real.logb 2 ((L*U)/r)⌋₊)*M)+1 := by
      simp only [Finset.product_eq_sprod,Finset.card_product]
      exact Nat.add_le_add_right (Nat.mul_le_mul (positiveKeys_card _ _ _) (positiveKeys_card _ _ _)) 1
    _ = stateCount (U/r) L M := by unfold stateCount; rw [mul_div_assoc]; ring

theorem summaryKey_mem {α : Type*} {a h : α → ℝ} {xs : List α}
    {r U L : ℝ} {M : ℕ} (hr : 0 < r) (hM : 0 < M) (hL : 0 ≤ L)
    (_hA0 : 0 ≤ traceSaved a xs)
    (hAz : traceSaved a xs = 0 ∨ r ≤ traceSaved a xs)
    (hAU : traceSaved a xs ≤ U)
    (hAH : traceSaved a xs ≤ traceSaved h xs)
    (hHL : traceSaved h xs ≤ L*traceSaved a xs) :
    summaryKey (binKey r M) a h xs ∈ stateKeys r U L M := by
  rcases hAz with hz | hlo
  · have hHz : traceSaved h xs = 0 := by rw [hz] at hAH hHL; nlinarith
    simp [summaryKey,hz,hHz,binKey_zero,stateKeys]
  · apply Finset.mem_insert_of_mem
    exact Finset.mem_product.mpr ⟨binKey_mem_positive hr hM hlo hAU,
      binKey_mem_positive hr hM (hlo.trans hAH)
        (hHL.trans (mul_le_mul_of_nonneg_left hAU hL))⟩

/-- Counting keys counts actual retained traces, because compression keeps exactly
one representative for each reachable key. -/
theorem trimSolve_card_bound {α : Type*} (a h saving : α → ℝ)
    (menus : List (Finset α)) {r U L : ℝ} {M : ℕ}
    (hkeys : ∀ xs ∈ enumerate menus,
      summaryKey (binKey r M) a h xs ∈ stateKeys r U L M) :
    (trimSolve (binKey r M) a h saving menus).card ≤ stateCount (U/r) L M := by
  classical
  cases menus with
  | nil => simp [trimSolve,stateCount]
  | cons menu rest =>
    rw [trimSolve,compress_card]
    apply (Finset.card_le_card ?_).trans (stateKeys_card r U L M)
    intro k hk
    obtain ⟨xs,hxs,he⟩ := (@Finset.mem_image (List α) _ (Classical.decEq _) _ _ _).mp hk
    rw [← he]
    apply hkeys
    obtain ⟨ys,hy,x,hx,rfl⟩ := mem_extend.mp hxs
    exact mem_extend.mpr ⟨ys,trimSolve_subset _ _ _ _ _ hy,x,hx,rfl⟩

/-- Number of candidate extensions examined before trimming; it counts work
events, not arithmetic bit operations. -/
def extensionCount {α κ : Type*} (key : ℝ → κ) (a h saving : α → ℝ) : List (Finset α) → ℕ
  | [] => 0
  | menu::rest => menu.card*(trimSolve key a h saving rest).card + extensionCount key a h saving rest

theorem extensionCount_bound {α κ : Type*} (key : ℝ → κ) (a h saving : α → ℝ)
    (menus : List (Finset α)) (S : ℕ)
    (hS : ∀ rest, rest.IsSuffix menus → (trimSolve key a h saving rest).card ≤ S) :
    extensionCount key a h saving menus ≤ (menus.map Finset.card).sum*S := by
  induction menus with
  | nil => simp [extensionCount]
  | cons menu rest ih =>
    have htail : rest.IsSuffix (menu::rest) := ⟨[menu],rfl⟩
    have hrest := ih (fun tail ht => hS tail (ht.trans htail))
    simpa [extensionCount,add_mul] using Nat.add_le_add (Nat.mul_le_mul_left _ (hS rest htail)) hrest

end ThresholdHC.FiniteSelectionApproximation
