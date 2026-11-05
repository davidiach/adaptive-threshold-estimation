import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Card
import Mathlib.Basic.Real.Basic

noncomputable section
open scoped Classical
namespace ThresholdHC.BandCostSelection

variable {α κ : Type*} (key : α → κ) (saved : α → ℝ)

/-- The feasible fiber of a reachable key is nonempty. -/
theorem fiber_nonempty (F : Finset α) (k : ↥(F.image key)) :
    (F.filter fun x => key x = k.val).Nonempty := by
  obtain ⟨x, hx, he⟩ := Finset.mem_image.mp k.property
  exact ⟨x, Finset.mem_filter.mpr ⟨hx, he⟩⟩

/-- Keep an actual maximizer of the saving within each reachable key. -/
def representative (F : Finset α) (k : ↥(F.image key)) : α :=
  Classical.choose ((F.filter fun x => key x = k.val).exists_max_image saved
    (fiber_nonempty key F k))

theorem representative_spec (F : Finset α) (k : ↥(F.image key)) :
    representative key saved F k ∈ F ∧ key (representative key saved F k) = k.val ∧
      ∀ x ∈ F, key x = k.val → saved x ≤ saved (representative key saved F k) := by
  have h := Classical.choose_spec ((F.filter fun x => key x = k.val).exists_max_image saved
    (fiber_nonempty key F k))
  exact ⟨(Finset.mem_filter.mp h.1).1, (Finset.mem_filter.mp h.1).2,
    fun x hx he => h.2 x (Finset.mem_filter.mpr ⟨hx, he⟩)⟩

def compress (F : Finset α) : Finset α :=
  (F.image key).attach.image (representative key saved F)

theorem compress_subset (F : Finset α) : compress key saved F ⊆ F := by
  intro x hx
  obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hx
  exact (representative_spec key saved F k).1

theorem compress_dominates (F : Finset α) {x : α} (hx : x ∈ F) :
    ∃ y ∈ compress key saved F, key y = key x ∧ saved x ≤ saved y := by
  let k : ↥(F.image key) := ⟨key x, Finset.mem_image_of_mem key hx⟩
  have h := representative_spec key saved F k
  exact ⟨representative key saved F k,
    Finset.mem_image_of_mem _ (Finset.mem_attach _ k), h.2.1, h.2.2 x hx rfl⟩

theorem key_injective_on_compress (F : Finset α) :
    Set.InjOn key (compress key saved F : Set α) := by
  intro x hx y hy he
  obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨l, _, rfl⟩ := Finset.mem_image.mp hy
  have hk := (representative_spec key saved F k).2.1
  have hl := (representative_spec key saved F l).2.1
  have : k = l := Subtype.ext (hk.symm.trans (he.trans hl))
  exact congrArg (representative key saved F) this

theorem compress_card (F : Finset α) :
    (compress key saved F).card = (F.image key).card := by
  unfold compress
  rw [Finset.card_image_of_injective, Finset.card_attach]
  intro k l he
  apply Subtype.ext
  exact (representative_spec key saved F k).2.1.symm.trans
    ((congrArg key he).trans (representative_spec key saved F l).2.1)

end ThresholdHC.BandCostSelection

