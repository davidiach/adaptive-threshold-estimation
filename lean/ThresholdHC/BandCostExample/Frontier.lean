import ThresholdHC.BandCostSelection.Counting
import Mathlib.Tactic.Ring

/-! Exact frontier sizes of the cost-compressed solver. Compression keeps one
trace per reachable cost multiset, so the retained keys of `solve` are exactly
the keys of the full enumeration. When every menu offers exactly two distinct
tags, a key is determined by how often the second tag occurs: `L` menus give
`L + 1` terminal states and `L (L + 1)` transitions. The band processing order
plays no role. -/
noncomputable section
open scoped Classical
namespace ThresholdHC.BandCostExample
open ThresholdHC.BandCostSelection

variable {α κ : Type*}

/-- Compression keeps every reachable key. -/
theorem compress_image_key [DecidableEq κ] (key : α → κ) (saved : α → ℝ) (F : Finset α) :
    (compress key saved F).image key = F.image key := by
  ext k
  constructor
  · intro hk
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hk
    exact Finset.mem_image_of_mem key (compress_subset key saved F hx)
  · intro hk
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hk
    obtain ⟨y, hy, hkey, -⟩ := compress_dominates key saved F hx
    exact Finset.mem_image.mpr ⟨y, hy, hkey⟩

theorem mem_extend_image (tag : α → κ) (F : Finset (List α)) (menu : Finset α)
    (m : Multiset κ) :
    m ∈ (extend F menu).image (traceKey tag) ↔
      ∃ k ∈ F.image (traceKey tag), ∃ x ∈ menu, tag x ::ₘ k = m := by
  constructor
  · intro h
    obtain ⟨ys, hys, rfl⟩ := Finset.mem_image.mp h
    obtain ⟨xs, hxs, x, hx, rfl⟩ := mem_extend.mp hys
    exact ⟨traceKey tag xs, Finset.mem_image_of_mem _ hxs, x, hx, rfl⟩
  · rintro ⟨k, hk, x, hx, rfl⟩
    obtain ⟨xs, hxs, rfl⟩ := Finset.mem_image.mp hk
    exact Finset.mem_image.mpr ⟨x :: xs, mem_extend.mpr ⟨xs, hxs, x, hx, rfl⟩, rfl⟩

theorem extend_image_congr (tag : α → κ) {F G : Finset (List α)} (menu : Finset α)
    (h : F.image (traceKey tag) = G.image (traceKey tag)) :
    (extend F menu).image (traceKey tag) = (extend G menu).image (traceKey tag) := by
  ext m
  rw [mem_extend_image, mem_extend_image, h]

/-- The retained keys of the compressed solver are all keys of the enumeration. -/
theorem solve_image_key (tag : α → κ) (saving : α → ℝ) (ms : List (Finset α)) :
    (solve tag saving ms).image (traceKey tag) = (enumerate ms).image (traceKey tag) := by
  induction ms with
  | nil => rfl
  | cons menu rest ih =>
    change (compress (traceKey tag) (traceSaved saving)
      (extend (solve tag saving rest) menu)).image (traceKey tag) =
        (extend (enumerate rest) menu).image (traceKey tag)
    rw [compress_image_key]
    exact extend_image_congr tag menu ih

/-- The number of terminal states is the number of reachable cost multisets. -/
theorem solve_card_eq (tag : α → κ) (saving : α → ℝ) (ms : List (Finset α)) :
    (solve tag saving ms).card = ((enumerate ms).image (traceKey tag)).card := by
  rw [← solve_image_key, Finset.card_image_of_injOn (solve_key_injective tag saving ms)]

/-- When every menu realizes exactly the tags satisfying `P`, the reachable keys
are the multisets of length `L` with all elements satisfying `P`. -/
theorem mem_key_image_iff (tag : α → κ) (P : κ → Prop) (ms : List (Finset α))
    (hT : ∀ M ∈ ms, ∀ y, (∃ x ∈ M, tag x = y) ↔ P y) :
    ∀ m : Multiset κ, m ∈ (enumerate ms).image (traceKey tag) ↔
      Multiset.card m = ms.length ∧ ∀ x ∈ m, P x := by
  induction ms with
  | nil =>
    intro m
    change m ∈ ({[]} : Finset (List α)).image (traceKey tag) ↔ _
    rw [Finset.image_singleton, Finset.mem_singleton]
    constructor
    · rintro rfl
      exact ⟨rfl, fun x hx => absurd hx (Multiset.notMem_zero x)⟩
    · rintro ⟨hc, -⟩
      exact Multiset.card_eq_zero.mp hc
  | cons M rest ih =>
    intro m
    have hM := hT M List.mem_cons_self
    have hrest : ∀ N ∈ rest, ∀ y, (∃ x ∈ N, tag x = y) ↔ P y :=
      fun N hN => hT N (List.mem_cons_of_mem _ hN)
    change m ∈ (extend (enumerate rest) M).image (traceKey tag) ↔ _
    rw [mem_extend_image]
    constructor
    · rintro ⟨k, hk, x, hx, rfl⟩
      obtain ⟨hc, hmem⟩ := (ih hrest k).mp hk
      refine ⟨by simp [hc], ?_⟩
      intro y hy
      rcases Multiset.mem_cons.mp hy with h | h
      · rw [h]
        exact (hM (tag x)).mp ⟨x, hx, rfl⟩
      · exact hmem y h
    · rintro ⟨hc, hmem⟩
      have hpos : 0 < Multiset.card m := by
        rw [hc]
        simp
      obtain ⟨y, hy⟩ := Multiset.card_pos_iff_exists_mem.mp hpos
      obtain ⟨x, hx, hxy⟩ := (hM y).mpr (hmem y hy)
      refine ⟨m.erase y, (ih hrest _).mpr ⟨?_, fun z hz => hmem z (Multiset.mem_of_mem_erase hz)⟩,
        x, hx, ?_⟩
      · rw [Multiset.card_erase_of_mem hy, hc]
        simp
      · rw [hxy]
        exact Multiset.cons_erase hy

theorem count_add_count {p q : κ} (hpq : p ≠ q) (m : Multiset κ)
    (hm : ∀ x ∈ m, x = p ∨ x = q) :
    Multiset.count p m + Multiset.count q m = Multiset.card m := by
  induction m using Multiset.induction_on with
  | empty => simp
  | cons a m ih =>
    have ih' := ih (fun x hx => hm x (Multiset.mem_cons_of_mem hx))
    rcases hm a (Multiset.mem_cons_self a m) with h | h
    · rw [h]
      simp only [Multiset.count_cons_self, Multiset.card_cons,
        Multiset.count_cons_of_ne hpq.symm]
      omega
    · rw [h]
      simp only [Multiset.count_cons_self, Multiset.card_cons,
        Multiset.count_cons_of_ne hpq]
      omega

/-- Length-`L` multisets over two distinct tags number exactly `L + 1`. -/
theorem card_two_tags {p q : κ} (hpq : p ≠ q) (L : ℕ) (I : Finset (Multiset κ))
    (hI : ∀ m, m ∈ I ↔ Multiset.card m = L ∧ ∀ x ∈ m, x = p ∨ x = q) :
    I.card = L + 1 := by
  have hinj : Set.InjOn (Multiset.count q) (I : Set (Multiset κ)) := by
    intro m1 h1 m2 h2 he
    have h1' := (hI m1).mp h1
    have h2' := (hI m2).mp h2
    have c1 := count_add_count hpq m1 h1'.2
    have c2 := count_add_count hpq m2 h2'.2
    have he' : Multiset.count q m1 = Multiset.count q m2 := he
    ext a
    by_cases haq : a = q
    · rw [haq]
      exact he'
    by_cases hap : a = p
    · rw [hap]
      omega
    · rw [Multiset.count_eq_zero.mpr, Multiset.count_eq_zero.mpr]
      · intro h
        rcases h2'.2 a h with h | h
        · exact hap h
        · exact haq h
      · intro h
        rcases h1'.2 a h with h | h
        · exact hap h
        · exact haq h
  have himage : I.image (Multiset.count q) = Finset.range (L+1) := by
    ext k
    rw [Finset.mem_image, Finset.mem_range]
    constructor
    · rintro ⟨m, hm, rfl⟩
      have h := Multiset.count_le_card q m
      rw [((hI m).mp hm).1] at h
      omega
    · intro hk
      refine ⟨Multiset.replicate k q + Multiset.replicate (L - k) p, (hI _).mpr ⟨?_, ?_⟩, ?_⟩
      · simp only [Multiset.card_add, Multiset.card_replicate]
        omega
      · intro x hx
        rcases Multiset.mem_add.mp hx with h | h
        · exact Or.inr (Multiset.eq_of_mem_replicate h)
        · exact Or.inl (Multiset.eq_of_mem_replicate h)
      · rw [Multiset.count_add, Multiset.count_replicate_self, Multiset.count_replicate,
          ite_eq_right hpq]
        simp
  rw [← Finset.card_image_of_injOn hinj, himage, Finset.card_range]

/-- Two distinct tags per menu: `L` menus leave `L + 1` terminal states. -/
theorem two_tag_solve_card (tag : α → κ) (saving : α → ℝ) {p q : κ} (hpq : p ≠ q)
    (ms : List (Finset α)) (hT : ∀ M ∈ ms, ∀ y, (∃ x ∈ M, tag x = y) ↔ (y = p ∨ y = q)) :
    (solve tag saving ms).card = ms.length + 1 := by
  rw [solve_card_eq]
  exact card_two_tags hpq _ _ (mem_key_image_iff tag (fun y => y = p ∨ y = q) ms hT)

/-- Two-option menus with two distinct tags: `L` menus take `L (L + 1)` transitions. -/
theorem two_tag_transitions (tag : α → κ) (saving : α → ℝ) {p q : κ} (hpq : p ≠ q)
    (ms : List (Finset α)) (hT : ∀ M ∈ ms, ∀ y, (∃ x ∈ M, tag x = y) ↔ (y = p ∨ y = q))
    (h2 : ∀ M ∈ ms, M.card = 2) :
    transitionCount tag saving ms = ms.length * (ms.length + 1) := by
  induction ms with
  | nil => rfl
  | cons M rest ih =>
    have hrest : ∀ N ∈ rest, ∀ y, (∃ x ∈ N, tag x = y) ↔ (y = p ∨ y = q) :=
      fun N hN => hT N (List.mem_cons_of_mem _ hN)
    have hrest2 : ∀ N ∈ rest, N.card = 2 := fun N hN => h2 N (List.mem_cons_of_mem _ hN)
    change (solve tag saving rest).card * M.card + transitionCount tag saving rest = _
    rw [two_tag_solve_card tag saving hpq rest hrest, h2 M List.mem_cons_self, ih hrest hrest2]
    simp only [List.length_cons]
    ring

end ThresholdHC.BandCostExample
