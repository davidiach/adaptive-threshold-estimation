import ThresholdHC.CriticalEntropy.CreationPopulation
import ThresholdHC.FiniteBayesAllocation.Kernel

/-! Observable prefix weights of a deterministic `stopAt n p` policy after
integrating the iid hidden magnitudes and signs, for an arbitrary magnitude
law. A word with a missing observation has weight `0`; a full word has the
product, over the labels, of the integrated likelihood of that label's flips.
The flip likelihood of one label is a power of the heads probability times a
power of the tails probability, with the exponents counted along the zipped
label and outcome lists. -/

noncomputable section
namespace ThresholdHC.FiniteBayesAllocation
open MeasureTheory
open ThresholdHC ThresholdHC.Proofs ThresholdHC.Tier5 ThresholdHC.CriticalEntropy ThresholdHC.HardBudget

theorem histBefore_length_le {n : ℕ} (w : Fin n → Option Bool) (t : Fin n) :
    (histBefore w t).length ≤ t := by
  unfold histBefore
  exact (List.length_filterMap_le _ _).trans (by simp)

theorem histBefore_full {n : ℕ} (u : Fin n → Bool) (t : Fin n) :
    histBefore (fun i => some (u i)) t = (List.ofFn u).take t := by
  unfold histBefore
  have h : (List.ofFn fun j : Fin t.val => (fun i => some (u i)) (Fin.castLE t.isLt.le j)) =
      (List.ofFn fun j : Fin t.val => u (Fin.castLE t.isLt.le j)).map some := by
    rw [List.map_ofFn]; rfl
  rw [h, List.filterMap_map]
  simp only [Function.comp_def, id, List.filterMap_some]
  apply List.ext_getElem
  · simp
  · intro i hi hj
    simp

/-- Label of flip `t` of the ordered word `u`. -/
def flipLabel {n : ℕ} (p : List Bool → ℕ) (u : Fin n → Bool) (t : Fin n) : ℕ :=
  p ((List.ofFn u).take t)

/-- Likelihood of the flips of label `l` when a head has probability `a`. -/
def labelRun {n : ℕ} (p : List Bool → ℕ) (u : Fin n → Bool) (l : ℕ) (a : ℝ) : ℝ :=
  ∏ t, if flipLabel p u t = l then (if u t then a else 1 - a) else 1

theorem stopAt_some {n : ℕ} (p : List Bool → ℕ) (w : Fin n → Option Bool) (t : Fin n) :
    stopAt n p (histBefore w t) = some (p (histBefore w t)) := by
  simp [stopAt, (histBefore_length_le w t).trans_lt t.isLt]

theorem cap_stopAt {n : ℕ} (p : List Bool → ℕ) (w : Fin n → Option Bool) (t : Fin n) :
    capPolicy (coinCap n (stopAt n p)) (stopAt n p) (histBefore w t) =
      some ⟨p (histBefore w t), selected_lt_coinCap (stopAt n p) w t _ (stopAt_some p w t)⟩ := by
  simp [capPolicy, stopAt_some p w t, selected_lt_coinCap (stopAt n p) w t _ (stopAt_some p w t)]

/-- A word with a missing observation has weight `0` under `stopAt n p`. -/
theorem stopAt_partial_weight {D : Type} [MeasurableSpace D] (μ : Measure D) [IsProbabilityMeasure μ]
    {n : ℕ} (p : List Bool → ℕ) (d q : D → ℝ) (hd : Measurable d) (hq : Measurable q)
    (w : Fin n → Option Bool) (t₀ : Fin n) (h₀ : w t₀ = none) :
    creationPopulationWeight μ (stopAt n p) d q w = 0 := by
  rw [creationPopulationWeight_eq_finite μ _ d q hd hq w, finite_population_factor]
  apply mul_eq_zero_of_right
  let i₀ : Fin (coinCap n (stopAt n p)) :=
    ⟨p (histBefore w t₀), selected_lt_coinCap (stopAt n p) w t₀ _ (stopAt_some p w t₀)⟩
  apply Finset.prod_eq_zero (Finset.mem_univ i₀)
  have hc (a : ℝ) : coinLike (capPolicy (coinCap n (stopAt n p)) (stopAt n p)) w i₀ a = 0 := by
    unfold coinLike
    apply Finset.prod_eq_zero (Finset.mem_univ t₀)
    rw [cap_stopAt, ite_eq_left rfl, h₀]
    rfl
  simp [hc]

theorem prod_reindex {m N : ℕ} (G : ℕ → ℝ) (S : Finset ℕ) (hm : S ⊆ Finset.range m)
    (hN : S ⊆ Finset.range N) (h1 : ∀ l ∉ S, G l = 1) :
    ∏ i : Fin m, G i.val = ∏ l ∈ Finset.range N, G l := by
  rw [Fin.prod_univ_eq_prod_range, ← Finset.prod_subset hm (fun x _ hx => h1 x hx),
    Finset.prod_subset hN (fun x _ hx => h1 x hx)]

/-- A full word of `stopAt n p` has the product over the labels `l < N` of the
integrated label likelihoods, when every queried label is below `N`. -/
theorem stopAt_full_weight {D : Type} [MeasurableSpace D] (μ : Measure D) [IsProbabilityMeasure μ]
    {n : ℕ} (p : List Bool → ℕ) (d q : D → ℝ) (hd : Measurable d) (hq : Measurable q)
    (N : ℕ) (u : Fin n → Bool) (hN : ∀ t, flipLabel p u t < N) :
    creationPopulationWeight μ (stopAt n p) d q (fun t => some (u t)) =
      ∏ l ∈ Finset.range N, ∫ x, q x * labelRun p u l (1/2 + d x) +
        (1 - q x) * labelRun p u l (1/2 - d x) ∂μ := by
  rw [creationPopulationWeight_eq_finite μ _ d q hd hq _, finite_population_factor]
  set m := coinCap n (stopAt n p)
  set P := capPolicy m (stopAt n p)
  have hlt (t : Fin n) : flipLabel p u t < m := by
    have := selected_lt_coinCap (stopAt n p) (fun t => some (u t)) t _ (stopAt_some p _ t)
    rwa [histBefore_full] at this
  have hP (t : Fin n) : P (histBefore (fun t => some (u t)) t) = some ⟨flipLabel p u t, hlt t⟩ := by
    rw [histBefore_full]
    have hl : ((List.ofFn u).take t).length < n := by simp
    simp only [P, capPolicy, stopAt, ite_eq_left hl, Option.bind_some]
    exact dite_eq_left (hlt t)
  have hval : pathValidity P (fun t => some (u t)) = 1 := by
    unfold pathValidity
    apply Finset.prod_eq_one
    intro t _
    rw [hP t]
    simp
  have hlike (i : Fin m) (a : ℝ) : coinLike P (fun t => some (u t)) i a = labelRun p u i.val a := by
    unfold coinLike labelRun
    apply Finset.prod_congr rfl
    intro t _
    rw [hP t]
    have he : ((some ⟨flipLabel p u t, hlt t⟩ : Option (Fin m)) = some i) ↔ flipLabel p u t = i.val := by
      rw [Option.some.injEq, Fin.ext_iff]
    by_cases h : flipLabel p u t = i.val
    · rw [ite_eq_left (he.mpr h), ite_eq_left h]
      show obsProb a (some (u t)) = _
      cases u t <;> rfl
    · rw [ite_eq_right (fun e => h (he.mp e)), ite_eq_right h]
  rw [hval, one_mul]
  simp_rw [hlike]
  let G : ℕ → ℝ := fun l => ∫ x, q x * labelRun p u l (1/2 + d x) +
    (1 - q x) * labelRun p u l (1/2 - d x) ∂μ
  change ∏ i : Fin m, G i.val = ∏ l ∈ Finset.range N, G l
  apply prod_reindex G (Finset.univ.image (flipLabel p u))
  · intro l hl
    obtain ⟨t, _, rfl⟩ := Finset.mem_image.mp hl
    exact Finset.mem_range.mpr (hlt t)
  · intro l hl
    obtain ⟨t, _, rfl⟩ := Finset.mem_image.mp hl
    exact Finset.mem_range.mpr (hN t)
  · intro l hl
    have hr (a : ℝ) : labelRun p u l a = 1 := by
      unfold labelRun
      apply Finset.prod_eq_one
      intro t _
      have : flipLabel p u t ≠ l := fun e => hl (Finset.mem_image.mpr ⟨t, Finset.mem_univ _, e⟩)
      rw [ite_eq_right this]
    simp only [G, hr]
    simp

theorem prod_zip_ofFn {M α β : Type*} [CommMonoid M] {n : ℕ} (a : Fin n → α) (b : Fin n → β)
    (f : α × β → M) :
    ∏ t, f (a t, b t) = (((List.ofFn a).zip (List.ofFn b)).map f).prod := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Fin.prod_univ_succ, List.ofFn_succ, List.ofFn_succ, List.zip_cons_cons, List.map_cons,
      List.prod_cons, ih (fun i => a i.succ) (fun i => b i.succ)]

theorem prod_map_label (L : List (ℕ × Bool)) (l : ℕ) (x y : ℝ) :
    (L.map fun lb => if lb.1 = l then (if lb.2 then x else y) else 1).prod =
      x ^ headCount L l * y ^ tailCount L l := by
  induction L with
  | nil => simp [headCount, tailCount]
  | cons lb L ih =>
    obtain ⟨l', b⟩ := lb
    simp only [List.map_cons, List.prod_cons, ih, headCount, tailCount, List.countP_cons]
    by_cases h : l' = l <;> cases b <;> simp [h, pow_succ] <;> ring

theorem count_add_le (L : List (ℕ × Bool)) (l : ℕ) : headCount L l + tailCount L l ≤ L.length := by
  induction L with
  | nil => simp [headCount, tailCount]
  | cons lb L ih =>
    obtain ⟨l', b⟩ := lb
    simp only [headCount, tailCount, List.countP_cons, List.length_cons] at ih ⊢
    by_cases h : l' = l <;> cases b <;> simp [h] <;> omega

/-- The label and outcome pairs of an ordered word. -/
def zipped {n : ℕ} (p : List Bool → ℕ) (u : Fin n → Bool) : List (ℕ × Bool) :=
  (labelsOf n p (List.ofFn u)).zip (List.ofFn u)

theorem zipped_length {n : ℕ} (p : List Bool → ℕ) (u : Fin n → Bool) : (zipped p u).length = n := by
  simp [zipped, labelsOf]

theorem labelRun_eq {n : ℕ} (p : List Bool → ℕ) (u : Fin n → Bool) (l : ℕ) (a : ℝ) :
    labelRun p u l a = a ^ headCount (zipped p u) l * (1 - a) ^ tailCount (zipped p u) l := by
  unfold labelRun
  rw [← prod_map_label]
  rw [prod_zip_ofFn (flipLabel p u) u (fun lb : ℕ × Bool =>
    if lb.1 = l then (if lb.2 then a else 1 - a) else 1)]
  rfl

end ThresholdHC.FiniteBayesAllocation
