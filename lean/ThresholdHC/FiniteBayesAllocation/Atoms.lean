import ThresholdHC.FiniteBayesAllocation.Risk

/-! Evaluation at a finite atomic gap law. A case is valid for a code when the
code's integers encode the masses, the sign-law values and the heads
probabilities. Then the weight of a full ordered word under the sign law `k`
is `wordNat C k (countsOf p u) / (den 32^8)^8`, and the target of sign law `k`
is `tt k / 16`. Both locked cases are valid for their codes. -/

noncomputable section
namespace ThresholdHC.FiniteBayesAllocation
open MeasureTheory
open ThresholdHC ThresholdHC.Tier6 ThresholdHC.FiniteLawCertificates ThresholdHC.CriticalEntropy
open ThresholdHC.HardBudget

/-- The integer code `C` encodes the atomic case `(d, m, v)`. -/
structure CaseValid {J K : ℕ} (d : Fin J → Gap) (m : Fin J → ℚ) (v : Fin K → Fin J → ℚ)
    (C : Code J K) : Prop where
  mass : ∀ j, 0 ≤ m j
  inj : Function.Injective d
  val : ∀ k j, 0 ≤ v k j ∧ v k j ≤ 1
  up : ∀ j, 1/2 + (d j : ℝ) = (C.up j : ℝ) / 32
  dn : ∀ j, 1/2 - (d j : ℝ) = (C.dn j : ℝ) / 32
  den : 0 < C.den
  pos : ∀ k j, (m j : ℝ) * (v k j : ℝ) = (C.pos k j : ℝ) / C.den
  neg : ∀ k j, (m j : ℝ) * (1 - (v k j : ℝ)) = (C.neg k j : ℝ) / C.den
  mean : ∀ k, ∑ j, (m j : ℝ) * (v k j : ℝ) = (C.tt k : ℝ) / 16

theorem atomSign_at {J : ℕ} (d : Fin J → Gap) (v : Fin J → ℚ) (hd : Function.Injective d)
    (j : Fin J) (hv : 0 ≤ v j ∧ v j ≤ 1) : (atomSign d v).val (d j) = v j := by
  have hs : ∑ j', ({d j'} : Set Gap).indicator (fun _ => (v j' : ℝ)) (d j) = v j := by
    rw [Finset.sum_eq_single j]
    · simp
    · intro b _ hb
      rw [Set.indicator_of_notMem]
      simp only [Set.mem_singleton_iff]
      exact fun h => hb (hd h).symm
    · simp
  change max 0 (min 1 (∑ j', ({d j'} : Set Gap).indicator (fun _ => (v j' : ℝ)) (d j))) = _
  have h1 : (v j : ℝ) ≤ 1 := by exact_mod_cast hv.2
  have h0 : (0 : ℝ) ≤ v j := by exact_mod_cast hv.1
  rw [hs, min_eq_right h1, max_eq_right h0]

theorem atom_mean {J K : ℕ} {d : Fin J → Gap} {m : Fin J → ℚ} {v : Fin K → Fin J → ℚ}
    {C : Code J K} (hc : CaseValid d m v C) (k : Fin K) :
    signMean (atomicMeasure d m) (atomSign d (v k)).val = (C.tt k : ℝ) / 16 := by
  rw [signMean, integral_atomic d m hc.mass]
  simp_rw [atomSign_at d (v k) hc.inj _ (hc.val k _)]
  exact hc.mean k

private theorem term_eq (P N U D : ℝ) (den : ℝ) (h : 0 < den) (a b : ℕ) :
    P / den * ((U / 32) ^ a * (D / 32) ^ b) + N / den * ((D / 32) ^ a * (U / 32) ^ b) =
      (P * U ^ a * D ^ b + N * D ^ a * U ^ b) / (den * 32 ^ (a + b)) := by
  rw [div_pow, div_pow, div_pow, div_pow, pow_add]
  field_simp

theorem localNat_cast {J K : ℕ} (C : Code J K) (k : Fin K) (a b : ℕ) (hab : a + b ≤ 8)
    (hden : 0 < C.den) :
    (localNat C k (a, b) : ℝ) / ((C.den : ℝ) * 32 ^ 8) =
      (∑ j, ((C.pos k j : ℝ) * (C.up j : ℝ) ^ a * (C.dn j : ℝ) ^ b +
        (C.neg k j : ℝ) * (C.dn j : ℝ) ^ a * (C.up j : ℝ) ^ b)) / ((C.den : ℝ) * 32 ^ (a + b)) := by
  have hd : (0 : ℝ) < C.den := by exact_mod_cast hden
  have h32 : (32 : ℝ) ^ 8 = 32 ^ (8 - (a + b)) * 32 ^ (a + b) := by
    rw [← pow_add, Nat.sub_add_cancel hab]
  unfold localNat
  push_cast [List.sum_ofFn]
  rw [h32]
  field_simp

/-- Weight of a full ordered word of an `8`-flip policy at a valid atomic case. -/
theorem word_weight {J K : ℕ} {d : Fin J → Gap} {m : Fin J → ℚ} {v : Fin K → Fin J → ℚ}
    {C : Code J K} (hc : CaseValid d m v C) [IsProbabilityMeasure (atomicMeasure d m)]
    (p : List Bool → ℕ) (k : Fin K) (u : Fin 8 → Bool) (hp : ∀ t, flipLabel p u t < 8) :
    creationPopulationWeight (atomicMeasure d m) (stopAt 8 p) gapReal (atomSign d (v k)).val
        (fun t => some (u t)) =
      (wordNat C k (countsOf p (List.ofFn u)) : ℝ) / ((C.den : ℝ) * 32 ^ 8) ^ 8 := by
  have hd : (0 : ℝ) < C.den := by exact_mod_cast hc.den
  rw [stopAt_full_weight _ p gapReal _ measurable_subtype_coe (atomSign d (v k)).property.1 8 u hp]
  have hw : wordNat C k (countsOf p (List.ofFn u)) =
      ∏ l ∈ Finset.range 8, localNat C k (headCount (zipped p u) l, tailCount (zipped p u) l) := by
    unfold wordNat countsOf
    rw [List.map_ofFn, List.prod_ofFn]
    exact Fin.prod_univ_eq_prod_range
      (fun l => localNat C k (headCount (zipped p u) l, tailCount (zipped p u) l)) 8
  have hdiv : ∏ l ∈ Finset.range 8,
      (localNat C k (headCount (zipped p u) l, tailCount (zipped p u) l) : ℝ) / ((C.den : ℝ) * 32 ^ 8) =
      (∏ l ∈ Finset.range 8, (localNat C k (headCount (zipped p u) l, tailCount (zipped p u) l) : ℝ)) /
        ((C.den : ℝ) * 32 ^ 8) ^ 8 := by
    rw [Finset.prod_div_distrib, Finset.prod_const, Finset.card_range]
  rw [hw, Nat.cast_prod, ← hdiv]
  apply Finset.prod_congr rfl
  intro l _
  have hle : headCount (zipped p u) l + tailCount (zipped p u) l ≤ 8 :=
    (count_add_le _ l).trans (zipped_length p u).le
  rw [localNat_cast C k _ _ hle hc.den, integral_atomic d m hc.mass, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro j _
  simp only [gapReal, atomSign_at d (v k) hc.inj j (hc.val k j), labelRun_eq]
  have e1 : 1 - (1/2 + (d j : ℝ)) = (C.dn j : ℝ) / 32 := by rw [← hc.dn j]; ring
  have e2 : 1 - (1/2 - (d j : ℝ)) = (C.up j : ℝ) / 32 := by rw [← hc.up j]; ring
  rw [e1, e2, hc.up j, hc.dn j, ← term_eq _ _ _ _ _ hd, ← hc.pos k j, ← hc.neg k j]
  ring

/-- Every label of an ordered word read from a table of labels below `8` is below `8`. -/
theorem tableLabel_lt (T : List ℕ) (hT : T.all (fun x => decide (x < 8)) = true) (xs : List Bool) :
    tableLabel T xs < 8 := by
  unfold tableLabel
  rw [List.all_eq_true] at hT
  rw [List.getD_eq_getElem?_getD]
  cases h : T[xs.foldl (fun a b => 2 * a + b.toNat) 1]? with
  | none => simp
  | some x =>
    simp only [Option.getD_some]
    exact of_decide_eq_true (hT x (List.mem_of_getElem? h))

theorem fresh_label_lt (u : Fin 8 → Bool) (t : Fin 8) : flipLabel (fun xs => xs.length) u t < 8 := by
  simp [flipLabel]

theorem single_label_lt (u : Fin 8 → Bool) (t : Fin 8) : flipLabel (fun _ => 0) u t < 8 := by
  simp [flipLabel]

/-- The two-scales sign-law values at the atoms, in `FINITE_LOCK.json` order. -/
def twoV : Fin 6 → Fin 2 → ℚ := ![![0, 0], ![1/2, 0], ![1, 0], ![0, 1/14], ![0, 1/7], ![1/8, 1/8]]

/-- The three-scales sign-law values at the atoms, in `FINITE_LOCK.json` order. -/
def threeV : Fin 7 → Fin 3 → ℚ :=
  ![![0, 0, 0], ![1, 0, 0], ![0, 1/3, 0], ![0, 2/3, 0], ![0, 0, 1/12], ![0, 0, 1/6],
    ![1/8, 1/8, 1/8]]

theorem twoScalesSign_eq (k : Fin 6) : twoScalesSign k = atomSign ![gap32, gap4] (twoV k) := rfl

theorem threeScalesSign_eq (k : Fin 7) :
    threeScalesSign k = atomSign ![gap32, gap8, gap2] (threeV k) := rfl

theorem twoValid : CaseValid ![gap32, gap4] ![1/8, 7/8] twoV twoCode where
  mass := by intro j; fin_cases j <;> norm_num
  inj := by
    intro i j h
    have h' := congrArg Subtype.val h
    fin_cases i <;> fin_cases j <;> first | rfl | (norm_num [gap32, gap4] at h')
  val := by intro k j; fin_cases k <;> fin_cases j <;> norm_num [twoV]
  up := by intro j; fin_cases j <;> norm_num [gap32, gap4, twoCode]
  dn := by intro j; fin_cases j <;> norm_num [gap32, gap4, twoCode]
  den := by norm_num [twoCode]
  pos := by intro k j; fin_cases k <;> fin_cases j <;> norm_num [twoV, twoCode]
  neg := by intro k j; fin_cases k <;> fin_cases j <;> norm_num [twoV, twoCode]
  mean := by intro k; fin_cases k <;> norm_num [Fin.sum_univ_succ, twoV, twoCode]

theorem threeValid : CaseValid ![gap32, gap8, gap2] ![1/16, 3/16, 3/4] threeV threeCode where
  mass := by intro j; fin_cases j <;> norm_num
  inj := by
    intro i j h
    have h' := congrArg Subtype.val h
    fin_cases i <;> fin_cases j <;> first | rfl | (norm_num [gap32, gap8, gap2] at h')
  val := by intro k j; fin_cases k <;> fin_cases j <;> norm_num [threeV]
  up := by intro j; fin_cases j <;> norm_num [gap32, gap8, gap2, threeCode]
  dn := by intro j; fin_cases j <;> norm_num [gap32, gap8, gap2, threeCode]
  den := by norm_num [threeCode]
  pos := by intro k j; fin_cases k <;> fin_cases j <;> norm_num [threeV, threeCode]
  neg := by intro k j; fin_cases k <;> fin_cases j <;> norm_num [threeV, threeCode]
  mean := by intro k; fin_cases k <;> norm_num [Fin.sum_univ_succ, threeV, threeCode]

end ThresholdHC.FiniteBayesAllocation
