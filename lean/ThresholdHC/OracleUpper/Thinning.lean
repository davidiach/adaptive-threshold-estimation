import ThresholdHC.OracleUpper.FreshOracle
import ThresholdHC.OracleUpper.SeedMoments

/-! The thinning estimators for both magnitude oracles. A seed holds
independent uniforms and an iid magnitude array. Among the first m indices,
index i is selected when its uniform is at most an acceptance probability at
its magnitude. The estimator buys one flip from a fresh coin at each selected
magnitude, in increasing index order, and returns an affine function of the
signed flips. In the revealed oracle the coins are the revealed array entries
at the selected indices. In the selected oracle each selected magnitude is
requested as a new coin. Both have the product transcript law of
`freshProduct` at every seed, so their squared risk and work reduce to the
seed integrals of `SeedMoments`. -/
noncomputable section
namespace ThresholdHC.OracleUpper
open MeasureTheory
open scoped ENNReal
open ThresholdHC ThresholdHC.Tier3 ThresholdHC.Tier5 ThresholdHC.Tier6 ThresholdHC.OracleLower

/-- Selection code of the first m indices of a seed. -/
def selCode (p : Gap → ℝ) (m : ℕ) (u : ThinSeed) : Fin m → Bool :=
  fun i => decide ((u.1 i : ℝ) ≤ p (u.2 i))

/-- The selected indices in increasing order. -/
def codeList (m : ℕ) (c : Fin m → Bool) : List ℕ :=
  (List.range m).filter (fun i => if h : i < m then c ⟨i, h⟩ else false)

/-- Number of selected indices: the stopping length. -/
def codeStop (m : ℕ) (c : Fin m → Bool) : ℕ := (codeList m c).length

/-- The k-th selected index. -/
def codeIndex (m : ℕ) (c : Fin m → Bool) (k : ℕ) : ℕ := (codeList m c).getD k 0

/-- Flip the coin at the k-th selected index at history length k, and stop
after the last selected index. -/
def codePolicy (m : ℕ) (c : Fin m → Bool) (xs : List Bool) : Option ℕ :=
  if xs.length < codeStop m c then some (codeIndex m c xs.length) else none

/-- Request a new coin while selected indices remain. -/
def codeRequest (m : ℕ) (c : Fin m → Bool) (xs : List Bool) : Option (Option ℕ) :=
  if xs.length < codeStop m c then some none else none

/-- Affine output in the signed flips of the first m observations. -/
def thinOutput (m : ℕ) (c β : ℝ) {S : Type} (z : S × ProcessTape) : ℝ :=
  c + β * ∑ k : Fin m, flipValue (z.2 k)

theorem measurable_selCode (p : Gap → ℝ) (hp : Measurable p) (m : ℕ) :
    Measurable (selCode p m) := by
  apply Measurable.of_eval
  intro i
  apply measurable_to_bool
  have he : (fun u : ThinSeed => selCode p m u i) ⁻¹' {true} =
      {u : ThinSeed | (u.1 i : ℝ) ≤ p (u.2 i)} := by
    ext u
    simp [selCode]
  rw [he]
  exact measurableSet_le
    (measurable_subtype_coe.comp ((measurable_pi_apply i.val).comp measurable_fst))
    (hp.comp ((measurable_pi_apply i.val).comp measurable_snd))

theorem measurable_thinOutput (m : ℕ) (c β : ℝ) {S : Type} [MeasurableSpace S] :
    Measurable (thinOutput m c β (S := S)) :=
  measurable_const.add (measurable_const.mul (Finset.measurable_sum _ fun k _ =>
    (measurable_of_countable flipValue).comp ((measurable_pi_apply k.val).comp measurable_snd)))

theorem codeStop_le (m : ℕ) (c : Fin m → Bool) : codeStop m c ≤ m := by
  unfold codeStop codeList
  exact (List.length_filter_le _ _).trans (List.length_range).le

theorem codeIndex_inj (m : ℕ) (c : Fin m → Bool) {k l : ℕ} (hk : k < codeStop m c)
    (hl : l < codeStop m c) (h : codeIndex m c k = codeIndex m c l) : k = l := by
  unfold codeIndex at h
  unfold codeStop at hk hl
  rw [List.getD_eq_getElem _ _ hk, List.getD_eq_getElem _ _ hl] at h
  exact ((List.nodup_range.filter _).getElem_inj_iff).mp h

private theorem list_index_sum (L : List ℕ) (F : ℕ → ℝ) :
    ∑ k ∈ Finset.range L.length, F (L.getD k 0) = (L.map F).sum := by
  induction L with
  | nil => simp
  | cons a L ih =>
    rw [List.length_cons, Finset.sum_range_succ']
    simp only [List.getD_cons_succ, List.getD_cons_zero, ih, List.map_cons, List.sum_cons]
    ring

private theorem filter_map_sum (m : ℕ) (P : ℕ → Bool) (F : ℕ → ℝ) :
    (((List.range m).filter P).map F).sum = ∑ i ∈ Finset.range m, if P i then F i else 0 := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [List.range_succ, List.filter_append, List.map_append, List.sum_append, ih,
      Finset.sum_range_succ]
    cases h : P m <;> simp [h]

/-- Sums over the selected indices are thinned sums over the window. -/
theorem selected_sum (p : Gap → ℝ) (m : ℕ) (u : ThinSeed) (F : Gap → ℝ) :
    ∑ k ∈ Finset.range (codeStop m (selCode p m u)), F (u.2 (codeIndex m (selCode p m u) k)) =
      ∑ i ∈ Finset.range m, thinned (p (u.2 i)) (F (u.2 i)) (u.1 i) := by
  unfold codeStop codeIndex
  rw [list_index_sum (codeList m (selCode p m u)) (fun i => F (u.2 i)), codeList, filter_map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  have hi' := Finset.mem_range.mp hi
  simp [hi', selCode, thinned]

/-- The revealed-oracle thinning estimator; its seed is the uniform array. -/
def thinRevealed (p : Gap → ℝ) (hp : Measurable p) (m : ℕ) (c β : ℝ) :
    RevealedEstimator (ℕ → unitInterval) where
  randomLaw := uniformLaw
  probability := inferInstance
  policy := fun u xs => codePolicy m (selCode p m u) xs
  policy_measurable := fun xs a => by
    change MeasurableSet (selCode p m ⁻¹' {c | codePolicy m c xs = a})
    exact (measurable_selCode p hp m) (Set.toFinite _).measurableSet
  output := thinOutput m c β
  output_measurable := measurable_thinOutput m c β

/-- The selected-oracle thinning estimator; its seed holds both arrays. -/
def thinSelected (μ : Measure Gap) [IsProbabilityMeasure μ] (p : Gap → ℝ) (hp : Measurable p)
    (m : ℕ) (c β : ℝ) : SelectedEstimator ThinSeed where
  randomLaw := thinSeedLaw μ
  probability := inferInstance
  request := fun u xs => codeRequest m (selCode p m u) xs
  request_measurable := fun xs =>
    (measurable_of_countable (fun c => codeRequest m c xs)).comp (measurable_selCode p hp m)
  newGap := fun u xs => u.2 (codeIndex m (selCode p m u) xs.length)
  newGap_measurable := fun xs => by
    have hF : Measurable (fun z : ThinSeed × (Fin m → Bool) => z.1.2 (codeIndex m z.2 xs.length)) :=
      measurable_from_prod_countable_left (fun c =>
        (measurable_pi_apply (codeIndex m c xs.length)).comp measurable_snd)
    exact hF.comp (measurable_id.prodMk (measurable_selCode p hp m))
  reuse_valid := by
    intro r xs j h
    simp only [codeRequest] at h
    split at h <;> simp at h
  output := thinOutput m c β
  output_measurable := measurable_thinOutput m c β

/-- Success probability of the flip bought at the k-th selected index. -/
def thinProb (q : SignLaw) (p : Gap → ℝ) (m : ℕ) (u : ThinSeed) (k : ℕ) : ℝ :=
  1/2 + (2 * q.val (u.2 (codeIndex m (selCode p m u) k)) - 1) *
    (u.2 (codeIndex m (selCode p m u) k) : ℝ)

/-- Signed mean of one flip of a fresh coin at gap d. -/
def flipMean (q : SignLaw) (d : Gap) : ℝ := 2 * (2 * q.val d - 1) * d

theorem revealed_law (μ : Measure Gap) [IsProbabilityMeasure μ] (p : Gap → ℝ)
    (hp : Measurable p) (m : ℕ) (c β : ℝ) (q : SignLaw) (u : ThinSeed) (n : ℕ) (w : Prefix n) :
    creationLaw ((revealedOracle μ (thinRevealed p hp m c β)).policy u)
      (fun i => ((revealedOracle μ (thinRevealed p hp m c β)).gap u i : ℝ))
      (fun i => q.val ((revealedOracle μ (thinRevealed p hp m c β)).gap u i)) w =
      freshProduct (codeStop m (selCode p m u)) (thinProb q p m u) w := by
  apply named_product _ _ _ (fun i => ⟨(u.2 i).property.1.le, (u.2 i).property.2⟩)
    (fun i => q.property.2 (u.2 i)) _ (fun xs => codeIndex m (selCode p m u) xs.length)
  · intro xs
    rfl
  · intro x y hx hy h
    exact codeIndex_inj m _ hx hy h
  · intro xs _
    rfl

theorem selected_law (μ : Measure Gap) [IsProbabilityMeasure μ] (p : Gap → ℝ)
    (hp : Measurable p) (m : ℕ) (c β : ℝ) (q : SignLaw) (u : ThinSeed) (n : ℕ) (w : Prefix n) :
    creationLaw ((selectedOracle (thinSelected μ p hp m c β)).policy u)
      (fun i => ((selectedOracle (thinSelected μ p hp m c β)).gap u i : ℝ))
      (fun i => q.val ((selectedOracle (thinSelected μ p hp m c β)).gap u i)) w =
      freshProduct (codeStop m (selCode p m u)) (thinProb q p m u) w := by
  apply named_product _ _ _ (fun i => ⟨(_ : Gap).property.1.le, (_ : Gap).property.2⟩)
    (fun i => q.property.2 _) _ (fun xs => Encodable.encode xs)
  · intro xs
    change selectedLabel xs (codeRequest m (selCode p m u) xs) = _
    unfold codeRequest
    split_ifs <;> rfl
  · intro x y _ _ h
    rw [Encodable.encode_injective h]
  · intro xs _
    change 1/2 + (2 * q.val (u.2 (codeIndex m (selCode p m u)
        ((Encodable.decode (α := List Bool) (Encodable.encode xs)).getD []).length)) - 1) *
        (u.2 (codeIndex m (selCode p m u)
          ((Encodable.decode (α := List Bool) (Encodable.encode xs)).getD []).length) : ℝ) = _
    rw [Encodable.encodek]
    rfl

private theorem flipMean_bound (q : SignLaw) (d : Gap) : |flipMean q d| ≤ 1 := by
  unfold flipMean
  have h1 := q.property.2 d
  have h2 := d.property
  rw [abs_le]
  constructor <;> nlinarith

theorem measurable_flipMean (q : SignLaw) : Measurable (flipMean q) :=
  (measurable_const.mul ((measurable_const.mul q.property.1).sub measurable_const)).mul
    measurable_subtype_coe

private theorem moment_thinned (q : SignLaw) (p : Gap → ℝ) (m : ℕ) (κ β : ℝ) (u : ThinSeed) :
    seedMoment (codeStop m (selCode p m u)) (fun k => 2 * thinProb q p m u k - 1) κ β =
      (κ + β * ∑ i ∈ Finset.range m, thinned (p (u.2 i)) (flipMean q (u.2 i)) (u.1 i))^2 +
        β^2 * ∑ i ∈ Finset.range m,
          thinned (p (u.2 i)) (1 - (flipMean q (u.2 i))^2) (u.1 i) := by
  have he (k : ℕ) : 2 * thinProb q p m u k - 1 =
      flipMean q (u.2 (codeIndex m (selCode p m u) k)) := by
    unfold thinProb flipMean
    ring
  unfold seedMoment
  simp only [he]
  rw [selected_sum p m u (flipMean q), selected_sum p m u (fun d => 1 - (flipMean q d)^2)]

/-- Common value of the squared risk of both thinning estimators. -/
def thinRisk (μ : Measure Gap) (q : SignLaw) (p : Gap → ℝ) (m : ℕ) (c β : ℝ) : ℝ :=
  (c - signMean μ q.val + β * (m * ∫ d, p d * flipMean q d ∂μ))^2 +
    β^2 * (m * (∫ d, p d ∂μ - (∫ d, p d * flipMean q d ∂μ)^2))

private theorem thin_seed_integral (μ : Measure Gap) [IsProbabilityMeasure μ] (q : SignLaw)
    (p : Gap → ℝ) (hp : Measurable p) (hp01 : ∀ d, 0 ≤ p d ∧ p d ≤ 1) (m : ℕ) (c β : ℝ) :
    ∫ u, seedMoment (codeStop m (selCode p m u)) (fun k => 2 * thinProb q p m u k - 1)
      (c - signMean μ q.val) β ∂thinSeedLaw μ = thinRisk μ q p m c β := by
  simp only [moment_thinned]
  exact seed_moment μ p (flipMean q) hp (measurable_flipMean q) hp01 (flipMean_bound q) m _ β

private theorem thin_work_integral (μ : Measure Gap) [IsProbabilityMeasure μ]
    (p : Gap → ℝ) (hp : Measurable p) (hp01 : ∀ d, 0 ≤ p d ∧ p d ≤ 1) (m : ℕ) :
    ∫ u, (codeStop m (selCode p m u) : ℝ) ∂thinSeedLaw μ = m * ∫ d, p d ∂μ := by
  have hc (u : ThinSeed) : (codeStop m (selCode p m u) : ℝ) =
      ∑ i ∈ Finset.range m, thinned (p (u.2 i)) 1 (u.1 i) := by
    rw [← selected_sum p m u (fun _ => 1)]
    simp
  simp only [hc]
  rw [seed_linear μ p (fun _ => 1) hp measurable_const hp01 1 (fun _ => by simp) m]
  simp

private theorem measurable_codeStop (p : Gap → ℝ) (hp : Measurable p) (m : ℕ) :
    Measurable (fun u => codeStop m (selCode p m u)) :=
  (measurable_of_countable (codeStop m)).comp (measurable_selCode p hp m)

theorem revealed_risk (μ : Measure Gap) [IsProbabilityMeasure μ] (p : Gap → ℝ)
    (hp : Measurable p) (hp01 : ∀ d, 0 ≤ p d ∧ p d ≤ 1) (m : ℕ) (c β : ℝ) (q : SignLaw) :
    squaredRisk (oracleLaw (revealedOracle μ (thinRevealed p hp m c β)) q)
      (revealedOracle μ (thinRevealed p hp m c β)).output (signMean μ q.val) =
      ENNReal.ofReal (thinRisk μ q p m c β) := by
  rw [oracle_squared_risk _ q (fun u => codeStop m (selCode p m u)) (thinProb q p m) m c β _
    (fun u => codeStop_le m _) (revealed_law μ p hp m c β q) (fun _ => rfl)]
  congr 1
  exact thin_seed_integral μ q p hp hp01 m c β

theorem selected_risk (μ : Measure Gap) [IsProbabilityMeasure μ] (p : Gap → ℝ)
    (hp : Measurable p) (hp01 : ∀ d, 0 ≤ p d ∧ p d ≤ 1) (m : ℕ) (c β : ℝ) (q : SignLaw) :
    squaredRisk (oracleLaw (selectedOracle (thinSelected μ p hp m c β)) q)
      (selectedOracle (thinSelected μ p hp m c β)).output (signMean μ q.val) =
      ENNReal.ofReal (thinRisk μ q p m c β) := by
  rw [oracle_squared_risk _ q (fun u => codeStop m (selCode p m u)) (thinProb q p m) m c β _
    (fun u => codeStop_le m _) (selected_law μ p hp m c β q) (fun _ => rfl)]
  congr 1
  exact thin_seed_integral μ q p hp hp01 m c β

theorem revealed_work (μ : Measure Gap) [IsProbabilityMeasure μ] (p : Gap → ℝ)
    (hp : Measurable p) (hp01 : ∀ d, 0 ≤ p d ∧ p d ≤ 1) (m : ℕ) (c β : ℝ) (q : SignLaw) :
    oracleWork (revealedOracle μ (thinRevealed p hp m c β)) q ≤
      ENNReal.ofReal (m * ∫ d, p d ∂μ) := by
  refine (oracle_work_le _ q (fun u => codeStop m (selCode p m u)) m (fun u => codeStop_le m _)
    (measurable_codeStop p hp m) ?_).trans_eq ?_
  · intro u xs
    change (codePolicy m (selCode p m u) xs).isSome = _
    unfold codePolicy
    split_ifs with h <;> simp [h]
  · congr 1
    exact thin_work_integral μ p hp hp01 m

theorem selected_work (μ : Measure Gap) [IsProbabilityMeasure μ] (p : Gap → ℝ)
    (hp : Measurable p) (hp01 : ∀ d, 0 ≤ p d ∧ p d ≤ 1) (m : ℕ) (c β : ℝ) (q : SignLaw) :
    oracleWork (selectedOracle (thinSelected μ p hp m c β)) q ≤
      ENNReal.ofReal (m * ∫ d, p d ∂μ) := by
  refine (oracle_work_le _ q (fun u => codeStop m (selCode p m u)) m (fun u => codeStop_le m _)
    (measurable_codeStop p hp m) ?_).trans_eq ?_
  · intro u xs
    change (selectedLabel xs (codeRequest m (selCode p m u) xs)).isSome = _
    unfold codeRequest
    split_ifs with h <;> simp [h, selectedLabel]
  · congr 1
    exact thin_work_integral μ p hp hp01 m

end ThresholdHC.OracleUpper
