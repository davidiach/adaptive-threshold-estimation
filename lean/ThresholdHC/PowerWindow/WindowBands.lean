import ThresholdHC.PowerWindow.CoreCost
import ThresholdHC.PowerWindow.FiniteEntropy

noncomputable section
open MeasureTheory Set
open scoped BigOperators ENNReal
namespace ThresholdHC.PowerWindow
open ThresholdHC.Tier6 ThresholdHC.EntropyTailQuantile ThresholdHC.PsiGap

theorem log_bandEdge (j : ℕ) : Real.log (bandEdge j) = -((j : ℝ) + 1) * Real.log 2 := by
  simp only [bandEdge, Real.log_pow, Real.log_inv, Nat.cast_add, Nat.cast_one]
  ring

theorem band_log_bounds {j : ℕ} {d : Gap} (hd : d ∈ band j) :
    ((j : ℝ) + 1) * Real.log 2 ≤ -Real.log (d : ℝ) ∧
      -Real.log (d : ℝ) < ((j : ℝ) + 2) * Real.log 2 := by
  have hu := Real.log_le_log d.2.1 hd.2
  have hl := Real.log_lt_log (div_pos (bandEdge_pos j) (by norm_num)) hd.1
  rw [log_bandEdge] at hu
  rw [Real.log_div (bandEdge_pos j).ne' (by norm_num), log_bandEdge] at hl
  constructor <;> linarith

theorem band_index_antitone {i j : ℕ} {d e : Gap}
    (hd : d ∈ band i) (he : e ∈ band j) (hde : (d : ℝ) ≤ e) : j ≤ i := by
  have hi := band_log_bounds hd
  have hj := band_log_bounds he
  have hl := Real.log_le_log d.2.1 hde
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  by_contra hn
  have hn' : (i : ℝ) + 1 ≤ j := by exact_mod_cast (show i + 1 ≤ j by omega)
  nlinarith

theorem band_window_count {i j : ℕ} {a t : Gap}
    (ha : a ∈ band i) (ht : t ∈ band j) (hta : (t : ℝ) ≤ a) :
    ((Finset.Icc i j).card : ℝ) ≤ Real.log ((a : ℝ) / t) / Real.log 2 + 2 := by
  have hij := band_index_antitone ht ha hta
  have hi := band_log_bounds ha
  have hj := band_log_bounds ht
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  rw [Nat.card_Icc, Nat.cast_sub (by omega : i ≤ j + 1), Nat.cast_add, Nat.cast_one,
    Real.log_div a.2.1.ne' t.2.1.ne']
  nlinarith [div_mul_cancel₀ (Real.log (a : ℝ) - Real.log (t : ℝ)) h2.ne']

theorem band_upper_label {i j : ℕ} {a d : Gap} (ha : a ∈ band i)
    (hd : d ∈ band j) (hda : (d : ℝ) ≤ a) :
    ((j - i : ℕ) : ℝ) ≤ 1 + Real.log ((a : ℝ) / d) / Real.log 2 := by
  have hij := band_index_antitone hd ha hda
  have hi := band_log_bounds ha
  have hj := band_log_bounds hd
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  rw [Nat.cast_sub hij, Real.log_div a.2.1.ne' d.2.1.ne']
  nlinarith [div_mul_cancel₀ (Real.log (a : ℝ) - Real.log (d : ℝ)) h2.ne']

theorem band_lower_label {j k : ℕ} {d t : Gap} (hd : d ∈ band j)
    (ht : t ∈ band k) (htd : (t : ℝ) ≤ d) :
    ((k - j : ℕ) : ℝ) ≤ 1 + Real.log ((d : ℝ) / t) / Real.log 2 := by
  have hjk := band_index_antitone ht hd htd
  have hj := band_log_bounds hd
  have hk := band_log_bounds ht
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  rw [Nat.cast_sub hjk, Real.log_div d.2.1.ne' t.2.1.ne']
  nlinarith [div_mul_cancel₀ (Real.log (d : ℝ) - Real.log (t : ℝ)) h2.ne']

/-- A measure supported in a positive compact window has exactly the finite
band decomposition needed for normalization and the two oriented moments. -/
theorem window_band_decomposition (σ : Measure Gap) [IsFiniteMeasure σ]
    {a t : Gap} {i j : ℕ} (ha : a ∈ band i) (ht : t ∈ band j)
    (hs : ∀ᵐ d : Gap ∂σ, (t : ℝ) ≤ d ∧ (d : ℝ) ≤ a) :
    Integrable (fun d : Gap => (d : ℝ)⁻¹ ^ 2) σ ∧
    (∀ k, k ∉ Finset.Icc i j → bandCost σ k = 0) ∧
    (∑ k ∈ Finset.Icc i j, bandCost σ k) = ∫ d : Gap, (d : ℝ)⁻¹ ^ 2 ∂σ := by
  obtain ⟨_, _, _, _, hint, _⟩ := core_bands σ t.2.1 t.2.2 (hs.mono fun _ h => h.1)
  have hzero (k : ℕ) (hk : k ∉ Finset.Icc i j) : σ (band k) = 0 := by
    have hh : ∀ᵐ d : Gap ∂σ, d ∉ band k := hs.mono fun d hd hdk =>
      hk (Finset.mem_Icc.2 ⟨band_index_antitone hdk ha hd.2,
        band_index_antitone ht hdk hd.1⟩)
    have he : {d : Gap | ¬d ∉ band k} = band k := by ext d; simp
    rw [ae_iff, he] at hh
    exact hh
  have hmem : ∀ᵐ d : Gap ∂σ, d ∈ ⋃ k ∈ Finset.Icc i j, band k := hs.mono fun d hd => by
    obtain ⟨k, hk⟩ := ThresholdHC.EntropyTail.exists_band d
    rw [← ThresholdHC.EntropyTail.quantile_band_eq] at hk
    exact mem_iUnion₂.2 ⟨k, Finset.mem_Icc.2 ⟨band_index_antitone hk ha hd.2,
      band_index_antitone ht hk hd.1⟩, hk⟩
  refine ⟨hint, fun k hk => ?_, ?_⟩
  · simp only [bandCost, Measure.restrict_eq_zero.mpr (hzero k hk), integral_zero_measure]
  · unfold bandCost
    rw [← integral_biUnion_finset (Finset.Icc i j) (fun k _ => measurableSet_band k)
      (fun k _ l _ hkl => bands_disjoint hkl) (fun k _ => hint.integrableOn),
      Measure.restrict_eq_self_of_ae_mem hmem]

theorem finite_entropy_card_bound {ι : Type*} [Fintype ι] {p : ι → ℝ}
    (hp : ∀ i, 0 ≤ p i) (hs : ∑ i, p i = 1) :
    (∑ i, Real.negMulLog (p i)) ≤ Real.log (Fintype.card ι) := by
  have hn : 0 < Fintype.card ι := by
    by_contra hn
    have : Fintype.card ι = 0 := by omega
    have : IsEmpty ι := Fintype.card_eq_zero_iff.1 this
    simp at hs
  have hn' : (0 : ℝ) < Fintype.card ι := by exact_mod_cast hn
  have h := finite_entropy_cross_entropy hp hs
    (q := fun _ => (Fintype.card ι : ℝ)⁻¹) (fun _ => inv_pos.2 hn')
    (by simp [hn'.ne'])
  simpa only [← Finset.sum_mul, hs, one_mul, Real.log_inv, neg_neg] using h

theorem window_entropy_normalization (σ : Measure Gap) [IsFiniteMeasure σ]
    {a t : Gap} {i j : ℕ} (ha : a ∈ band i) (ht : t ∈ band j)
    (hs : ∀ᵐ d : Gap ∂σ, (t : ℝ) ≤ d ∧ (d : ℝ) ≤ a)
    {A : ℝ} (hA : 0 < A) (hAt : (∫ d : Gap, (d : ℝ)⁻¹ ^ 2 ∂σ) = A) :
    (∑ k : Finset.Icc i j, bandCost σ k / A) = 1 ∧
    (∑' k : ℕ, Real.negMulLog (bandCost σ k / A)) =
      ∑ k : Finset.Icc i j, Real.negMulLog (bandCost σ k / A) := by
  classical
  obtain ⟨_, hz, hsum⟩ := window_band_decomposition σ ha ht hs
  constructor
  · rw [Finset.sum_coe_sort (Finset.Icc i j) (fun k => bandCost σ k / A),
      ← Finset.sum_div, hsum, hAt, div_self hA.ne']
  · rw [Finset.sum_coe_sort (Finset.Icc i j) (fun k => Real.negMulLog (bandCost σ k / A))]
    exact tsum_eq_sum fun k hk => by simp [hz k hk]

/-- Band labels can be bounded before integration, then averaged with the
inverse-square cost weights. -/
theorem window_label_mean (σ : Measure Gap) [IsFiniteMeasure σ]
    {a t : Gap} {i j : ℕ} (ha : a ∈ band i) (ht : t ∈ band j)
    (hs : ∀ᵐ d : Gap ∂σ, (t : ℝ) ≤ d ∧ (d : ℝ) ≤ a)
    (k : ℕ → ℕ) (g : Gap → ℝ)
    (hint : Integrable (fun d : Gap => (d : ℝ)⁻¹ ^ 2 * g d) σ)
    (hbound : ∀ l ∈ Finset.Icc i j, ∀ᵐ d : Gap ∂σ,
      d ∈ band l → (k l : ℝ) ≤ g d) :
    (∑ l ∈ Finset.Icc i j, bandCost σ l * (k l : ℝ)) ≤
      ∫ d : Gap, (d : ℝ)⁻¹ ^ 2 * g d ∂σ := by
  obtain ⟨hi, _, _⟩ := window_band_decomposition σ ha ht hs
  have hmem : ∀ᵐ d : Gap ∂σ, d ∈ ⋃ l ∈ Finset.Icc i j, band l := hs.mono fun d hd => by
    obtain ⟨l, hl⟩ := ThresholdHC.EntropyTail.exists_band d
    rw [← ThresholdHC.EntropyTail.quantile_band_eq] at hl
    exact mem_iUnion₂.2 ⟨l, Finset.mem_Icc.2 ⟨band_index_antitone hl ha hd.2,
      band_index_antitone ht hl hd.1⟩, hl⟩
  calc
    _ ≤ ∑ l ∈ Finset.Icc i j, ∫ d in band l, (d : ℝ)⁻¹ ^ 2 * g d ∂σ := by
      apply Finset.sum_le_sum
      intro l hl
      rw [bandCost, ← integral_mul_const]
      apply integral_mono_ae (hi.integrableOn.mul_const _) hint.integrableOn
      filter_upwards [ae_restrict_of_ae (hbound l hl), ae_restrict_mem (measurableSet_band l)]
        with d hd hdl
      exact mul_le_mul_of_nonneg_left (hd hdl) (sq_nonneg _)
    _ = _ := by
      rw [← integral_biUnion_finset (Finset.Icc i j) (fun l _ => measurableSet_band l)
        (fun l _ n _ hln => bands_disjoint hln) (fun l _ => hint.integrableOn),
        Measure.restrict_eq_self_of_ae_mem hmem]

end ThresholdHC.PowerWindow
