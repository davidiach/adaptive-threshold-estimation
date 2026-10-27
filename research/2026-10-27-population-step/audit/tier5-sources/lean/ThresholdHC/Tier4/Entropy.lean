import Mathlib.InformationTheory.KullbackLeibler.DataProcessing

/-! Relative entropy on measurable restrictions and increasing exhaustions. -/

noncomputable section
open MeasureTheory Set InformationTheory
open scoped ENNReal

namespace ThresholdHC.Tier4

theorem rnDeriv_restrict_both {α : Type*} [MeasurableSpace α]
    (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hac : μ ≪ ν) {s : Set α} (hs : MeasurableSet s) :
    (μ.restrict s).rnDeriv (ν.restrict s) =ᵐ[ν.restrict s] μ.rnDeriv ν := by
  have heq : μ.restrict s = (ν.restrict s).withDensity (μ.rnDeriv ν) := by
    rw [← restrict_withDensity hs, Measure.withDensity_rnDeriv_eq μ ν hac]
  rw [heq]
  exact Measure.rnDeriv_withDensity _ (Measure.measurable_rnDeriv _ _)

theorem klDiv_restrict_eq_lintegral {α : Type*} [MeasurableSpace α]
    (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hac : μ ≪ ν) {s : Set α} (hs : MeasurableSet s) :
    klDiv (μ.restrict s) (ν.restrict s) =
      ∫⁻ x in s, ENNReal.ofReal (klFun (μ.rnDeriv ν x).toReal) ∂ν := by
  rw [klDiv_eq_lintegral_klFun_of_ac (hac.restrict s)]
  apply lintegral_congr_ae
  filter_upwards [rnDeriv_restrict_both μ ν hac hs] with x hx
  rw [hx]

theorem klDiv_restrict_le {α : Type*} [MeasurableSpace α]
    (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {s : Set α} (hs : MeasurableSet s) :
    klDiv (μ.restrict s) (ν.restrict s) ≤ klDiv μ ν := by
  by_cases hac : μ ≪ ν
  · rw [klDiv_restrict_eq_lintegral μ ν hac hs,
      klDiv_eq_lintegral_klFun_of_ac hac]
    exact lintegral_mono' Measure.restrict_le_self le_rfl
  · simp [klDiv_of_not_ac hac]

theorem absolutelyContinuous_of_restrict_exhaustion {α : Type*} [MeasurableSpace α]
    (μ ν : Measure α) (s : ℕ → Set α)
    (hcover : ∀ᵐ x ∂μ, x ∈ ⋃ n, s n)
    (hac : ∀ n, μ.restrict (s n) ≪ ν.restrict (s n)) : μ ≪ ν := by
  apply Measure.ae_le_iff_absolutelyContinuous.mp
  rw [← Measure.restrict_eq_self_of_ae_mem hcover, ae_restrict_iUnion_eq]
  apply iSup_le
  intro n
  exact (hac n).ae_le.trans (Measure.absolutelyContinuous_restrict).ae_le

theorem klDiv_eq_iSup_restrict {α : Type*} [MeasurableSpace α]
    (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (s : ℕ → Set α) (hs : ∀ n, MeasurableSet (s n)) (hmono : Monotone s)
    (hac : μ ≪ ν) (hcover : ∀ᵐ x ∂ν, x ∈ ⋃ n, s n) :
    klDiv μ ν = ⨆ n, klDiv (μ.restrict (s n)) (ν.restrict (s n)) := by
  simp_rw [klDiv_restrict_eq_lintegral μ ν hac (hs _)]
  rw [← setLIntegral_iUnion_of_directed _ hmono.directed_le,
    Measure.restrict_eq_self_of_ae_mem hcover, klDiv_eq_lintegral_klFun_of_ac hac]

theorem klDiv_le_of_restrict_exhaustion {α : Type*} [MeasurableSpace α]
    (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (s : ℕ → Set α) (hs : ∀ n, MeasurableSet (s n)) (hmono : Monotone s)
    (hcoverμ : ∀ᵐ x ∂μ, x ∈ ⋃ n, s n) (hcoverν : ∀ᵐ x ∂ν, x ∈ ⋃ n, s n)
    (C : ℝ≥0∞) (hC : C ≠ ∞)
    (hbound : ∀ n, klDiv (μ.restrict (s n)) (ν.restrict (s n)) ≤ C) :
    klDiv μ ν ≤ C := by
  have hac : μ ≪ ν := absolutelyContinuous_of_restrict_exhaustion μ ν s hcoverμ
    (fun n => (klDiv_ne_top_iff.mp (ne_top_of_le_ne_top hC (hbound n))).1)
  rw [klDiv_eq_iSup_restrict μ ν s hs hmono hac hcoverν]
  exact iSup_le hbound

theorem restrict_eq_map_reconstruct {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (f : α → β) (r : β → α) (s : Set β)
    (hf : Measurable f) (hr : Measurable r) (hs : MeasurableSet s)
    (hrecon : ∀ᵐ x ∂μ.restrict (f ⁻¹' s), r (f x) = x) :
    μ.restrict (f ⁻¹' s) = ((μ.map f).restrict s).map r := by
  rw [Measure.restrict_map hf hs, Measure.map_map hr hf]
  exact (Measure.map_congr hrecon).trans Measure.map_id |>.symm

theorem klDiv_restrict_le_map_of_reconstruct {α β : Type*}
    [MeasurableSpace α] [MeasurableSpace β]
    (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (f : α → β) (r : β → α) (s : Set β)
    (hf : Measurable f) (hr : Measurable r) (hs : MeasurableSet s)
    (hμ : ∀ᵐ x ∂μ.restrict (f ⁻¹' s), r (f x) = x)
    (hν : ∀ᵐ x ∂ν.restrict (f ⁻¹' s), r (f x) = x) :
    klDiv (μ.restrict (f ⁻¹' s)) (ν.restrict (f ⁻¹' s)) ≤
      klDiv (μ.map f) (ν.map f) := by
  rw [restrict_eq_map_reconstruct μ f r s hf hr hs hμ,
    restrict_eq_map_reconstruct ν f r s hf hr hs hν]
  exact (klDiv_map_le _ _ hr).trans (klDiv_restrict_le _ _ hs)

/-- Entropy is recovered by finite observations which reconstruct the outcome
on an increasing, almost-sure exhaustion. No entropy convergence is assumed. -/
theorem klDiv_eq_iSup_map_of_reconstruction {α : Type*} {β : ℕ → Type*}
    [MeasurableSpace α] [∀ n, MeasurableSpace (β n)]
    (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (f : (n : ℕ) → α → β n) (r : (n : ℕ) → β n → α)
    (s : (n : ℕ) → Set (β n))
    (hf : ∀ n, Measurable (f n)) (hr : ∀ n, Measurable (r n))
    (hs : ∀ n, MeasurableSet (s n))
    (hmono : Monotone (fun n => f n ⁻¹' s n))
    (hcoverμ : ∀ᵐ x ∂μ, x ∈ ⋃ n, f n ⁻¹' s n)
    (hcoverν : ∀ᵐ x ∂ν, x ∈ ⋃ n, f n ⁻¹' s n)
    (hreconμ : ∀ n, ∀ᵐ x ∂μ.restrict (f n ⁻¹' s n), r n (f n x) = x)
    (hreconν : ∀ n, ∀ᵐ x ∂ν.restrict (f n ⁻¹' s n), r n (f n x) = x) :
    klDiv μ ν = ⨆ n, klDiv (μ.map (f n)) (ν.map (f n)) := by
  have hlower : (⨆ n, klDiv (μ.map (f n)) (ν.map (f n))) ≤ klDiv μ ν :=
    iSup_le fun n => klDiv_map_le μ ν (hf n)
  by_cases htop : (⨆ n, klDiv (μ.map (f n)) (ν.map (f n))) = ∞
  · exact le_antisymm (htop ▸ le_top) hlower
  have hfinite (n : ℕ) : klDiv (μ.map (f n)) (ν.map (f n)) ≠ ∞ :=
    ne_top_of_le_ne_top htop (le_iSup (fun n => klDiv (μ.map (f n)) (ν.map (f n))) n)
  have hbound (n : ℕ) := klDiv_restrict_le_map_of_reconstruct μ ν (f n) (r n) (s n)
    (hf n) (hr n) (hs n) (hreconμ n) (hreconν n)
  have hac : μ ≪ ν := absolutelyContinuous_of_restrict_exhaustion μ ν
    (fun n => f n ⁻¹' s n) hcoverμ
    (fun n => (klDiv_ne_top_iff.mp (ne_top_of_le_ne_top (hfinite n) (hbound n))).1)
  apply le_antisymm
  · rw [klDiv_eq_iSup_restrict μ ν (fun n => f n ⁻¹' s n)
      (fun n => (hf n) (hs n)) hmono hac hcoverν]
    exact iSup_le fun n => (hbound n).trans (le_iSup (fun n => klDiv (μ.map (f n))
      (ν.map (f n))) n)
  · exact hlower

end ThresholdHC.Tier4
