import ThresholdHC.Tier4.Entropy
import Mathlib.Probability.Martingale.Convergence

/-! Relative entropy approximation along generating finite observations.
Only absolute continuity of the first law is required; the second law need
not be supported on finite stopping histories. -/

noncomputable section
open MeasureTheory InformationTheory Filter
open scoped ENNReal Topology

namespace ThresholdHC.Tier5

theorem klDiv_map_eq_lintegral_condExp {α β : Type*}
    [MeasurableSpace α] [mβ : MeasurableSpace β]
    (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (f : α → β) (hf : Measurable f) (hac : μ ≪ ν) :
    klDiv (μ.map f) (ν.map f) =
      ∫⁻ x, ENNReal.ofReal (klFun ((ν[fun x => (μ.rnDeriv ν x).toReal |
        mβ.comap f]) x)) ∂ν := by
  rw [klDiv_eq_lintegral_klFun_of_ac (hac.map hf), lintegral_map (by fun_prop) hf]
  apply lintegral_congr_ae
  filter_upwards [toReal_rnDeriv_map hac hf] with x hx
  rw [hx]

theorem klDiv_eq_iSup_map_of_generates {α : Type*} {β : ℕ → Type*}
    [mα : MeasurableSpace α] [mβ : ∀ n, MeasurableSpace (β n)]
    (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (f : (n : ℕ) → α → β n) (hf : ∀ n, Measurable (f n))
    (hmono : Monotone (fun n => (mβ n).comap (f n)))
    (hgen : (⨆ n, (mβ n).comap (f n)) = mα) (hac : μ ≪ ν) :
    klDiv μ ν = ⨆ n, klDiv (μ.map (f n)) (ν.map (f n)) := by
  let ℱ : Filtration ℕ mα := ⟨fun n => (mβ n).comap (f n), hmono, fun n => (hf n).comap_le⟩
  let g : α → ℝ := fun x => (μ.rnDeriv ν x).toReal
  have hg : Integrable g ν := Measure.integrable_toReal_rnDeriv
  have hgm : StronglyMeasurable[⨆ n, ℱ n] g := by
    change StronglyMeasurable[⨆ n, (mβ n).comap (f n)] g
    rw [hgen]
    exact (Measure.measurable_rnDeriv μ ν).ennreal_toReal.stronglyMeasurable
  have hconv := hg.tendsto_ae_condExp (ℱ := ℱ) hgm
  have hlim : (fun x => ENNReal.ofReal (klFun (g x))) =ᵐ[ν]
      (fun x => liminf (fun n => ENNReal.ofReal (klFun ((ν[g | ℱ n]) x))) atTop) := by
    filter_upwards [hconv] with x hx
    exact ((ENNReal.continuous_ofReal.tendsto _).comp
      ((continuous_klFun.tendsto _).comp hx)).liminf_eq.symm
  apply le_antisymm
  · rw [klDiv_eq_lintegral_klFun_of_ac hac]
    change (∫⁻ x, ENNReal.ofReal (klFun (g x)) ∂ν) ≤ _
    rw [lintegral_congr_ae hlim]
    calc
      _ ≤ liminf (fun n => ∫⁻ x, ENNReal.ofReal (klFun ((ν[g | ℱ n]) x)) ∂ν) atTop := by
        apply lintegral_liminf_le
        intro n
        exact (continuous_klFun.measurable.comp
          ((stronglyMeasurable_condExp.mono (ℱ.le n)).measurable)).ennreal_ofReal
      _ ≤ ⨆ n, klDiv (μ.map (f n)) (ν.map (f n)) := by
        simp_rw [show ∀ n, (∫⁻ x, ENNReal.ofReal (klFun ((ν[g | ℱ n]) x)) ∂ν) =
          klDiv (μ.map (f n)) (ν.map (f n)) from
          fun n => (klDiv_map_eq_lintegral_condExp μ ν (f n) (hf n) hac).symm]
        calc
          _ ≤ limsup (fun n => klDiv (μ.map (f n)) (ν.map (f n))) atTop :=
            liminf_le_limsup
          _ ≤ _ := limsup_le_of_le (h := Filter.Eventually.of_forall (fun n =>
            le_iSup (fun n => klDiv (μ.map (f n)) (ν.map (f n))) n))
  · exact iSup_le fun n => klDiv_map_le μ ν (hf n)

end ThresholdHC.Tier5
