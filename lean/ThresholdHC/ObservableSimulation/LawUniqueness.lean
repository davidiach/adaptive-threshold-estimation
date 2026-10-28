import Mathlib
import ThresholdHC.Tier4.StoppedReconstruction
import ThresholdHC.Tier5.Model

noncomputable section

namespace ThresholdHC.ObservableSimulation
open MeasureTheory ThresholdHC.Tier3 ThresholdHC.Tier4

/-- Seed-and-tape laws are determined by every observable finite prefix.
No countability or standard-Borel assumption is imposed on the seed space. -/
theorem joint_tape_law_ext {R : Type} [MeasurableSpace R]
    (P Q : Measure (R × ProcessTape)) [IsFiniteMeasure P] [IsFiniteMeasure Q]
    (hprefix : ∀ n : ℕ,
      P.map (fun z => (z.1,processPrefix n z.2)) =
      Q.map (fun z => (z.1,processPrefix n z.2))) : P = Q := by
  classical
  let F : R × ProcessTape → ℕ → R × Option Bool := fun z n => (z.1,z.2 n)
  have hF : Measurable F := Measurable.of_eval (fun n =>
    measurable_fst.prodMk ((measurable_pi_apply n).comp measurable_snd))
  have hfinite (I : Finset ℕ) :
      P.map (fun z => I.restrict (F z)) = Q.map (fun z => I.restrict (F z)) := by
    let N := I.sup id+1
    have hi (i : I) : i.val < N := Nat.lt_succ_of_le (Finset.le_sup (f := id) i.property)
    let e : R × Prefix N → (i : I) → R × Option Bool :=
      fun z i => (z.1,z.2 ⟨i.val,hi i⟩)
    have he : Measurable e := Measurable.of_eval (fun i =>
      measurable_fst.prodMk ((measurable_pi_apply (⟨i.val,hi i⟩ : Fin N)).comp measurable_snd))
    have heq (ν : Measure (R × ProcessTape)) :
        (ν.map (fun z => (z.1,processPrefix N z.2))).map e =
          ν.map (fun z => I.restrict (F z)) := by
      rw [Measure.map_map he (measurable_jointPrefix N)]
      rfl
    rw [← heq P,← heq Q,hprefix N]
  let family (I : Finset ℕ) := P.map (fun z => I.restrict (F z))
  have hP : IsProjectiveLimit (P.map F) family := by
    intro I
    rw [Measure.map_map (Finset.measurable_restrict _) hF]
    rfl
  have hQ : IsProjectiveLimit (Q.map F) family := by
    intro I
    rw [Measure.map_map (Finset.measurable_restrict _) hF]
    exact (hfinite I).symm
  have hwhole := hP.unique hQ
  let g : (ℕ → R × Option Bool) → R × ProcessTape := fun z => ((z 0).1,fun n => (z n).2)
  have hg : Measurable g :=
    (measurable_fst.comp (measurable_pi_apply 0)).prodMk
      (Measurable.of_eval (fun n => measurable_snd.comp (measurable_pi_apply n)))
  have hback := congrArg (fun ν : Measure (ℕ → R × Option Bool) => ν.map g) hwhole
  rw [Measure.map_map hg hF,Measure.map_map hg hF] at hback
  have hinv : g ∘ F = id := by rfl
  simpa only [hinv,Measure.map_id] using hback

end ThresholdHC.ObservableSimulation

namespace ThresholdHC.ObservableSimulation
open MeasureTheory ThresholdHC.Tier3 ThresholdHC.Tier4
open scoped ENNReal

theorem measure_eq_of_bounded_real_tests {X : Type} [MeasurableSpace X]
    (P Q : Measure X) [IsFiniteMeasure P] [IsFiniteMeasure Q]
    (h : ∀ f : X → ℝ, Measurable f → (∃ C : ℝ, ∀ x, |f x| ≤ C) →
      (∫ x, f x ∂P) = ∫ x, f x ∂Q) : P = Q := by
  apply Measure.ext
  intro S hS
  apply (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).mp
  change P.real S = Q.real S
  let g : X → ℝ := S.indicator (fun _ => 1)
  have hg : Measurable g := measurable_const.indicator hS
  have hb : ∃ C : ℝ, ∀ x, |g x| ≤ C := by
    refine ⟨1,?_⟩
    intro x
    by_cases hx : x ∈ S <;> simp [g,hx]
  simpa only [g,integral_indicator_const (1 : ℝ) hS,smul_eq_mul,mul_one] using h g hg hb

/-- Two concrete experiments realizing the same creation-prefix laws have the
same full observable law, even when their underlying sample spaces differ. -/
theorem realizes_creation_joint_law_unique {R Ω Ξ : Type}
    [MeasurableSpace R] [MeasurableSpace Ω] [MeasurableSpace Ξ]
    (μ : Measure R) (P : Measure Ω) (Q : Measure Ξ)
    [IsFiniteMeasure P] [IsFiniteMeasure Q]
    (seedP : Ω → R) (tapeP : Ω → ProcessTape)
    (seedQ : Ξ → R) (tapeQ : Ξ → ProcessTape)
    (pol : R → List Bool → Option ℕ) (d q : R → ℕ → ℝ)
    (hsP : Measurable seedP) (htP : Measurable tapeP)
    (hsQ : Measurable seedQ) (htQ : Measurable tapeQ)
    (hP : Tier5.RealizesCreationPrefixes μ P seedP tapeP pol d q)
    (hQ : Tier5.RealizesCreationPrefixes μ Q seedQ tapeQ pol d q) :
    P.map (fun x => (seedP x,tapeP x)) = Q.map (fun x => (seedQ x,tapeQ x)) := by
  apply joint_tape_law_ext
  intro n
  rw [Measure.map_map (measurable_jointPrefix n) (hsP.prodMk htP),
    Measure.map_map (measurable_jointPrefix n) (hsQ.prodMk htQ)]
  apply measure_eq_of_bounded_real_tests
  intro f hf hb
  have hprefP := (measurable_jointPrefix n).comp (hsP.prodMk htP)
  have hprefQ := (measurable_jointPrefix n).comp (hsQ.prodMk htQ)
  rw [integral_map hprefP.aemeasurable hf.aestronglyMeasurable,
    integral_map hprefQ.aemeasurable hf.aestronglyMeasurable]
  have hfm (w : Prefix n) : Measurable (fun u : R => f (u,w)) :=
    hf.comp (measurable_id.prodMk measurable_const)
  have hfb : ∃ C : ℝ, ∀ u w, |f (u,w)| ≤ C := by
    obtain ⟨C,hC⟩ := hb
    exact ⟨C,fun u w => hC (u,w)⟩
  exact (hP n (fun u w => f (u,w)) hfm hfb).trans
    (hQ n (fun u w => f (u,w)) hfm hfb).symm

end ThresholdHC.ObservableSimulation
