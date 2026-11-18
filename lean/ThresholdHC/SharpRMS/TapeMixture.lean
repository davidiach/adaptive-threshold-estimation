import ThresholdHC.SharpRMS.TapeLaw
import Mathlib.Probability.ProductMeasure

/-! Identify one-coin measures from cylinders, including the mixed signs and
the sampled magnitude. -/
noncomputable section
namespace ThresholdHC.SharpRMS
open MeasureTheory ProbabilityTheory Set Tier6 CriticalEntropy ObservableSimulation
open scoped ENNReal

private theorem begins_prefix {n : ℕ} (w : Fin n → Bool) (x : ℕ → Bool) :
    begins (List.ofFn w) x ↔ Tier2.tapePrefix n x=w := by
  induction n generalizing x with
  | zero => simp [begins,Subsingleton.elim (Tier2.tapePrefix 0 x) w]
  | succ n ih =>
    obtain ⟨b,v,rfl⟩ := Fin.exists_cons w
    rw [List.ofFn_cons]
    change (x 0=b ∧ begins (List.ofFn v) (tapeDrop 1 x)) ↔ _
    rw [ih]
    constructor
    · rintro ⟨hb,h⟩
      funext i
      refine Fin.cases hb (fun j => ?_) i
      simpa only [Tier2.tapePrefix,tapeDrop,Fin.cons_succ,Fin.val_succ,Nat.add_comm] using congrFun h j
    · intro he
      refine ⟨congrFun he 0,?_⟩
      funext j
      simpa only [Tier2.tapePrefix,tapeDrop,Fin.cons_succ,Fin.val_succ,Nat.add_comm] using congrFun he j.succ

theorem tape_ext_words (P Q : Measure (ℕ → Bool)) [IsFiniteMeasure P] [IsFiniteMeasure Q]
    (words : ∀ w : List Bool, P {x | begins w x} = Q {x | begins w x}) : P=Q := by
  have pref (n : ℕ) : P.map (Tier2.tapePrefix n)=Q.map (Tier2.tapePrefix n) := by
    apply Measure.ext_of_singleton
    intro w
    have hm : Measurable (Tier2.tapePrefix n) := Measurable.of_eval fun i => measurable_pi_apply i.val
    rw [Measure.map_apply hm (measurableSet_singleton _),Measure.map_apply hm (measurableSet_singleton _)]
    change P {x | Tier2.tapePrefix n x=w} = Q {x | Tier2.tapePrefix n x=w}
    simpa only [begins_prefix] using words (List.ofFn w)
  let family (J : Finset ℕ) := P.map J.restrict
  have pp : IsProjectiveLimit P family := fun _ => rfl
  apply pp.unique
  intro J
  let N := J.sup id+1
  let restrict (w : Fin N → Bool) (j : J) := w ⟨j.val,Nat.lt_succ_of_le (Finset.le_sup (f:=id) j.property)⟩
  have mr : Measurable restrict := Measurable.of_eval (fun _ => measurable_pi_apply _)
  have mp : Measurable (Tier2.tapePrefix N) := Measurable.of_eval fun i => measurable_pi_apply i.val
  have eq := congrArg (fun (ν : Measure (Fin N → Bool)) => ν.map restrict) (pref N)
  rw [Measure.map_map mr mp,Measure.map_map mr mp] at eq
  exact eq.symm

theorem iid_word (p : unitInterval) (w : List Bool) :
    Tier2.tapeMeasure p {x | begins w x} = ENNReal.ofReal (wordMass p.val (w.count true) (w.count false)) := by
  induction w with
  | nil => simp [begins,wordMass]
  | cons b w ih =>
    let S : Set (Bool × (ℕ → Bool)) := {b} ×ˢ {x | begins w x}
    have ms : MeasurableSet S := (measurableSet_singleton b).prod (measurable_begins w)
    change Tier2.tapeMeasure p ((fun x => (x 0,tapeDrop 1 x)) ⁻¹' S) = _
    rw [(tape_head_drop_preserving p).measure_preimage ms.nullMeasurableSet,Measure.prod_prod,ih]
    have atom : (bernoulliMeasure true false p) {b} = ENNReal.ofReal (bitMass p.val b) := by
      cases b <;> simp [bernoulliMeasure_def,bitMass,←ENNReal.ofReal_coe_nnreal]
    rw [atom,←ENNReal.ofReal_mul (by cases b <;> simp [bitMass,p.property.1,p.property.2])]
    congr 1
    cases b <;> simp [bitMass,wordMass,pow_succ] <;> ring

theorem original_tape_lintegral (μ : Measure Gap) [IsProbabilityMeasure μ] (q : SignLaw)
    (F : (ℕ → Bool) → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ x, F x ∂originalPopulationTapeLaw μ q) =
    ∫⁻ d, ENNReal.ofReal (q.val d)*(∫⁻ x, F x ∂Tier2.tapeMeasure (gapParameter true d))+
      ENNReal.ofReal (1-q.val d)*(∫⁻ x, F x ∂Tier2.tapeMeasure (gapParameter false d)) ∂μ := by
  let G := fun (p : unitInterval) => ∫⁻ v, F (uniformCoinTape p v) ∂uniformTapeMeasure
  have hm : Measurable G := (hF.comp measurable_uniformCoinTape).lintegral_prod_right'
  have comp (p : unitInterval) : G p = ∫⁻ x, F x ∂Tier2.tapeMeasure p := by
    have m : Measurable (uniformCoinTape p) := measurable_uniformCoinTape.comp (measurable_const.prodMk measurable_id)
    rw [←uniformCoinTape_map,lintegral_map hF m]
  let p0 := gapParameter false
  let p1 := gapParameter true
  let q0 := signUnit q
  have mm := measurable_mixtureParameter p0 p1 q0 (measurable_gapParameter false)
    (measurable_gapParameter true) (measurable_signUnit q)
  let κ := populationParameterLaw μ p0 p1 q0
  let : IsProbabilityMeasure κ := populationParameterLaw_probability μ p0 p1 q0
    (measurable_gapParameter false) (measurable_gapParameter true) (measurable_signUnit q)
  change (∫⁻ x, F x ∂(κ.prod uniformTapeMeasure).map (fun z => uniformCoinTape z.1 z.2)) = _
  rw [lintegral_map hF measurable_uniformCoinTape,lintegral_prod (fun z => F (uniformCoinTape z.1 z.2)) (hF.comp measurable_uniformCoinTape).aemeasurable]
  change (∫⁻ p, G p ∂(μ.prod uniformUnitMeasure).map (mixtureParameter p0 p1 q0)) = _
  rw [lintegral_map hm mm,lintegral_prod (fun z => G (mixtureParameter p0 p1 q0 z)) (hm.comp mm).aemeasurable]
  exact lintegral_congr (fun d => by simpa only [comp,p0,p1,q0,signUnit] using mixtureParameter_lintegral p0 p1 q0 d G hm)

end ThresholdHC.SharpRMS
