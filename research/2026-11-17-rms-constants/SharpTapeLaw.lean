import SharpCausal
import SharpWordSimulation
import ThresholdHC.ContinuousObserved.UniformTape
import ThresholdHC.CriticalEntropy.PopulationTapeLaw

/-! Cylinder probabilities for the causal one-coin tape transformation. -/
noncomputable section
namespace ThresholdHC.SharpRMS
open MeasureTheory ProbabilityTheory Set CriticalEntropy ContinuousObserved Tier6 ObservableSimulation
open scoped ENNReal

def observedSign (e : Bool) : ℝ := if e then 1 else -1

private theorem valid_sign (e : Bool) : observedSign e= -1 ∨ observedSign e=1 := by cases e <;> simp [observedSign]

def outputParameter (d g : Gap) (h l : ℕ) (y : Bool) : unitInterval :=
  ⟨(1+channelMean (2*d.val) (2*g.val) h l (observedSign y))/2, by
    have h := channel_range (2*d.val) (2*g.val) (by linarith [d.property.1]) (by linarith [d.property.2])
      (by linarith [g.property.1]) h l (observedSign y) (by cases y <;> norm_num [observedSign])
    constructor <;> linarith [(abs_le.mp h).1,(abs_le.mp h).2]⟩

theorem measurable_outputParameter (g : Gap) (h l : ℕ) (y : Bool) :
    Measurable (fun d : Gap => outputParameter d g h l y) := by
  apply Measurable.subtype_mk
  exact (measurable_const.add ((measurable_channelMean _ _ _ _).comp
    (measurable_const.mul measurable_subtype_coe))).div_const 2

def coinDecoder (d g : Gap) (h l : ℕ) (v : ℕ → ℝ) (xs : List Bool) (y : Bool) :=
  uniformCoinFlip (outputParameter d g (h+xs.count true) (l+xs.count false) y) (v xs.length)

theorem measurable_coinDecoder (g : Gap) (h l : ℕ) (xs : List Bool) (y : Bool) :
    Measurable (fun z : Gap × (ℕ → ℝ) => coinDecoder z.1 g h l z.2 xs y) :=
  measurable_uniformCoinFlip.comp (((measurable_outputParameter g _ _ y).comp measurable_fst).prodMk
    ((measurable_pi_apply _).comp measurable_snd))

def virtualTape (d g : Gap) (h l : ℕ) (v : ℕ → ℝ) (raw : ℕ → Bool) :=
  transformTape (coinDecoder d g h l v) raw

private theorem shift_virtual (d g : Gap) (h l : ℕ) (v : ℕ → ℝ) (raw : ℕ → Bool) (b : Bool)
    (eq : virtualTape d g h l v raw 0=b) :
    tapeDrop 1 (virtualTape d g h l v raw) =
      virtualTape d g (h+if b then 1 else 0) (l+if b then 0 else 1) (uniformTail v) (tapeDrop 1 raw) := by
  change coinDecoder d g h l v [] (raw 0)=b at eq
  change tapeDrop 1 (transformTape (coinDecoder d g h l v) raw)=_
  have tail (c : List Bool → Bool → Bool) (r : ℕ → Bool) : tapeDrop 1 (transformTape c r) =
      transformTape (fun ys => c (c [] (r 0)::ys)) (tapeDrop 1 r) := by
    funext n
    unfold tapeDrop
    rw [show 1+n=n+1 by omega]
    rfl
  rw [tail,eq]
  apply congrArg (fun c => transformTape c (tapeDrop 1 raw))
  funext xs y
  cases b <;> simp [coinDecoder,uniformTail,Nat.add_comm,Nat.add_left_comm]

private theorem split_pair (p : unitInterval) :
    MeasurePreserving (fun z : (ℕ → ℝ) × (ℕ → Bool) =>
      ((z.2 0,z.1 0),(uniformTail z.1,tapeDrop 1 z.2)))
      (uniformTapeMeasure.prod (Tier2.tapeMeasure p))
      (((bernoulliMeasure true false p).prod uniformUnitMeasure).prod
        (uniformTapeMeasure.prod (Tier2.tapeMeasure p))) := by
  let A := uniformUnitMeasure
  let B := uniformTapeMeasure
  let C := bernoulliMeasure true false p
  let D := Tier2.tapeMeasure p
  have h := uniform_head_tail_preserving.prod (tape_head_drop_preserving p)
  have h1 := measurePreserving_prodAssoc A B (C.prod D)
  have h2 := (MeasurePreserving.id A).prod (measurePreserving_prodAssoc B C D).symm
  have h3 := (MeasurePreserving.id A).prod
    ((Measure.measurePreserving_swap (μ := B) (ν := C)).prod (MeasurePreserving.id D))
  have h4 := (MeasurePreserving.id A).prod (measurePreserving_prodAssoc C B D)
  have h5 := (measurePreserving_prodAssoc A C (B.prod D)).symm
  have h6 := (Measure.measurePreserving_swap (μ := A) (ν := C)).prod (MeasurePreserving.id (B.prod D))
  exact h6.comp (h5.comp (h4.comp (h3.comp (h2.comp (h1.comp h)))))

def bitMass (p : ℝ) (b : Bool) := if b then p else 1-p

private theorem uniform_atom (p : unitInterval) (b : Bool) :
    uniformUnitMeasure {x | uniformCoinFlip p x=b} = ENNReal.ofReal (bitMass p.val b) := by
  have hm : Measurable (uniformCoinFlip p) := measurable_uniformCoinFlip.comp (measurable_const.prodMk measurable_id)
  have e := congrArg (fun (μ : Measure Bool) => μ {b}) (uniformCoinFlip_map p)
  rw [Measure.map_apply hm (measurableSet_singleton _)] at e
  apply e.trans
  cases b <;> simp [bernoulliMeasure_def,bitMass,← ENNReal.ofReal_coe_nnreal]

private theorem mixed_atom (p : unitInterval) (r : Bool → unitInterval) (b : Bool) :
    ((bernoulliMeasure true false p).prod uniformUnitMeasure)
      {z | uniformCoinFlip (r z.1) z.2=b} =
      ENNReal.ofReal (p.val*bitMass (r true).val b+(1-p.val)*bitMass (r false).val b) := by
  have hm : Measurable (fun z : Bool × ℝ => uniformCoinFlip (r z.1) z.2) := measurable_uniformCoinFlip.comp (((measurable_of_countable r).comp measurable_fst).prodMk measurable_snd)
  rw [Measure.prod_apply (measurableSet_eq_fun hm (measurable_const (a := b)))]
  change (∫⁻ y, uniformUnitMeasure {v | uniformCoinFlip (r y) v=b} ∂bernoulliMeasure true false p) = _
  simp_rw [uniform_atom]
  have pos (q : unitInterval) : 0≤bitMass q.val b := by cases b <;> simp [bitMass,q.property.1,q.property.2]
  rw [ENNReal.ofReal_add (mul_nonneg p.property.1 (pos _)) (mul_nonneg (sub_nonneg.mpr p.property.2) (pos _)),
    ENNReal.ofReal_mul p.property.1,ENNReal.ofReal_mul (sub_nonneg.mpr p.property.2)]
  simp [bernoulliMeasure_def,lintegral_add_measure,lintegral_smul_measure,ENNReal.smul_def,smul_eq_mul,ENNReal.coe_nnreal_eq]

def begins : List Bool → (ℕ → Bool) → Prop
  | [], _ => True
  | b::bs, x => x 0=b ∧ begins bs (tapeDrop 1 x)

theorem measurable_begins (w : List Bool) : MeasurableSet {x | begins w x} := by
  induction w with
  | nil => simp [begins]
  | cons b w ih => exact (measurableSet_eq_fun (measurable_pi_apply 0) measurable_const).inter ((measurable_tapeDrop 1) ih)

theorem measurable_virtualTape_joint (g : Gap) (h l : ℕ) :
    Measurable (fun z : (Gap × (ℕ → ℝ)) × (ℕ → Bool) => virtualTape z.1.1 g h l z.1.2 z.2) :=
  measurable_transformTape (fun (z : Gap × (ℕ → ℝ)) xs y => coinDecoder z.1 g h l z.2 xs y) (measurable_coinDecoder g h l)

private theorem measurable_fixed_virtual (d g : Gap) (h l : ℕ) :
    Measurable (fun z : (ℕ → ℝ) × (ℕ → Bool) => virtualTape d g h l z.1 z.2) :=
  (measurable_virtualTape_joint g h l).comp ((measurable_const.prodMk measurable_fst).prodMk measurable_snd)

def virtualEvent (d g : Gap) (h l : ℕ) (w : List Bool) : Set ((ℕ → ℝ) × (ℕ → Bool)) :=
  {z | begins w (virtualTape d g h l z.1 z.2)}

private theorem event_step (d g : Gap) (p : unitInterval) (h l : ℕ) (b : Bool) (w : List Bool) :
    let law := uniformTapeMeasure.prod (Tier2.tapeMeasure p)
    law (virtualEvent d g h l (b::w)) =
      ENNReal.ofReal (p.val*bitMass (outputParameter d g h l true).val b+
        (1-p.val)*bitMass (outputParameter d g h l false).val b)*
      law (virtualEvent d g (h+if b then 1 else 0) (l+if b then 0 else 1) w) := by
  let f := fun z : (ℕ → ℝ) × (ℕ → Bool) => ((z.2 0,z.1 0),(uniformTail z.1,tapeDrop 1 z.2))
  let H := {z : Bool × ℝ | uniformCoinFlip (outputParameter d g h l z.1) z.2=b}
  let T := virtualEvent d g (h+if b then 1 else 0) (l+if b then 0 else 1) w
  have mh : Measurable (fun z : Bool × ℝ => uniformCoinFlip (outputParameter d g h l z.1) z.2) :=
    measurable_uniformCoinFlip.comp (((measurable_of_countable (outputParameter d g h l)).comp measurable_fst).prodMk measurable_snd)
  have hH : MeasurableSet H := measurableSet_eq_fun mh measurable_const
  have hT : MeasurableSet T := measurable_fixed_virtual d g _ _ (measurable_begins w)
  have first (z : (ℕ → ℝ) × (ℕ → Bool)) :
      virtualTape d g h l z.1 z.2 0=uniformCoinFlip (outputParameter d g h l (z.2 0)) (z.1 0) := by
    simp [virtualTape,transformTape,coinDecoder]
  have eq : virtualEvent d g h l (b::w) = f ⁻¹' (H ×ˢ T) := by
    ext z
    change (virtualTape d g h l z.1 z.2 0=b ∧ _) ↔ (uniformCoinFlip _ _=b ∧ _)
    rw [←first]
    exact and_congr_right fun head => by rw [shift_virtual d g h l z.1 z.2 b head]; rfl
  rw [eq]
  change (uniformTapeMeasure.prod (Tier2.tapeMeasure p)) (f ⁻¹' (H ×ˢ T)) = _
  calc
    _ = _ := (split_pair p).measure_preimage (hH.prod hT).nullMeasurableSet
    _ = _ := by rw [Measure.prod_prod]; exact congrArg (fun z => z * _) (mixed_atom p _ b)

theorem virtual_word_probability (d g : Gap) (e : Bool) (w : List Bool) (h l : ℕ) :
    let a := 2*d.val
    let s := 2*g.val
    let f := min 1 (s/a)
    let L := conditionalWord a f (observedSign e)
    ENNReal.ofReal (L h l) * (uniformTapeMeasure.prod (Tier2.tapeMeasure (gapParameter e g)))
      (virtualEvent d g h l w) = ENNReal.ofReal (L (h+w.count true) (l+w.count false)) := by
  let a := 2*d.val
  let s := 2*g.val
  let E := observedSign e
  let f := min 1 (s/a)
  let L := conditionalWord a f E
  let P := uniformTapeMeasure.prod (Tier2.tapeMeasure (gapParameter e g))
  change ENNReal.ofReal (L h l)*P (virtualEvent d g h l w) = ENNReal.ofReal (L (h+w.count true) (l+w.count false))
  have sa : 0<s := by dsimp [s]; linarith [g.property.1]
  have aa : 0<a := by dsimp [a]; linarith [d.property.1]
  have a1 : a≤1 := by dsimp [a]; linarith [d.property.2]
  have ff : 0≤f ∧ f≤1 := ⟨le_min zero_le_one (div_nonneg sa.le aa.le),min_le_left ..⟩
  have L0 (h l) : 0≤L h l := by
    have q0 : 0≤(1+a)/2 := by linarith
    have q1 : 0≤(1-a)/2 := by linarith
    have w0 (p : ℝ) (p0 : 0≤p) (p1 : p≤1) : 0≤wordMass p h l :=
      mul_nonneg (pow_nonneg p0 _) (pow_nonneg (sub_nonneg.mpr p1) _)
    have c0 : 0≤(1+f*E)/2 ∧ 0≤(1-f*E)/2 := by
      rcases valid_sign e with he|he <;> change observedSign e=_ at he <;> dsimp [E] <;> rw [he] <;> constructor <;> linarith [ff.1,ff.2]
    exact add_nonneg (mul_nonneg c0.1 (w0 _ q0 (by linarith))) (mul_nonneg c0.2 (w0 _ q1 (by linarith)))
  have pval : (gapParameter e g).val=(1+s*E)/2 := by cases e <;> simp [gapParameter,s,E,observedSign] <;> ring
  induction w generalizing h l with
  | nil => simp [virtualEvent,begins,P]
  | cons b w ih =>
    let m := ((1+s*E)/2)*channelMean a s h l 1+((1-s*E)/2)*channelMean a s h l (-1)
    have hm := simulate_word_step a s E aa a1 sa h l (valid_sign e)
    change L (h+1) l=L h l*((1+m)/2) ∧ L h (l+1)=L h l*((1-m)/2) at hm
    have ph : (1+s*E)/2*(bitMass (outputParameter d g h l true).val b) +
        (1-(1+s*E)/2)*(bitMass (outputParameter d g h l false).val b) =
        (if b then (1+m)/2 else (1-m)/2) := by
      cases b <;> dsimp [bitMass,outputParameter,m,a,s,E,observedSign] <;> ring
    have update := event_step d g (gapParameter e g) h l b w
    rw [pval,ph] at update
    change P _ = _*P _ at update
    rw [update,←mul_assoc,←ENNReal.ofReal_mul (L0 h l)]
    cases b with
    | false => simpa [←hm.2,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using ih h (l+1)
    | true => simpa [←hm.1,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using ih (h+1) l

end ThresholdHC.SharpRMS
