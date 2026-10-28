import ThresholdHC.CriticalEntropy.LocalSimulation
import ThresholdHC.CriticalEntropy.FinitePopulation

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace ThresholdHC.CriticalEntropy

theorem tape_head_drop_preserving (p : unitInterval) :
    MeasurePreserving (fun ω : ℕ → Bool => (ω 0,tapeDrop 1 ω))
      (Tier2.tapeMeasure p) ((bernoulliMeasure true false p).prod (Tier2.tapeMeasure p)) := by
  have hi : IndepFun (fun ω : ℕ → Bool => ω 0) (tapeDrop 1) (Tier2.tapeMeasure p) :=
    (prefix_drop_independent p 1).comp
      (measurable_pi_apply (0 : Fin 1)) measurable_id
  refine ⟨(measurable_pi_apply 0).prodMk (measurable_tapeDrop 1),?_⟩
  rw [hi.map_prod_eq_prod_map_map (measurable_pi_apply 0).aemeasurable
    (measurable_tapeDrop 1).aemeasurable,tapeDrop_map]
  congr 1
  exact (measurePreserving_eval_infinitePi (fun _ : ℕ => bernoulliMeasure true false p) 0).map_eq

/-- Extracting one current head leaves the full independent array of unused
tapes. This is a fixed-parameter probability identity, not an assumed oracle. -/
theorem array_head_drop_preserving {m : ℕ} (p : Fin m → unitInterval) (j : Fin m) :
    MeasurePreserving
      (fun s : Fin m → ℕ → Bool => (s j 0,Function.update s j (tapeDrop 1 (s j))))
      (Measure.pi (fun i => Tier2.tapeMeasure (p i)))
      ((bernoulliMeasure true false (p j)).prod (Measure.pi (fun i => Tier2.tapeMeasure (p i)))) := by
  cases m with
  | zero => exact Fin.elim0 j
  | succ m =>
    let μ (i : Fin (m+1)) := Tier2.tapeMeasure (p i)
    let ν := Measure.pi (fun k : Fin m => μ (j.succAbove k))
    let β := bernoulliMeasure true false (p j)
    let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m+1) => ℕ → Bool) j
    have he : MeasurePreserving e (Measure.pi μ) ((μ j).prod ν) :=
      measurePreserving_piFinSuccAbove μ j
    have hsplit := (tape_head_drop_preserving (p j)).prod (MeasurePreserving.id ν)
    have hassoc := measurePreserving_prodAssoc β (μ j) ν
    have hjoin := (MeasurePreserving.id β).prod he.symm
    have hall := hjoin.comp (hassoc.comp (hsplit.comp he))
    convert hall using 1
    funext s
    apply Prod.ext
    · rfl
    · exact (Fin.insertNth_removeNth j (tapeDrop 1 (s j)) s).symm

end ThresholdHC.CriticalEntropy

open MeasureTheory ProbabilityTheory Set
namespace ThresholdHC.CriticalEntropy
open ThresholdHC ThresholdHC.Proofs

theorem histBefore_cons_zero {n : ℕ} (o : Option Bool) (w : Fin n → Option Bool) :
    histBefore (Fin.cons o w) 0 = [] := by simp [histBefore]

theorem histBefore_cons_succ {n : ℕ} (o : Option Bool) (w : Fin n → Option Bool)
    (t : Fin n) :
    histBefore (Fin.cons o w) t.succ = o.toList ++ histBefore w t := by
  unfold histBefore
  have hf : (fun j : Fin (t.val+1) =>
      (Fin.cons o w : Fin (n+1) → Option Bool) (Fin.castLE t.succ.isLt.le j)) =
      Fin.cons o (fun j : Fin t.val => w (Fin.castLE t.isLt.le j)) := by
    funext j
    refine Fin.cases ?_ (fun k => ?_) j <;> rfl
  calc
    _ = (List.ofFn (Fin.cons o (fun j : Fin t.val => w (Fin.castLE t.isLt.le j)))).filterMap id :=
      congrArg (fun f : Fin (t.val+1) → Option Bool => (List.ofFn f).filterMap id) hf
    _ = _ := by rw [List.ofFn_cons]; cases o <;> rfl

theorem pathProb_cons {m n : ℕ} (pol : List Bool → Option (Fin m)) (p : Fin m → ℝ)
    (o : Option Bool) (w : Fin n → Option Bool) :
    pathProb pol p (Fin.cons o w) = stepProb pol p [] o *
      pathProb (fun xs => pol (o.toList ++ xs)) p w := by
  change (∏ t : Fin (n+1), stepProb pol p (histBefore (Fin.cons o w) t)
    ((Fin.cons o w : Fin (n+1) → Option Bool) t)) = _
  rw [Fin.prod_univ_succ]
  simp only [histBefore_cons_zero,histBefore_cons_succ,Fin.cons_zero,Fin.cons_succ]
  rfl

theorem pathProb_initial_stop {m n : ℕ} (pol : List Bool → Option (Fin m)) (p : Fin m → ℝ)
    (hp : pol [] = none) (w : Fin n → Option Bool) :
    pathProb pol p w = if w = (fun _ => none) then 1 else 0 := by
  classical
  induction n with
  | zero => simp [pathProb,Subsingleton.elim w (fun _ => none)]
  | succ n ih =>
    obtain ⟨o,v,rfl⟩ := Fin.exists_cons w
    rw [pathProb_cons]
    cases o with
    | none =>
      have he : (Fin.cons none v = (fun _ => (none : Option Bool))) ↔
          v = (fun _ => none) := by
        constructor
        · intro h; funext t; exact congrFun h t.succ
        · intro h; subst v; funext t; exact Fin.cases rfl (fun _ => rfl) t
      simpa only [stepProb,hp,Option.toList_none,List.nil_append,one_mul,he] using ih v
    | some b =>
      have hne : Fin.cons (some b) v ≠ (fun _ => (none : Option Bool)) := by
        intro h
        exact Option.some_ne_none b (congrFun h 0)
      simp [stepProb,hp,hne]

theorem sum_cons_word {n : ℕ} {M : Type} [AddCommMonoid M]
    (f : (Fin (n+1) → Option Bool) → M) :
    (∑ w, f w) = ∑ o : Option Bool, ∑ w : Fin n → Option Bool, f (Fin.cons o w) := by
  rw [← (Fin.consEquiv (fun _ : Fin (n+1) => Option Bool)).sum_comp]
  rw [Fintype.sum_prod_type]
  rfl

end ThresholdHC.CriticalEntropy
namespace ThresholdHC.CriticalEntropy
open MeasureTheory ProbabilityTheory Set ThresholdHC ThresholdHC.Proofs
open scoped ENNReal
local instance : MeasurableSpace (Option Bool) := ⊤

theorem measurable_populationSimulation_word {I : Type} [DecidableEq I]
    (n : ℕ) (pol : List Bool → Option I) :
    Measurable (fun s : I → ℕ → Bool => (populationSimulation pol n s).2) := by
  classical
  cases isEmpty_or_nonempty I with
  | inl h =>
    let := h
    exact measurable_of_countable _
  | inr h =>
    obtain ⟨i⟩ := h
    have hm := (measurable_localSimulation i n pol).snd.comp
      (measurable_id.prodMk (measurable_pi_apply i))
    have he (s : I → ℕ → Bool) : (localSimulation i pol n s (s i)).2 =
        (populationSimulation pol n s).2 := by
      rw [localSimulation_eq_population,Function.update_eq_self]
    simpa only [Function.comp_def,id_eq,he] using hm

theorem bernoulli_singleton_ofReal (p : unitInterval) (b : Bool) :
    bernoulliMeasure true false p {b} = ENNReal.ofReal (if b then (p : ℝ) else 1-(p : ℝ)) := by
  rw [← Tier2.bernoulli_real_singleton p b,measureReal_def,ENNReal.ofReal_toReal (measure_ne_top _ _)]

/-- Exact finite transcript law of the independent-tape simulation for fixed
Bernoulli parameters. No independence at an adaptive time is assumed. -/
theorem populationSimulation_lintegral {m : ℕ} (p : Fin m → unitInterval)
    (n : ℕ) (pol : List Bool → Option (Fin m)) (f : (Fin n → Option Bool) → ℝ≥0∞) :
    (∫⁻ s, f ((populationSimulation pol n s).2)
      ∂Measure.pi (fun i => Tier2.tapeMeasure (p i))) =
      ∑ w, ENNReal.ofReal (pathProb pol (fun i => (p i : ℝ)) w)*f w := by
  classical
  induction n generalizing pol with
  | zero =>
    simp [populationSimulation,pathProb]
    exact congrArg f (Subsingleton.elim _ _)
  | succ n ih =>
    cases hp : pol [] with
    | none =>
      simp_rw [pathProb_initial_stop pol (fun i => (p i : ℝ)) hp]
      simp [populationSimulation,hp,apply_ite]
    | some j =>
      let μ := Measure.pi (fun i => Tier2.tapeMeasure (p i))
      let β := bernoulliMeasure true false (p j)
      let g (z : Bool × (Fin m → ℕ → Bool)) : ℝ≥0∞ :=
        f (Fin.cons (some z.1) (populationSimulation (fun xs => pol (z.1::xs)) n z.2).2)
      have hgm : Measurable g := by
        apply measurable_from_prod_countable_right
        intro b
        exact (measurable_of_countable (fun w : Fin n → Option Bool =>
          f (Fin.cons (some b) w))).comp
            (measurable_populationSimulation_word n (fun xs => pol (b::xs)))
      have hcons (b : Bool) (w : Fin n → Option Bool) :
          ENNReal.ofReal (pathProb pol (fun i => (p i : ℝ)) (Fin.cons (some b) w)) =
          β {b}*ENNReal.ofReal (pathProb (fun xs => pol (b::xs)) (fun i => (p i : ℝ)) w) := by
        rw [pathProb_cons]
        dsimp only [β]
        rw [bernoulli_singleton_ofReal]
        cases b <;> simp only [stepProb,hp,Option.toList_some,List.singleton_append,
          Bool.false_eq_true,ite_false,ite_true]
        · rw [ENNReal.ofReal_mul (sub_nonneg.mpr (p j).property.2)]
        · rw [ENNReal.ofReal_mul (p j).property.1]
      have hzero (w : Fin n → Option Bool) :
          pathProb pol (fun i => (p i : ℝ)) (Fin.cons none w) = 0 := by
        simp [pathProb_cons,stepProb,hp]
      calc
        _ = ∫⁻ s, g (s j 0,Function.update s j (tapeDrop 1 (s j))) ∂μ := by
          apply lintegral_congr
          intro s
          simp only [populationSimulation,hp,g]
        _ = ∫⁻ z, g z ∂β.prod μ := (array_head_drop_preserving p j).lintegral_comp hgm
        _ = ∑ b : Bool, β {b} *
            (∑ w : Fin n → Option Bool,
              ENNReal.ofReal (pathProb (fun xs => pol (b::xs)) (fun i => (p i : ℝ)) w)*
                f (Fin.cons (some b) w)) := by
          rw [lintegral_prod _ hgm.aemeasurable,lintegral_fintype]
          apply Finset.sum_congr rfl
          intro b hb
          rw [mul_comm]
          congr 1
          exact ih (fun xs => pol (b::xs)) (fun w => f (Fin.cons (some b) w))
        _ = _ := by
          rw [sum_cons_word,Fintype.sum_option]
          simp_rw [hzero,ENNReal.ofReal_zero,zero_mul,Finset.sum_const_zero,zero_add,hcons,
            mul_assoc,← Finset.mul_sum]

theorem populationSimulation_word_law {m : ℕ} (p : Fin m → unitInterval)
    (n : ℕ) (pol : List Bool → Option (Fin m)) :
    (Measure.pi (fun i => Tier2.tapeMeasure (p i))).map
      (fun s => (populationSimulation pol n s).2) =
      finiteWeightMeasure (pathProb pol (fun i => (p i : ℝ))) := by
  classical
  apply Measure.ext_of_singleton
  intro w
  have h := populationSimulation_lintegral p n pol
    (({w} : Set (Fin n → Option Bool)).indicator (fun _ => 1))
  rw [← lintegral_map (measurable_const.indicator (measurableSet_singleton w))
    (measurable_populationSimulation_word n pol),lintegral_indicator_fun_one (measurableSet_singleton w)] at h
  rw [finiteWeightMeasure_singleton]
  simpa [Set.indicator_apply] using h

end ThresholdHC.CriticalEntropy
namespace ThresholdHC.CriticalEntropy
open MeasureTheory ProbabilityTheory Set ThresholdHC ThresholdHC.Proofs
open scoped ENNReal
local instance : MeasurableSpace (Option Bool) := ⊤

theorem measurable_uniformTapeArray {I : Type} :
    Measurable (fun z : (I → unitInterval) × (I → ℕ → ℝ) =>
      fun i => uniformCoinTape (z.1 i) (z.2 i)) := by
  apply Measurable.of_eval
  intro i
  have hi : Measurable (fun z : (I → unitInterval) × (I → ℕ → ℝ) => (z.1 i,z.2 i)) :=
    ((measurable_pi_apply i).comp measurable_fst).prodMk
      ((measurable_pi_apply i).comp measurable_snd)
  exact measurable_uniformCoinTape.comp hi

def parameterTapeLaw (κ : Measure unitInterval) : Measure (ℕ → Bool) :=
  (κ.prod uniformTapeMeasure).map (fun z => uniformCoinTape z.1 z.2)

instance parameterTapeLaw_probability (κ : Measure unitInterval) [IsProbabilityMeasure κ] :
    IsProbabilityMeasure (parameterTapeLaw κ) :=
  (Measure.isProbabilityMeasure_map_iff measurable_uniformCoinTape.aemeasurable).2 inferInstance

theorem parameterTapeLaw_array_map {I : Type} [Fintype I]
    (κ : I → Measure unitInterval) [∀ i, IsProbabilityMeasure (κ i)] :
    ((Measure.pi κ).prod (Measure.pi (fun _ : I => uniformTapeMeasure))).map
      (fun z i => uniformCoinTape (z.1 i) (z.2 i)) =
      Measure.pi (fun i => parameterTapeLaw (κ i)) := by
  let e := MeasurableEquiv.arrowProdEquivProdArrow unitInterval (ℕ → ℝ) I
  have he := measurePreserving_arrowProdEquivProdArrow unitInterval (ℕ → ℝ) I
    κ (fun _ => uniformTapeMeasure)
  have hmap := Measure.pi_map_pi (μ := fun i => (κ i).prod uniformTapeMeasure)
    (fun _ => measurable_uniformCoinTape.aemeasurable)
  rw [← he.map_eq,Measure.map_map measurable_uniformTapeArray he.measurable]
  exact hmap

theorem fixed_parameter_uniform_array_lintegral {m : ℕ} (p : Fin m → unitInterval)
    (n : ℕ) (pol : List Bool → Option (Fin m)) (f : (Fin n → Option Bool) → ℝ≥0∞) :
    (∫⁻ u : Fin m → ℕ → ℝ,
      f ((populationSimulation pol n (fun i => uniformCoinTape (p i) (u i))).2)
      ∂Measure.pi (fun _ => uniformTapeMeasure)) =
      ∑ w, ENNReal.ofReal (pathProb pol (fun i => (p i : ℝ)) w)*f w := by
  have hm (i : Fin m) : Measurable (uniformCoinTape (p i)) :=
    measurable_uniformCoinTape.comp (measurable_const.prodMk measurable_id)
  have hmap : (Measure.pi (fun _ : Fin m => uniformTapeMeasure)).map
      (fun u i => uniformCoinTape (p i) (u i)) =
      Measure.pi (fun i => Tier2.tapeMeasure (p i)) := by
    rw [Measure.pi_map_pi (fun i => (hm i).aemeasurable)]
    simp_rw [uniformCoinTape_map]
  rw [← populationSimulation_lintegral p n pol f,← hmap]
  exact (lintegral_map ((measurable_of_countable f).comp (measurable_populationSimulation_word n pol))
    (measurable_uniformTapeArray.comp (measurable_const.prodMk measurable_id))).symm

theorem parameterTapeLaw_population_lintegral {m : ℕ}
    (κ : Fin m → Measure unitInterval) [∀ i, IsProbabilityMeasure (κ i)]
    (n : ℕ) (pol : List Bool → Option (Fin m)) (f : (Fin n → Option Bool) → ℝ≥0∞) :
    (∫⁻ s, f ((populationSimulation pol n s).2) ∂Measure.pi (fun i => parameterTapeLaw (κ i))) =
      ∫⁻ p : Fin m → unitInterval,
        (∑ w, ENNReal.ofReal (pathProb pol (fun i => (p i : ℝ)) w)*f w) ∂Measure.pi κ := by
  have hm : Measurable (fun z : (Fin m → unitInterval) × (Fin m → ℕ → ℝ) =>
      f ((populationSimulation pol n (fun i => uniformCoinTape (z.1 i) (z.2 i))).2)) :=
    ((measurable_of_countable f).comp (measurable_populationSimulation_word n pol)).comp
      measurable_uniformTapeArray
  have hF : Measurable (fun s => f ((populationSimulation pol n s).2)) :=
    (measurable_of_countable f).comp (measurable_populationSimulation_word n pol)
  rw [← parameterTapeLaw_array_map κ,lintegral_map hF measurable_uniformTapeArray,
    lintegral_prod _ hm.aemeasurable]
  exact lintegral_congr (fun p => fixed_parameter_uniform_array_lintegral p n pol f)

end ThresholdHC.CriticalEntropy
namespace ThresholdHC.CriticalEntropy
open MeasureTheory ProbabilityTheory Set ThresholdHC ThresholdHC.Proofs
open scoped ENNReal
local instance : MeasurableSpace (Option Bool) := ⊤

theorem measurable_pathProb_parameters {m n : ℕ}
    (pol : List Bool → Option (Fin m)) (w : Fin n → Option Bool) :
    Measurable (fun p : Fin m → unitInterval => pathProb pol (fun i => (p i : ℝ)) w) := by
  unfold pathProb
  apply Finset.measurable_prod
  intro t ht
  cases pol (histBefore w t) with
  | none => cases w t <;> exact measurable_const
  | some i =>
    cases w t with
    | none => exact measurable_const
    | some b =>
      cases b
      · exact measurable_const.sub (measurable_subtype_coe.comp (measurable_pi_apply i))
      · exact measurable_subtype_coe.comp (measurable_pi_apply i)

theorem pathProb_parameters_bounds {m n : ℕ}
    (pol : List Bool → Option (Fin m)) (w : Fin n → Option Bool) (p : Fin m → unitInterval) :
    0 ≤ pathProb pol (fun i => (p i : ℝ)) w ∧ pathProb pol (fun i => (p i : ℝ)) w ≤ 1 := by
  have hn (v : Fin n → Option Bool) := pathProb_nonneg pol (fun i => (p i : ℝ))
    (fun i => (p i).property) v
  refine ⟨hn w,?_⟩
  have h := Finset.single_le_sum (fun v (_ : v ∈ Finset.univ) => hn v) (Finset.mem_univ w)
  simpa only [pathProb_total] using h

theorem integrable_pathProb_parameters {m n : ℕ}
    (κ : Fin m → Measure unitInterval) [∀ i, IsProbabilityMeasure (κ i)]
    (pol : List Bool → Option (Fin m)) (w : Fin n → Option Bool) :
    Integrable (fun p : Fin m → unitInterval => pathProb pol (fun i => (p i : ℝ)) w) (Measure.pi κ) :=
  ThresholdHC.Tier5.integrable_of_abs_bound _ _ (measurable_pathProb_parameters pol w) 1
    (fun p => by rw [abs_of_nonneg (pathProb_parameters_bounds pol w p).1];
                 exact (pathProb_parameters_bounds pol w p).2)

theorem parameterTapeLaw_population_word_law {m : ℕ}
    (κ : Fin m → Measure unitInterval) [∀ i, IsProbabilityMeasure (κ i)]
    (n : ℕ) (pol : List Bool → Option (Fin m)) :
    (Measure.pi (fun i => parameterTapeLaw (κ i))).map
      (fun s => (populationSimulation pol n s).2) =
      finiteWeightMeasure (fun w => ∫ p : Fin m → unitInterval,
        pathProb pol (fun i => (p i : ℝ)) w ∂Measure.pi κ) := by
  classical
  apply Measure.ext_of_singleton
  intro w
  have h := parameterTapeLaw_population_lintegral κ n pol
    (({w} : Set (Fin n → Option Bool)).indicator (fun _ => 1))
  rw [← lintegral_map (measurable_const.indicator (measurableSet_singleton w))
    (measurable_populationSimulation_word n pol),lintegral_indicator_fun_one (measurableSet_singleton w)] at h
  simp only [Set.indicator_apply,mem_singleton_iff,mul_ite,mul_one,mul_zero,
    Finset.sum_ite_eq',Finset.mem_univ,ite_true] at h
  rw [finiteWeightMeasure_singleton,h]
  exact (ofReal_integral_eq_lintegral_ofReal (integrable_pathProb_parameters κ pol w)
    (ae_of_all _ (fun p => (pathProb_parameters_bounds pol w p).1))).symm

theorem parameter_pathProb_factor {m n : ℕ}
    (κ : Fin m → Measure unitInterval) [∀ i, IsProbabilityMeasure (κ i)]
    (pol : List Bool → Option (Fin m)) (w : Fin n → Option Bool) :
    (∫ p : Fin m → unitInterval, pathProb pol (fun i => (p i : ℝ)) w ∂Measure.pi κ) =
      pathValidity pol w * ∏ i, ∫ p : unitInterval, coinLike pol w i p ∂κ i := by
  simp_rw [pathProb_factor]
  rw [integral_const_mul]
  congr 1
  exact integral_fintype_prod_eq_prod (fun (i : Fin m) (p : unitInterval) => coinLike pol w i p)

end ThresholdHC.CriticalEntropy
namespace ThresholdHC.CriticalEntropy
open MeasureTheory ProbabilityTheory Set ThresholdHC ThresholdHC.Proofs
open scoped ENNReal
local instance : MeasurableSpace (Option Bool) := ⊤

def populationParameterLaw {D : Type} [MeasurableSpace D]
    (μ : Measure D) (p₀ p₁ q : D → unitInterval) : Measure unitInterval :=
  (μ.prod uniformUnitMeasure).map (mixtureParameter p₀ p₁ q)

theorem populationParameterLaw_probability {D : Type} [MeasurableSpace D]
    (μ : Measure D) [IsProbabilityMeasure μ] (p₀ p₁ q : D → unitInterval)
    (h₀ : Measurable p₀) (h₁ : Measurable p₁) (hq : Measurable q) :
    IsProbabilityMeasure (populationParameterLaw μ p₀ p₁ q) :=
  (Measure.isProbabilityMeasure_map_iff
    (measurable_mixtureParameter p₀ p₁ q h₀ h₁ hq).aemeasurable).2 inferInstance

theorem populationParameterLaw_integral {D : Type} [MeasurableSpace D]
    (μ : Measure D) [IsProbabilityMeasure μ] (p₀ p₁ q : D → unitInterval)
    (h₀ : Measurable p₀) (h₁ : Measurable p₁) (hq : Measurable q)
    (F : unitInterval → ℝ) (hF : Measurable F) (M : ℝ) (hbound : ∀ p, |F p| ≤ M) :
    (∫ p, F p ∂populationParameterLaw μ p₀ p₁ q) =
      ∫ d, (q d : ℝ)*F (p₁ d)+(1-(q d : ℝ))*F (p₀ d) ∂μ := by
  have hm := measurable_mixtureParameter p₀ p₁ q h₀ h₁ hq
  have hi : Integrable (fun z => F (mixtureParameter p₀ p₁ q z)) (μ.prod uniformUnitMeasure) :=
    ThresholdHC.Tier5.integrable_of_abs_bound _ _ (hF.comp hm) M (fun _ => hbound _)
  rw [populationParameterLaw,integral_map hm.aemeasurable hF.aestronglyMeasurable,integral_prod _ hi]
  apply integral_congr_ae
  exact ae_of_all _ (fun d => mixtureParameter_integral p₀ p₁ q d F hF)

/-- The full independent-tape simulator has exactly the original integrated
adaptive transcript law for coin-specific latent sign laws (including hybrids).
Parameter identities need hold only on the actual magnitude support. -/
theorem population_tape_word_law {D : Type} [MeasurableSpace D] {m n : ℕ}
    (μ : Measure D) [IsProbabilityMeasure μ] (p₀ p₁ : D → unitInterval)
    (h₀ : Measurable p₀) (h₁ : Measurable p₁)
    (q : Fin m → D → unitInterval) (hq : ∀ i, Measurable (q i))
    (d : D → ℝ) (h₀d : ∀ᵐ x ∂μ, (p₀ x : ℝ) = 1/2-d x)
    (h₁d : ∀ᵐ x ∂μ, (p₁ x : ℝ) = 1/2+d x)
    (pol : List Bool → Option (Fin m)) :
    (Measure.pi (fun i => parameterTapeLaw (populationParameterLaw μ p₀ p₁ (q i)))).map
      (fun s => (populationSimulation pol n s).2) =
      finiteWeightMeasure (finitePopulationWeight (n := n) μ pol d (fun i x => (q i x : ℝ))) := by
  let κ (i : Fin m) := populationParameterLaw μ p₀ p₁ (q i)
  let (i : Fin m) : IsProbabilityMeasure (κ i) :=
    populationParameterLaw_probability μ p₀ p₁ (q i) h₀ h₁ (hq i)
  rw [parameterTapeLaw_population_word_law κ n pol]
  congr 1
  funext w
  rw [parameter_pathProb_factor,finite_population_factor]
  congr 1
  apply Finset.prod_congr rfl
  intro i hi
  have hF : Measurable (fun p : unitInterval => coinLike pol w i p) :=
    (continuous_coinLike pol w i).measurable.comp measurable_subtype_coe
  rw [populationParameterLaw_integral μ p₀ p₁ (q i) h₀ h₁ (hq i) _ hF 1
    (fun p => by rw [abs_of_nonneg (coinLike_nonneg pol w i p.property.1 p.property.2)];
                 exact coinLike_le_one pol w i p p.property.1 p.property.2)]
  apply integral_congr_ae
  filter_upwards [h₀d,h₁d] with x h₀x h₁x
  rw [h₀x,h₁x]

end ThresholdHC.CriticalEntropy
