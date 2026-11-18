import ThresholdHC.SharpRMS.SmallBudget
import ThresholdHC.Tier5.PriorRatio
import ThresholdHC.Tier5.CreationBase
import ThresholdHC.Tier3.StoppingBase

/-! A uniform-prior Bayes risk inequality for the repository's actual finite
adaptive transcripts, with an arbitrary gap at every coin label. -/
noncomputable section
namespace ThresholdHC.SharpRMS
open MeasureTheory Set Proofs Tier3 Tier5

private def moments {I : Type} (a b : I → ℝ) (S : Finset I) (h l : ℕ)
    (f : ℝ → ℝ) := ∫ p in (0:ℝ)..1,
    leafWeight h l p * (∏ i ∈ S, (p*a i+(1-p)*b i)) * f p

private theorem moments_insert {I : Type} [DecidableEq I] (a b : I → ℝ) (S : Finset I)
    (i : I) (hi : i ∉ S) (h l : ℕ) (f : ℝ → ℝ) (hf : Continuous f) :
    moments a b (insert i S) h l f = a i*moments a b S (h+1) l f + b i*moments a b S h (l+1) f := by
  let g := fun (H L : ℕ) (p : ℝ) => leafWeight H L p * (∏ j ∈ S, (p*a j+(1-p)*b j)) * f p
  have hg (H L) : Continuous (g H L) := by dsimp [g,leafWeight]; fun_prop
  have split (p : ℝ) : leafWeight h l p*(∏ j ∈ insert i S, (p*a j+(1-p)*b j))*f p =
      a i*g (h+1) l p+b i*g h (l+1) p := by
    rw [Finset.prod_insert hi]
    dsimp [g,leafWeight]
    simp only [pow_succ]
    ring
  unfold moments
  simp_rw [split]
  have h₁ : IntervalIntegrable (fun p => a i*g (h+1) l p) volume 0 1 :=
    (continuous_const.mul (hg (h+1) l)).intervalIntegrable ..
  have h₂ : IntervalIntegrable (fun p => b i*g h (l+1) p) volume 0 1 :=
    (continuous_const.mul (hg h (l+1))).intervalIntegrable ..
  rw [intervalIntegral.integral_add h₁ h₂,intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul]

private def payoff (x T p : ℝ) := (x-p)^2-(10-T)/36*(p*(1-p))

private theorem moments_nonneg {I : Type} [DecidableEq I] (a b : I → ℝ)
    (ha : ∀ i, 0 ≤ a i) (hb : ∀ i, 0 ≤ b i) (S : Finset I)
    (h l : ℕ) (x T : ℝ) (hT : (h:ℝ)+l+S.card ≤ T) :
    0 ≤ moments a b S h l (payoff x T) := by
  induction S using Finset.induction_on generalizing h l with
  | empty =>
    simp only [Finset.card_empty,Nat.cast_zero,add_zero] at hT
    have hw (p : ℝ) (hp : p ∈ Icc 0 1) : 0 ≤ leafWeight h l p :=
      mul_nonneg (pow_nonneg hp.1 _) (pow_nonneg (sub_nonneg.mpr hp.2) _)
    have hpen := intervalIntegral.integral_mono_on (μ := volume) (a := (0:ℝ)) (b := 1) (by norm_num)
      (f := fun p => leafWeight h l p * ((10-T)/36*(p*(1-p))))
      (g := fun p => leafWeight h l p * ((10-(h+l:ℝ))/36*(p*(1-p))))
      (Continuous.intervalIntegrable (by unfold leafWeight; fun_prop) ..)
      (Continuous.intervalIntegrable (by unfold leafWeight; fun_prop) ..)
      (fun p hp => mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (by linarith)
        (mul_nonneg hp.1 (sub_nonneg.mpr hp.2))) (hw p hp))
    simp only [moments,Finset.prod_empty,mul_one,payoff]
    simp_rw [mul_sub (leafWeight h l _) ((x-_)^2)]
    rw [intervalIntegral.integral_sub (Continuous.intervalIntegrable (by unfold leafWeight; fun_prop) ..)
      (Continuous.intervalIntegrable (by unfold leafWeight; fun_prop) ..)]
    exact sub_nonneg.mpr (hpen.trans (leaf_risk_work h l x))
  | insert i S hi ih =>
    rw [Finset.card_insert_of_notMem hi,Nat.cast_add_one] at hT
    rw [moments_insert a b S i hi h l _ (by unfold payoff; fun_prop)]
    exact add_nonneg (mul_nonneg (ha i) (ih (h+1) l (by push_cast; linarith)))
      (mul_nonneg (hb i) (ih h (l+1) (by push_cast; linarith)))

private theorem finite_leaf {m n : ℕ} (pol : List Bool → Option (Fin m)) (d : Fin m → ℝ)
    (hd : ∀ i, 0 ≤ d i ∧ d i ≤ 1/2) (w : Prefix n) (x : ℝ) :
    0 ≤ ∫ p in (0:ℝ)..1, transcriptLaw pol d (fun _ => p) w * payoff x (workOf w) p := by
  classical
  by_cases valid : ∀ k, (w k).isSome = (pol (histBefore w k)).isSome
  · let paid := Finset.univ.filter fun k => (w k).isSome = true
    let S := queriedCoins pol w
    have hsub : S ⊆ paid.biUnion (fun k => (pol (histBefore w k)).toFinset) := by
      intro i hi
      obtain ⟨k,_,hk⟩ := Finset.mem_biUnion.mp hi
      apply Finset.mem_biUnion.mpr
      refine ⟨k,Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_⟩,hk⟩
      rw [valid]
      cases hh : pol (histBefore w k) <;> simp_all
    have hcard := (Finset.card_le_card hsub).trans (Finset.card_biUnion_le_card_mul paid
      (fun k => (pol (histBefore w k)).toFinset) 1 (fun k _ => by cases pol (histBefore w k) <;> simp))
    have ht : (S.card:ℝ) ≤ workOf w := by
      simp only [mul_one] at hcard
      change (S.card:ℝ) ≤ (paid.card:ℝ)
      exact_mod_cast hcard
    let a := fun i => coinLike pol w i (1/2+d i)
    let b := fun i => coinLike pol w i (1/2-d i)
    have ha i : 0 ≤ a i := coinLike_nonneg _ _ _ (by linarith [(hd i).1]) (by linarith [(hd i).2])
    have hb i : 0 ≤ b i := coinLike_nonneg _ _ _ (by linarith [(hd i).2]) (by linarith [(hd i).1])
    have eqw (p : ℝ) : transcriptLaw pol d (fun _ => p) w =
        pathValidity pol w * ∏ i ∈ S, (p*a i+(1-p)*b i) := by
      rw [transcriptLaw_factor]
      congr 1
      symm
      apply Finset.prod_subset (Finset.subset_univ S)
      intro i _ hi
      simp [a,b,coinLike_eq_one_of_not_queried pol w i hi]
    have hf := moments_nonneg a b ha hb S 0 0 x (workOf w) (by simpa using ht)
    simp only [moments,leafWeight,pow_zero,one_mul] at hf
    simp_rw [eqw,mul_assoc,intervalIntegral.integral_const_mul]
    exact mul_nonneg (pathValidity_nonneg pol w) hf
  · push Not at valid
    obtain ⟨k,hk⟩ := valid
    simp only [transcriptLaw_zero_of_invalid pol d _ w k hk,zero_mul,intervalIntegral.integral_zero,le_refl]

/-- Each adaptive word obeys the small-budget tradeoff. No common-gap or
finite ambient coin-count assumption is needed. -/
theorem creation_leaf_risk_work {n : ℕ} (pol : List Bool → Option ℕ) (d : ℕ → ℝ)
    (hd : ∀ i, 0 ≤ d i ∧ d i ≤ 1/2) (w : Prefix n) (x : ℝ) :
    0 ≤ ∫ p in (0:ℝ)..1, creationLaw pol d (fun _=>p) w *
      ((x-p)^2 - (10-workOf w)/36*(p*(1-p))) :=
  finite_leaf (capPolicy (coinCap n pol) pol) _ (fun i => hd i.val) w x

end ThresholdHC.SharpRMS
