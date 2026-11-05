import ThresholdHC.ContinuousObserved.Word

noncomputable section
open MeasureTheory
namespace ThresholdHC.ContinuousObserved
open ThresholdHC ThresholdHC.Tier3 ThresholdHC.CriticalEntropy

theorem measurable_noisyWord {N : ℕ} (D : QueryDesign N)
    (c : List Bool → Bool) (q : List Bool → unitInterval) (n : ℕ) :
    Measurable (fun z : (ℕ → ℝ) × (Fin N → ℕ → Bool) => noisyWord D c q n z.1 z.2) := by
  induction n generalizing c q with
  | zero => exact measurable_const
  | succ n ih =>
    by_cases hc : c [] = true
    · let j := D.cell (q [])
      have ht : Measurable (fun z : (ℕ → ℝ) × (Fin N → ℕ → Bool) =>
          (uniformTail z.1,Function.update z.2 j (tapeDrop 1 (z.2 j)))) :=
        (measurable_uniformTail.comp measurable_fst).prodMk
          (measurable_update'.comp (measurable_snd.prodMk
            ((measurable_tapeDrop 1).comp ((measurable_pi_apply j).comp measurable_snd))))
      let f (b : Bool) (z : (ℕ → ℝ) × (Fin N → ℕ → Bool)) : Prefix (n + 1) :=
        Fin.cons (some b) (noisyWord D (fun ys => c (b :: ys)) (fun ys => q (b :: ys)) n
          (uniformTail z.1) (Function.update z.2 j (tapeDrop 1 (z.2 j))))
      have hf (b : Bool) : Measurable (f b) :=
        (measurable_of_countable (fun w : Prefix n => (Fin.cons (some b) w : Prefix (n + 1)))).comp
          ((ih (fun ys => c (b :: ys)) (fun ys => q (b :: ys))).comp ht)
      have hm : Measurable (fun z : Bool × ((ℕ → ℝ) × (Fin N → ℕ → Bool)) => f z.1 z.2) :=
        measurable_from_prod_countable_right hf
      have hb : Measurable (fun z : (ℕ → ℝ) × (Fin N → ℕ → Bool) =>
          stepNoise D q z.1 [] (z.2 j 0)) := by
        have hn : Measurable (fun z : (ℕ → ℝ) × (Fin N → ℕ → Bool) =>
            uniformCoinFlip (ThresholdHC.ObservedState.noiseRate (D.cap j) (D.gap (q [])) (D.bound _)) (z.1 0)) :=
          measurable_uniformCoinFlip.comp
            (measurable_const.prodMk ((measurable_pi_apply 0).comp measurable_fst))
        have hr : Measurable (fun z : (ℕ → ℝ) × (Fin N → ℕ → Bool) => z.2 j 0) :=
          (measurable_pi_apply 0).comp ((measurable_pi_apply j).comp measurable_snd)
        exact (measurable_of_countable (fun z : Bool × Bool => Bool.xor z.1 z.2)).comp (hr.prodMk hn)
      have h := hm.comp (hb.prodMk measurable_id)
      simpa only [noisyWord,hc,ite_true,f,j,Function.comp_def,id_eq] using h
    · simp [noisyWord,hc]

end ThresholdHC.ContinuousObserved
