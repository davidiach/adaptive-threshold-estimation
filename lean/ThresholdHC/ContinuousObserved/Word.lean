import ThresholdHC.ContinuousObserved.Prefix
import ThresholdHC.ContinuousObserved.Reduction
import ThresholdHC.ContinuousObserved.UniformTape

noncomputable section
namespace ThresholdHC.ContinuousObserved
open ThresholdHC ThresholdHC.Tier3 ThresholdHC.Tier6 ThresholdHC.ObservedState
open ThresholdHC.CriticalEntropy

def stepNoise {N : ℕ} (D : QueryDesign N) (q : List Bool → unitInterval)
    (v : ℕ → ℝ) (xs : List Bool) (b : Bool) : Bool :=
  Bool.xor b (uniformCoinFlip (noiseRate (D.cap (D.cell (q xs))) (D.gap (q xs)) (D.bound _))
    (v xs.length))

def rawPolicy {N : ℕ} (D : QueryDesign N) (c : List Bool → Bool)
    (q : List Bool → unitInterval) (v : ℕ → ℝ) (xs : List Bool) : Option (Fin N) :=
  let ys := decode (stepNoise D q v) xs
  if c ys then some (D.cell (q ys)) else none

theorem stepNoise_shift {N : ℕ} (D : QueryDesign N) (q : List Bool → unitInterval)
    (v : ℕ → ℝ) (a b : Bool) (xs : List Bool) :
    stepNoise D q v (a :: xs) b =
      stepNoise D (fun ys => q (a :: ys)) (uniformTail v) xs b := rfl

theorem rawPolicy_shift {N : ℕ} (D : QueryDesign N) (c : List Bool → Bool)
    (q : List Bool → unitInterval) (v : ℕ → ℝ) (b : Bool) (xs : List Bool) :
    rawPolicy D c q v (b :: xs) =
      rawPolicy D (fun ys => c (stepNoise D q v [] b :: ys))
        (fun ys => q (stepNoise D q v [] b :: ys)) (uniformTail v) xs := rfl

/-- A direct recursive execution using one raw cell observation and one
fresh independent noise value at each active step. -/
def noisyWord {N : ℕ} (D : QueryDesign N) (c : List Bool → Bool)
    (q : List Bool → unitInterval) :
    (n : ℕ) → (ℕ → ℝ) → (Fin N → ℕ → Bool) → Prefix n
  | 0, _, _ => Fin.elim0
  | n + 1, v, raw =>
    if c [] then
      let j := D.cell (q [])
      let b := stepNoise D q v [] (raw j 0)
      Fin.cons (some b) (noisyWord D (fun ys => c (b :: ys)) (fun ys => q (b :: ys)) n
        (uniformTail v) (Function.update raw j (tapeDrop 1 (raw j))))
    else fun _ => none

theorem noisyWord_decode {N : ℕ} (D : QueryDesign N) (c : List Bool → Bool)
    (q : List Bool → unitInterval) (n : ℕ) (v : ℕ → ℝ) (raw : Fin N → ℕ → Bool) :
    noisyWord D c q n v raw =
      decodePrefix (stepNoise D q v) (populationSimulation (rawPolicy D c q v) n raw).2 := by
  induction n generalizing c q v raw with
  | zero => exact Subsingleton.elim _ _
  | succ n ih =>
    cases hc : c [] with
    | false =>
      have hp : rawPolicy D c q v [] = none := by simp [rawPolicy,decode,hc]
      simp [noisyWord,hc,populationSimulation,hp,decodePrefix_none]
    | true =>
      have hp : rawPolicy D c q v [] = some (D.cell (q [])) := by simp [rawPolicy,decode,hc]
      rw [noisyWord]
      simp only [hc,ite_true,populationSimulation,hp,decodePrefix_cons_some]
      rw [ih]
      rfl

end ThresholdHC.ContinuousObserved
