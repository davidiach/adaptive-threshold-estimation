import SharpWordSimulation

/-! Exact simulation of heterogeneous, interleaved finite transcripts.
One observation of the designated source label is used per target flip. -/
noncomputable section
namespace ThresholdHC.SharpRMS
open Proofs Tier3 Tier5

def tally {m n : ℕ} (pol : List Bool → Option (Fin m)) (w : Prefix n) (i : Fin m) (b : Bool) : ℕ :=
  ∑ j, if pol (histBefore w j)=some i ∧ w j=some b then 1 else 0

private theorem coin_word {m n : ℕ} (pol : List Bool → Option (Fin m)) (w : Prefix n)
    (valid : ∀ j, (w j).isSome=(pol (histBefore w j)).isSome) (i : Fin m) (p : ℝ) :
    coinLike pol w i p = wordMass p (tally pol w i true) (tally pol w i false) := by
  unfold wordMass tally coinLike
  rw [← Finset.prod_pow_eq_pow_sum,← Finset.prod_pow_eq_pow_sum,← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro j _
  by_cases h : pol (histBefore w j)=some i
  · have ok := valid j
    cases hw : w j with
    | none => simp [hw,h] at ok
    | some o => cases o <;> simp [h,obsProb]
  · simp [h]

def signBit (b : Bool) : ℝ := if b then 1 else -1

/-- Conditional probability after marginalizing one source flip. The channel
uses the local history of the queried label and is independent of its sign. -/
def simulatedStep {m n : ℕ} (pol : List Bool → Option (Fin m)) (a : Fin m → ℝ)
    (s : ℝ) (e : Fin m → Bool) (w : Prefix n) (o : Option Bool) : ℝ :=
  match pol (fullHist w), o with
  | none, none => 1
  | some i, some b =>
    let h := tally pol w i true
    let l := tally pol w i false
    let M := ((1+s*signBit (e i))/2)*channelMean (a i) s h l 1+
      ((1-s*signBit (e i))/2)*channelMean (a i) s h l (-1)
    (1+signBit b*M)/2
  | _, _ => 0

def simulatedPath {m : ℕ} (pol : List Bool → Option (Fin m)) (a : Fin m → ℝ)
    (s : ℝ) (e : Fin m → Bool) : {n : ℕ} → Prefix n → ℝ
  | 0, _ => 1
  | n+1, w => simulatedPath pol a s e (Fin.init w)*simulatedStep pol a s e (Fin.init w) (w (Fin.last n))

private theorem signBit_cases (e : Bool) : signBit e= -1 ∨ signBit e=1 := by cases e <;> simp [signBit]

theorem conditioned_path {m n : ℕ} (pol : List Bool → Option (Fin m)) (a : Fin m → ℝ)
    (s : ℝ) (ha : ∀ i, 0<a i ∧ a i≤1) (hs : 0<s) (e : Fin m → Bool) (w : Prefix n) :
    simulatedPath pol a s e w =
      transcriptLaw pol (fun i => a i/2) (fun i => conditionalPrior (min 1 (s/a i)) (e i)) w := by
  let d := fun i => a i/2
  let q := fun i => conditionalPrior (min 1 (s/a i)) (e i)
  induction n with
  | zero =>
    rw [transcriptLaw_factor]
    simp [simulatedPath,pathValidity,coinLike]
  | succ n ih =>
    rw [←Fin.snoc_init_self w]
    generalize Fin.init w = v
    generalize w (Fin.last n) = o
    simp only [simulatedPath,Fin.init_snoc,Fin.snoc_last,ih]
    change transcriptLaw pol d q v*simulatedStep pol a s e v o=transcriptLaw pol d q (Fin.snoc v o)
    by_cases valid : ∀ j, (v j).isSome=(pol (histBefore v j)).isSome
    · cases hi : pol (fullHist v) with
      | none => rw [transcriptLaw_stop pol d q v hi]; cases o <;> simp [simulatedStep,hi]
      | some i =>
        cases o with
        | none => simp [simulatedStep,hi,transcriptLaw_query_none pol d q v i hi]
        | some b =>
          let f := min 1 (s/a i)
          let h := tally pol v i true
          let l := tally pol v i false
          let E := signBit (e i)
          let M := ((1+s*E)/2)*channelMean (a i) s h l 1+((1-s*E)/2)*channelMean (a i) s h l (-1)
          let A := wordMass ((1+a i)/2) h l
          let B := wordMass ((1-a i)/2) h l
          have prior : q i=(1+f*E)/2 := by
            dsimp [q,conditionalPrior,E,signBit,f]
            cases e i <;> simp
            ring
          have plus : 1/2+d i=(1+a i)/2 := by dsimp [d]; ring
          have minus : 1/2-d i=(1-a i)/2 := by dsimp [d]; ring
          have hh := simulate_word_step (a i) s E (ha i).1 (ha i).2 hs h l (signBit_cases (e i))
          rw [transcriptLaw_query pol d q v i hi,transcriptLaw_split pol d q v i]
          simp only [coinMix,coin_word pol v valid,plus,minus,prior,show 1-(1+f*E)/2=(1-f*E)/2 by ring,simulatedStep,hi]
          change (_*(((1+f*E)/2)*A+((1-f*E)/2)*B))*((1+signBit b*M)/2) = _*_
          rw [mul_assoc]
          congr 1
          cases b with
          | false =>
            have down (p : ℝ) : wordMass p h (l+1)=wordMass p h l*(1-p) := by simp [wordMass,pow_succ]; ring
            have eq := hh.2
            change conditionalWord (a i) f E h (l+1)=conditionalWord (a i) f E h l*((1-M)/2) at eq
            simp only [conditionalWord,down] at eq
            dsimp [signBit,obsProb,A,B]
            linarith only [eq]
          | true =>
            have up (p : ℝ) : wordMass p (h+1) l=wordMass p h l*p := by simp [wordMass,pow_succ]; ring
            have eq := hh.1
            change conditionalWord (a i) f E (h+1) l=conditionalWord (a i) f E h l*((1+M)/2) at eq
            simp only [conditionalWord,up] at eq
            dsimp [signBit,obsProb,A,B]
            linarith only [eq]
    · push Not at valid
      obtain ⟨j,bad⟩ := valid
      have bad' : ((Fin.snoc v o : Prefix (n+1)) j.castSucc).isSome ≠ (pol (histBefore (Fin.snoc v o) j.castSucc)).isSome := by
        simpa only [Fin.snoc_castSucc,histBefore_snoc_castSucc] using bad
      rw [transcriptLaw_zero_of_invalid pol d q v j bad,
        transcriptLaw_zero_of_invalid pol d q (Fin.snoc v o) j.castSucc bad',zero_mul]

/-- Correctness of the simulated adaptive transcript after averaging the
independent source signs, simultaneously for all sign means t. -/
theorem adaptive_simulated_transcript {m n : ℕ} (pol : List Bool → Option (Fin m))
    (a : Fin m → ℝ) (s t : ℝ) (ha : ∀ i, 0<a i ∧ a i≤1) (hs : 0<s) (w : Prefix n) :
    (∑ e : Fin m → Bool, (∏ i, if e i then (1+t)/2 else (1-t)/2)*simulatedPath pol a s e w) =
      transcriptLaw pol (fun i => a i/2) (fun i => (1+t*min 1 (s/a i))/2) w := by
  simp_rw [conditioned_path pol a s ha hs]
  exact (signed_prefix_mixture pol _ _ t w).symm

end ThresholdHC.SharpRMS
