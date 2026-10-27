import ThresholdHC.Proofs.Tier2.TranscriptLikelihood

noncomputable section
namespace ThresholdHC.Tier5
open ThresholdHC.Proofs

theorem histBefore_length_le {n : ℕ} (w : Fin n → Option Bool) (t : Fin n) :
    (histBefore w t).length ≤ t.val := by
  unfold histBefore
  exact (List.length_filterMap_le _ _).trans_eq List.length_ofFn

theorem transcriptLaw_unused_last {m n : ℕ}
    (pol : List Bool → Option (Fin m)) (pol' : List Bool → Option (Fin (m+1)))
    (d q : Fin (m+1) → ℝ) (w : Fin n → Option Bool)
    (hp : ∀ t : Fin n, pol' (histBefore w t) = (pol (histBefore w t)).map Fin.castSucc) :
    transcriptLaw pol' d q w =
      transcriptLaw pol (fun i => d i.castSucc) (fun i => q i.castSucc) w := by
  have hv : pathValidity pol' w = pathValidity pol w := by
    unfold pathValidity
    apply Finset.prod_congr rfl
    intro t ht
    rw [hp t]
    cases pol (histBefore w t) <;> simp
  have hc (i : Fin m) (p : ℝ) : coinLike pol' w i.castSucc p = coinLike pol w i p := by
    unfold coinLike
    apply Finset.prod_congr rfl
    intro t ht
    rw [hp t]
    cases he : pol (histBefore w t) with
    | none => simp
    | some j => simp
  have hz (p : ℝ) : coinLike pol' w (Fin.last m) p = 1 := by
    unfold coinLike
    apply Finset.prod_eq_one
    intro t ht
    rw [hp t]
    cases pol (histBefore w t) <;> simp
  rw [transcriptLaw_factor, transcriptLaw_factor, hv, Fin.prod_univ_castSucc]
  simp only [hc, hz]
  ring

end ThresholdHC.Tier5
