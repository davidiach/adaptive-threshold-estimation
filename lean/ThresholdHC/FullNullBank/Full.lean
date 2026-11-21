import ThresholdHC.FullNullBank.Level

/-! The targets of `ThresholdHC.FullNullBank`: the bank that evaluates the
exact null mixture of `z0 delta_0 + (1 - z0) eta`, the fair-coin likelihood
included, is upward in the flips, obeys Ville's bound under the full null, has
integrated false positives at most `u` on the positive part, and has the
known-law work bounds on one coin with the envelope `z0 + threePieceEnvelope`;
and its level race under a true law coupled above the reference has error at
most `levelAccuracy rho l` and work at most the known-law level price when
`z0 + zeta(all) <= rho`. -/

noncomputable section
open MeasureTheory

namespace ThresholdHC.FullNullBank

theorem full_null_bank : FullNullBankStatement := by
  intro z₀ η _ weights hw hz0 hz1
  refine ⟨fun u => fullNullBankTest_upward z₀ η weights u,
    fun u => fullNull_bank_error z₀ η weights hw u,
    fun u hu => fullNull_integrated_false_positive z₀ η weights hw hz1.le hu, ?_⟩
  intro σ τ ζ _ _ _ hdesign hσ hτ ε ρ hε hε1 hρ j L hwj hwj1 d₀ d hd h
  exact ⟨fullNull_positive_work hz0 hz1.le η σ τ ζ hdesign hσ hτ weights hε hε1 hρ j L hwj hwj1
      hd h,
    race_negative_work_of_le _ weights hε hε1 j L hwj hwj1 hd h⟩

theorem full_null_level : FullNullLevelStatement := by
  intro z₀ η _ hz0 hz1 π _ hup href μ₀ _ ρ hρ q hq
  refine ⟨?_, ?_⟩
  · intro ν ζ _ _ hdesign weights hw l k hk hz
    exact fullNull_level_error hz1 η ν ζ hdesign π hup href μ₀ weights hw hρ q hq l k hk hz
  · intro σ τ ζ _ _ _ hdesign t N ht hs hN hτ hz l L
    exact fullNull_three_piece_level_work hz0 hz1.le η σ τ ζ hdesign π hup href μ₀ ht hs hN hτ
      hρ hz q hq l L

end ThresholdHC.FullNullBank
