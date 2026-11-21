import ThresholdHC.LocalizationCounter.Counter
import ThresholdHC.LocalizationCounter.Noise

/-! Theorem `loc:thm:counter` and Proposition `loc:prop:noise` of the v6
appendix on localized rare-event scales (`paper/v6/appendix-localization.tex`).

The counterexample proof gives the explicit lower bound `ρ/40`, which implies the
stated `ρ/100`; see `Counter.lean`. The unbounded-factor statement follows from
it and `H ≤ 3ρ²` with `ρ₀ = 1/(400K)`. -/
noncomputable section
namespace ThresholdHC.LocalizationCounter

theorem counter_law_probability : CounterLawProbabilityStatement :=
  counterLaw_probability_proof

theorem counterexample : CounterexampleStatement := by
  intro ρ d hρ hρ1 hd μ _ hμ
  refine ⟨?_, counter_minimax_upper μ ρ _ hρ.le, ?_, ?_⟩
  · exact (ENNReal.ofReal_le_ofReal (by linarith)).trans
      (counter_minimax_lower ρ d hρ hρ1 hd μ hμ)
  · rw [hμ]; exact counter_heuristic_eq ρ d hρ hρ1 hd
  · rw [hμ]; exact counter_heuristic_le ρ d hρ hρ1 hd

theorem counter_unbounded : CounterUnboundedStatement := by
  intro K hK
  refine ⟨1/(400*K), by positivity, ?_⟩
  intro ρ d hρ hρ0 hρ1 hd μ _ hμ
  have hH := counter_heuristic_le ρ d hρ hρ1 hd
  rw [← hμ] at hH
  refine lt_of_lt_of_le ?_ (counter_minimax_lower ρ d hρ hρ1 hd μ hμ)
  rw [ENNReal.ofReal_lt_ofReal_iff (by positivity)]
  have hKρ : ρ * (400*K) ≤ 1 := (le_div_iff₀ (by positivity)).mp hρ0
  have hKH := mul_le_mul_of_nonneg_left hH hK.le
  nlinarith

theorem observable713_noise_floor : Observable713NoiseFloorStatement :=
  observable713_noise_floor_proof

theorem original_second_moment_floor : OriginalSecondMomentFloorStatement :=
  original_second_moment_floor_proof

theorem truncated_noise_floor : TruncatedNoiseFloorStatement :=
  truncated_noise_floor_proof

end ThresholdHC.LocalizationCounter
