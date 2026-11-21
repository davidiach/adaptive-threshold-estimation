import ThresholdHC.ObservedState.StateModel

/-! Target statements for the Hoeffding replication count in the proof of the
finite-cell observable-state lower bound, `paper/v6/core.tex`, Proposition
`prop:outer` (Finite-cell observable-state lower bound).

The proof creates, for each rounded magnitude `d_j` of weight `w_j`, `M` cells of
lengths `w_j/M` with unknown fixed signs. The sum of squared target weights is
`∑_j w_j²/M ≤ 1/M`, so weighted Hoeffding gives
`P_±(|θ(s) - E_± θ(s)| > Δ/8) ≤ 2 exp(-MΔ²/32)`, and the proof chooses an integer
`M ≥ 32 Δ⁻² log(2/δ)`. The status note `paper/v6/appendix-finite-observed.tex`
(Appendix `app:finite-observed`) records that the checked construction of
`ThresholdHC.ObservedState.finite_observed_state_lower` uses the second-moment
condition `M⁻¹ ≤ δΔ²/16` and that the Hoeffding-based cell count remained a paper
bound. These statements check that count.

* `WeightedHoeffdingStatement`: weighted Hoeffding for the sign target
  `target w s = ∑ w_i 1[s_i]` under every product sign prior `signLaw q`, with the
  strict two-sided event and the bound `2 exp(-2r²/v)` for nonnegative weights,
  `v > 0`, `r ≥ 0` and `∑ w_i² ≤ v`.
* `ReplicationTailStatement`: the display of the proof. `∑ w² ≤ 1/M` gives the
  tail `2 exp(-MΔ²/32)` at radius `Δ/8`, and `M ≥ 32 Δ⁻² log(2/δ)` makes it at
  most `δ`.
* `HoeffdingConfidenceLowerStatement`: the finite-cell testing lower bound
  `ThresholdHC.ObservedState.finite_confidence_lower` with `0 ≤ w i` and the
  Hoeffding weight condition `32 log(2/δ) ∑ w² ≤ Δ²` in place of
  `∑ w² ≤ δΔ²/16`.
* `HoeffdingDesignLowerStatement`: every finite measurable cell design whose
  squared cell lengths meet the Hoeffding condition, in particular every design
  with `∑ w² ≤ 1/M` and `M ≥ 32 Δ⁻² log(2/δ)`, forces the lower bound
  `225 kl(1-2δ,2δ)/(128h²)` for every selected-state estimator that is valid to
  radius `Δ/4` with failure probability `δ` and whose expected work is uniformly
  at most `B`. Here `Δ` is the design's separation `cellDelta`.
* `HoeffdingFiniteObservedStatement`: the proposition with the paper's replicated
  construction. There are `N` labels with distinct common caps `c j` and weights
  `v j` summing to one, and `M` replicas per label. Cell `(j,k)` has cap `c j` and
  length `v j / M`, with `M = ⌈32 Δ⁻² log(2/δ)⌉₊` the least admissible integer.
  The design carries the envelope, the separation `Δ ≥ ω_μ(h)/8`, the tail
  bound `2 exp(-MΔ²/32) ≤ δ` and the lower bound.

The rounding is the checked `finite_upward_rounding` (raise to `h`, then a finite
grid with distortion two) rather than the literal grid `h,2h,4h,…`, as for
`finite_observed_state_lower`. The proofs are in the other modules of this
directory. -/
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace ThresholdHC.ObservedHoeffding
open ThresholdHC ThresholdHC.Tier3 ThresholdHC.Tier6 ThresholdHC.ObservedState

/-- Weighted Hoeffding for the sign target under a product sign prior. -/
def WeightedHoeffdingStatement : Prop :=
  ∀ {I : Type} [Fintype I] (q : I → unitInterval) (w : I → ℝ) {v r : ℝ},
    (∀ i, 0 ≤ w i) → 0 < v → (∑ i, (w i) ^ 2) ≤ v → 0 ≤ r →
    signLaw q {s | r < |target w s - ∑ i, w i * (q i : ℝ)|} ≤
      ENNReal.ofReal (2 * Real.exp (-2 * r ^ 2 / v))

/-- The display in the proof of `prop:outer`: `∑ w² ≤ 1/M` gives `2 exp(-MΔ²/32)`,
and `M ≥ 32 Δ⁻² log(2/δ)` makes that at most `δ`. -/
def ReplicationTailStatement : Prop :=
  ∀ {I : Type} [Fintype I] (q : I → unitInterval) (w : I → ℝ) (M : ℕ) {Δ δ : ℝ},
    (∀ i, 0 ≤ w i) → 0 < M → (∑ i, (w i) ^ 2) ≤ 1 / (M : ℝ) → 0 < Δ → 0 < δ →
    32 * Real.log (2 / δ) / Δ ^ 2 ≤ (M : ℝ) →
    signLaw q {s | Δ / 8 < |target w s - ∑ i, w i * (q i : ℝ)|} ≤
        ENNReal.ofReal (2 * Real.exp (-(M : ℝ) * Δ ^ 2 / 32)) ∧
      2 * Real.exp (-(M : ℝ) * Δ ^ 2 / 32) ≤ δ

/-- `finite_confidence_lower` with `0 ≤ w i` and the Hoeffding weight condition
`32 log(2/δ) ∑ w² ≤ Δ²` in place of `∑ w² ≤ δΔ²/16`. -/
def HoeffdingConfidenceLowerStatement : Prop :=
  ∀ {m : ℕ} {R : Type} [MeasurableSpace R] (A : Estimator m R) (d : Fin m → Gap)
    (w η : Fin m → ℝ) (qp qm : Fin m → unitInterval),
    (∀ i, (qp i : ℝ) = 1 / 2 + η i) → (∀ i, (qm i : ℝ) = 1 / 2 - η i) →
    ∀ {B h Δ δ : ℝ}, 0 ≤ B → 0 < h → 0 < Δ → 0 < δ → δ ≤ 1 / 8 →
    (∀ i, 0 ≤ η i ∧ η i ≤ 1 / 8) → (∀ i, (d i : ℝ) * η i ≤ h / 8) →
    (∑ i, w i * (qp i : ℝ)) - (∑ i, w i * (qm i : ℝ)) = Δ →
    (∀ i, 0 ≤ w i) → 32 * Real.log (2 / δ) * (∑ i, (w i) ^ 2) ≤ Δ ^ 2 →
    (∀ s, ThresholdHC.ObservedState.expectedWork A d s ≤ ENNReal.ofReal B) →
    UniformConfidence A d w (Δ / 4) δ →
    (225 / (128 * h ^ 2)) * klB (1 - 2 * δ) (2 * δ) ≤ B

/-- Every finite measurable cell design whose squared cell lengths meet the
Hoeffding condition `32 log(2/δ) ∑ w² ≤ Δ²`, with `Δ = cellDelta`, forces the
lower bound. In particular this covers every design with `∑ w² ≤ 1/M` and
`M ≥ 32 Δ⁻² log(2/δ)`. -/
def HoeffdingDesignLowerStatement : Prop :=
  ∀ (h : Gap) {N : ℕ} (cap : Fin N → Gap) (cell : unitInterval → Fin N) (hc : Measurable cell)
    {δ : ℝ}, 0 < δ → δ ≤ 1 / 8 →
    32 * Real.log (2 / δ) * (∑ i, (cellWeight cell i) ^ 2) ≤ (cellDelta cap cell h) ^ 2 →
    ∀ (R : Type) [MeasurableSpace R] (A : StateEstimator R) (B : ℝ), 0 ≤ B →
      (∀ s, (∫⁻ z, totalProcessWork z.2 ∂stateLaw A cap cell hc s) ≤ ENNReal.ofReal B) →
      (∀ s, stateLaw A cap cell hc s
        {z | cellDelta cap cell h / 4 < |A.output z - stateTarget cell s|} ≤ ENNReal.ofReal δ) →
      (225 / (128 * (h : ℝ) ^ 2)) * klB (1 - 2 * δ) (2 * δ) ≤ B

/-- `prop:outer` with the paper's replicated construction: `N` labels with distinct
caps `c j` and weights `v j`, and `M` equal replicas per label (cell `(j,k)` has
cap `c j` and length `v j / M`), with `M = ⌈32 Δ⁻² log(2/δ)⌉₊`. -/
def HoeffdingFiniteObservedStatement : Prop :=
  ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] (h : Gap) {δ : ℝ}, 0 < δ → δ ≤ 1 / 8 →
    ∃ (N M : ℕ) (c : Fin N → Gap) (v : Fin N → ℝ) (cap : Fin (N * M) → Gap)
      (gap : unitInterval → Gap) (cell : unitInterval → Fin (N * M)) (hc : Measurable cell),
      Measurable gap ∧ volume.map gap = μ ∧ (∀ u, gap u ≤ cap (cell u)) ∧
      Function.Injective c ∧ (∀ j, 0 ≤ v j) ∧ (∑ j, v j) = 1 ∧
      (∀ j k, cap (finProdFinEquiv (j, k)) = c j) ∧
      (∀ j k, cellWeight cell (finProdFinEquiv (j, k)) = v j / (M : ℝ)) ∧
      0 < M ∧ M = ⌈32 * Real.log (2 / δ) / (cellDelta cap cell h) ^ 2⌉₊ ∧
      (∑ i, (cellWeight cell i) ^ 2) ≤ 1 / (M : ℝ) ∧
      2 * Real.exp (-(M : ℝ) * (cellDelta cap cell h) ^ 2 / 32) ≤ δ ∧
      0 < cellDelta cap cell h ∧
      modulus μ h / 8 ≤ cellDelta cap cell h ∧
      (∀ x : ℝ, volume {u : unitInterval | (cap (cell u) : ℝ) ≤ x} ≤ μ {d : Gap | (d : ℝ) ≤ x}) ∧
      (∀ (R : Type) [MeasurableSpace R] (A : StateEstimator R) (B : ℝ), 0 ≤ B →
        (∀ s, (∫⁻ z, totalProcessWork z.2 ∂stateLaw A cap cell hc s) ≤ ENNReal.ofReal B) →
        (∀ s, stateLaw A cap cell hc s
          {z | cellDelta cap cell h / 4 < |A.output z - stateTarget cell s|} ≤ ENNReal.ofReal δ) →
        (225 / (128 * (h : ℝ) ^ 2)) * klB (1 - 2 * δ) (2 * δ) ≤ B)

end ThresholdHC.ObservedHoeffding
