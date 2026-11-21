import Mathlib.Probability.Moments.Variance
import Mathlib.Order.SaddlePoint
import Mathlib.Data.EReal.Basic

/-! Target statements for the restricted pilot correction.

Source: `research/2026-10-27-population-step/upper/proof.tex` (generated copy
`proof-body.tex`), paragraph `Experiment`, Theorem `thm:saddle` (A saddle point
for a fixed scalar control variate) and the following unlabeled Theorem
(Independent pilot learning does not improve this minimax risk). The claim is
summarized in `research/2026-10-27-population-step/FINAL_REPORT.md` and in the
row `Restricted pilot correction` of `docs/SECONDARY_CLAIMS.md`.

* `SaddleStatement`: `thm:saddle`. The map `f(β,q) = Var_q(Y - βZ)` has a
  saddle point `(β₀,q₀)` on `ℝ × Q`, and both `inf_β sup_q f` and
  `sup_q inf_β f` equal `f(β₀,q₀)`.
* `PilotNoGainStatement`: the pilot theorem. The fixed coefficient `β₀` gives
  an unbiased raw average whose worst mean squared error over `Q` is
  `F*/n`, where `F* = inf_β sup_q f`; no coefficient chosen by an independent
  pilot has worst mean squared error below `F*/n` (mean squared errors are
  taken in `[0,∞]`, so infinite risk is allowed, as in the source).
* `CoinWitnessStatement`: a nonvacuity witness that goes beyond the source.
  One gap `d = 1/2` (so a single flip reveals the sign) and an internal fair
  coin give features satisfying `FixedFeatures` for every `0 < ρ ≤ 1/2`, with
  a parameter `q ∈ Q` at which every coefficient has variance at least
  `ρ(1-ρ) > 0`; hence `F* > 0` there and the no-gain bound is not trivial.

Deviations from the source.

* The model is an abstract mixture. The source's single-coin observation rule
  (gaps `0 < d_i ≤ 1/2`, conditionally iid flips with success probability
  `1/2 + (2S-1)D`) is replaced by arbitrary conditional probability laws
  `Pplus i` and `Pminus i`, on an arbitrary measurable space, of one fresh
  coin's observations and internal randomization given `(D,S) = (d_i,±)`.
  Every observation rule induces such laws, so this is a generalization, but
  gaps and flips are not modelled and there is no formal link to the
  repository's coin or Tier6 experiment model. Only the mixture structure
  `coinLaw` is used.
* Weaker side conditions: `π_i ≥ 0` instead of `π_i > 0`, and `ρ ≥ 0` instead
  of `0 < ρ ≤ 1/4`. Added hypotheses: `Y`, `Z` and the pilot coefficient
  `βhat` are measurable (Tonelli's theorem needs them).
* The observation space `Ω` and the pilot transcript space `T` are
  quantified in `Type` (universe 0).
* The pilot is an arbitrary transcript space `T` with a law `L q` that may
  depend on `q` in any way (oracle coefficients included). Its independence
  from the production coins is encoded by the product measure
  `(L q).prod (Measure.pi ...)`; an almost surely finite coefficient is a
  real-valued `βhat : T → ℝ`.
* The work-accounting sentence (`ℓ` flips per coin; `m+n` fixed-coefficient
  coins give `F*/(m+n)`) is not modelled; since `β₀` and `F*` are chosen
  before `n`, the fixed-coefficient clause at `m+n` gives its arithmetic.
* Not stated: `prop:two` (the three-flip, two-gap construction), the
  fully specified pilot implementation and its mean squared error, the exact
  moment formulas and the numerical example `427/16`.
* As in the source, clipping the output, changing the production feature or
  sampling rule after the pilot, adaptive production sample sizes, accepting
  bias and nonlinear aggregation are outside the statements. -/
noncomputable section
namespace ThresholdHC.PilotCorrection
open MeasureTheory ProbabilityTheory
open scoped ENNReal

/-- The parameter space `Q = {q ∈ [0,1]^k : ∑ π_i q_i ≤ ρ}`. -/
def rarityPolytope {k : ℕ} (π : Fin k → ℝ) (ρ : ℝ) : Set (Fin k → ℝ) :=
  {q | (∀ i, 0 ≤ q i ∧ q i ≤ 1) ∧ ∑ i, π i * q i ≤ ρ}

/-- The sign mass `θ(q) = ∑ π_i q_i`. -/
def signMass {k : ℕ} (π q : Fin k → ℝ) : ℝ := ∑ i, π i * q i

/-- Law of one fresh coin's observations and internal randomization. Gap `i`
has mass `π i` and sign `+` has probability `q i`; `Pplus i` and `Pminus i`
are the conditional laws given `(D,S) = (d_i,+)` and `(d_i,-)`. -/
def coinLaw {Ω : Type*} [MeasurableSpace Ω] {k : ℕ} (π : Fin k → ℝ)
    (Pplus Pminus : Fin k → Measure Ω) (q : Fin k → ℝ) : Measure Ω :=
  ∑ i, (ENNReal.ofReal (π i * q i) • Pplus i +
    ENNReal.ofReal (π i * (1 - q i)) • Pminus i)

/-- The raw production average `n⁻¹ ∑_j (Y_j - β Z_j)`. -/
def rawAverage {Ω : Type*} (Y Z : Ω → ℝ) (n : ℕ) (β : ℝ) (ω : Fin n → Ω) : ℝ :=
  (n : ℝ)⁻¹ * ∑ j, (Y (ω j) - β * Z (ω j))

/-- Mean squared error, in `[0,∞]`, of the raw average with a fixed
coefficient `β` on `n` independent production coins. -/
def fixedRisk {Ω : Type*} [MeasurableSpace Ω] {k : ℕ} (π : Fin k → ℝ)
    (Pplus Pminus : Fin k → Measure Ω) (Y Z : Ω → ℝ) (n : ℕ) (β : ℝ)
    (q : Fin k → ℝ) : ℝ≥0∞ :=
  ∫⁻ ω, ENNReal.ofReal ((rawAverage Y Z n β ω - signMass π q) ^ 2)
    ∂Measure.pi (fun _ : Fin n => coinLaw π Pplus Pminus q)

/-- Mean squared error, in `[0,∞]`, of the raw average whose coefficient
`βhat t` is chosen from a pilot transcript `t ∼ L q` independent of the `n`
production coins (product measure). -/
def pilotRisk {Ω T : Type*} [MeasurableSpace Ω] [MeasurableSpace T] {k : ℕ}
    (π : Fin k → ℝ) (Pplus Pminus : Fin k → Measure Ω) (Y Z : Ω → ℝ) (n : ℕ)
    (L : (Fin k → ℝ) → Measure T) (βhat : T → ℝ) (q : Fin k → ℝ) : ℝ≥0∞ :=
  ∫⁻ x, ENNReal.ofReal ((rawAverage Y Z n (βhat x.1) x.2 - signMass π q) ^ 2)
    ∂(L q).prod (Measure.pi (fun _ : Fin n => coinLaw π Pplus Pminus q))

/-- The hypotheses of `thm:saddle`: square-integrable measurable features
under every conditional law, with `E_q Y = θ(q)`, `E_q Z = 0` and
`E_q Z² = v > 0` for every `q ∈ Q`, together with the experiment conditions
`π_i ≥ 0`, `∑ π_i = 1` and `ρ ≥ 0` (weaker than the source's `π_i > 0` and
`0 < ρ ≤ 1/4`). -/
def FixedFeatures {Ω : Type*} [MeasurableSpace Ω] {k : ℕ} (π : Fin k → ℝ)
    (ρ : ℝ) (Pplus Pminus : Fin k → Measure Ω) (Y Z : Ω → ℝ) (v : ℝ) : Prop :=
  (∀ i, 0 ≤ π i) ∧ ∑ i, π i = 1 ∧ 0 ≤ ρ ∧ Measurable Y ∧ Measurable Z ∧
  (∀ i, MemLp Y 2 (Pplus i) ∧ MemLp Y 2 (Pminus i) ∧
    MemLp Z 2 (Pplus i) ∧ MemLp Z 2 (Pminus i)) ∧
  0 < v ∧
  ∀ q ∈ rarityPolytope π ρ,
    (∫ ω, Y ω ∂coinLaw π Pplus Pminus q) = signMass π q ∧
    (∫ ω, Z ω ∂coinLaw π Pplus Pminus q) = 0 ∧
    (∫ ω, Z ω ^ 2 ∂coinLaw π Pplus Pminus q) = v

/-- `thm:saddle`: `f(β,q) = Var_q(Y - βZ)` has a saddle point `(β₀,q₀)` on
`ℝ × Q`, and `inf_β sup_q f = sup_q inf_β f = f(β₀,q₀)`. -/
def SaddleStatement : Prop :=
  ∀ (Ω : Type) [MeasurableSpace Ω] (k : ℕ) (π : Fin k → ℝ) (ρ : ℝ)
    (Pplus Pminus : Fin k → Measure Ω)
    [∀ i, IsProbabilityMeasure (Pplus i)] [∀ i, IsProbabilityMeasure (Pminus i)]
    (Y Z : Ω → ℝ) (v : ℝ),
    FixedFeatures π ρ Pplus Pminus Y Z v →
    ∃ β₀ : ℝ, ∃ q₀ ∈ rarityPolytope π ρ,
      IsSaddlePointOn Set.univ (rarityPolytope π ρ)
        (fun β q => variance (fun ω => Y ω - β * Z ω) (coinLaw π Pplus Pminus q))
        β₀ q₀ ∧
      (⨅ β : ℝ, ⨆ q ∈ rarityPolytope π ρ,
          ((variance (fun ω => Y ω - β * Z ω) (coinLaw π Pplus Pminus q) : ℝ) :
            EReal)) =
        ((variance (fun ω => Y ω - β₀ * Z ω) (coinLaw π Pplus Pminus q₀) : ℝ) :
          EReal) ∧
      (⨆ q ∈ rarityPolytope π ρ, ⨅ β : ℝ,
          ((variance (fun ω => Y ω - β * Z ω) (coinLaw π Pplus Pminus q) : ℝ) :
            EReal)) =
        ((variance (fun ω => Y ω - β₀ * Z ω) (coinLaw π Pplus Pminus q₀) : ℝ) :
          EReal)

/-- The pilot theorem: with `F* = inf_β sup_q Var_q(Y - βZ)`, the fixed
coefficient `β₀` gives an unbiased raw average with worst mean squared error
`F*/n`, and no coefficient chosen by an independent pilot has worst mean
squared error below `F*/n` (mean squared errors may be infinite). -/
def PilotNoGainStatement : Prop :=
  ∀ (Ω : Type) [MeasurableSpace Ω] (k : ℕ) (π : Fin k → ℝ) (ρ : ℝ)
    (Pplus Pminus : Fin k → Measure Ω)
    [∀ i, IsProbabilityMeasure (Pplus i)] [∀ i, IsProbabilityMeasure (Pminus i)]
    (Y Z : Ω → ℝ) (v : ℝ),
    FixedFeatures π ρ Pplus Pminus Y Z v →
    ∃ β₀ Fstar : ℝ,
      (Fstar : EReal) = ⨅ β : ℝ, ⨆ q ∈ rarityPolytope π ρ,
        ((variance (fun ω => Y ω - β * Z ω) (coinLaw π Pplus Pminus q) : ℝ) :
          EReal) ∧
      ∀ n : ℕ, 1 ≤ n →
        (∀ q ∈ rarityPolytope π ρ,
          (∫ ω, rawAverage Y Z n β₀ ω
              ∂Measure.pi (fun _ : Fin n => coinLaw π Pplus Pminus q)) =
            signMass π q) ∧
        (⨆ q ∈ rarityPolytope π ρ, fixedRisk π Pplus Pminus Y Z n β₀ q) =
          ENNReal.ofReal (Fstar / n) ∧
        ∀ (T : Type) [MeasurableSpace T] (L : (Fin k → ℝ) → Measure T),
          (∀ q ∈ rarityPolytope π ρ, IsProbabilityMeasure (L q)) →
          ∀ βhat : T → ℝ, Measurable βhat →
            ENNReal.ofReal (Fstar / n) ≤
              ⨆ q ∈ rarityPolytope π ρ, pilotRisk π Pplus Pminus Y Z n L βhat q

/-- A fair internal coin. -/
def fairCoin : Measure Bool :=
  (2⁻¹ : ℝ≥0∞) • Measure.dirac true + (2⁻¹ : ℝ≥0∞) • Measure.dirac false

/-- Nonvacuity witness: one gap `d = 1/2`, so that one flip reveals the sign,
plus an internal fair coin. The indicator `Y` of the flip and the `±1` value
`Z` of the internal coin satisfy `FixedFeatures` with `v = 1` for every
`0 < ρ ≤ 1/2`, and at some `q ∈ Q` every coefficient has variance at least
`ρ(1-ρ) > 0`, so `F* ≥ ρ(1-ρ) > 0` for this instance. -/
def CoinWitnessStatement : Prop :=
  ∀ ρ : ℝ, 0 < ρ → ρ ≤ 1 / 2 →
    let Pp : Fin 1 → Measure (Bool × Bool) := fun _ => (Measure.dirac true).prod fairCoin
    let Pm : Fin 1 → Measure (Bool × Bool) := fun _ => (Measure.dirac false).prod fairCoin
    let Y : Bool × Bool → ℝ := fun ω => if ω.1 then 1 else 0
    let Z : Bool × Bool → ℝ := fun ω => if ω.2 then 1 else -1
    (∀ i, IsProbabilityMeasure (Pp i)) ∧ (∀ i, IsProbabilityMeasure (Pm i)) ∧
    FixedFeatures (fun _ => 1) ρ Pp Pm Y Z 1 ∧
    ∃ q ∈ rarityPolytope (fun _ => 1) ρ, ∀ β : ℝ,
      ρ * (1 - ρ) ≤ variance (fun ω => Y ω - β * Z ω) (coinLaw (fun _ => 1) Pp Pm q)

end ThresholdHC.PilotCorrection
