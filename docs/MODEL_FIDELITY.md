# Model-fidelity brief for specialist review

A Lean audit in this repository shows that a named Lean type is proved, using
only the axioms `propext`, `Classical.choice` and `Quot.sound`. It cannot show
that the type says what the paper means. This brief is for a probabilist or
statistician who wants to check that second step. It sets the paper's model
sentences beside the Lean definitions that the theorems unfold to, and follows
the chain from the single-coin obstruction to the population lower bound. It
then lists where Lean is wider or narrower than the paper, and what protects
the statements.

The brief covers six definitions: the observable experiment, adaptive
policies, physical-flip cost, the expected budget, the global rarity
constraint and the risk. It does not re-prove anything, and it is not a review
of the paper proofs.

## How to read it

- **Lean pins.** Lean links point to commit
  [`43d9fba`](https://github.com/davidiach/adaptive-threshold-estimation/tree/43d9fba720332fe7f3b5dfbcfef137839e6cfef5).
  GitHub Actions run 42003950396 on that commit passed all five jobs,
  including the three Lean jobs. Every Lean file cited here is byte-identical
  at the commit that adds this brief; later commits only add the
  `AnytimeLower` files and edit `lean/README.md`.
- **Paper references** give the rendered numbers of the
  [current v6 build](../paper/v6/README.md) and the `.tex` source file in
  `paper/v6/`. Do not use `paper/v6/paper.pdf`, which predates later status
  corrections.
- **Labels.** *Matches*: the same object. *Wider*: Lean allows more than the
  paper's wording. *Narrower*: Lean allows less. *Differs*: a different object
  or route. For a minimax lower bound, a wider algorithm class gives a stronger
  statement. A narrower one gives a weaker statement, which still transfers if
  every algorithm the paper intends embeds in the Lean class.
- **How this was produced.** Seven extraction passes read the paper and Lean
  sources, one per component. An independent verifier then reopened every
  citation at `43d9fba` and corrected the extraction. Lean was not compiled
  for this brief. Statements about audits rest on the saved records and on the
  CI run above.

## Five checks that carry most of the weight

1. The finite-prefix law [`transcriptLaw`][transcriptLaw] and
   [`creationLaw`][creationLaw], and the proved realization
   [`ProcessRealizationStatement`][ProcessRealization]. This is the only place
   where equation (3) is written as a formula. Every risk, work and confidence
   quantity is defined from the measure it describes.
2. [`AdaptiveEstimator`][AdaptiveEstimator] together with
   [`populationPolicy`][populationPolicy] and [`populationOutput`][populationOutput]:
   what an algorithm may see.
3. [`expectedWork`][expectedWork], [`UniformBudget`][UniformBudget] and
   [`RareBudget`][RareBudget]: what is charged, and under which priors.
4. [`minimaxRisk`][minimaxRisk] and [`rareMinimaxRisk`][rareMinimaxRisk]:
   where the infimum and supremum sit, and over which seed spaces.
5. [`NullVarianceObstruction`][NullVarianceObstruction]: the premise of the
   general RMS transfer. Lean never proves it for any gap law
   ([section 7](#7-theorem-chain-from-the-single-coin-obstruction-to-the-population-bound)).

## 1. The observable experiment

**Paper** (Section 2, equation (3), `core.tex`):

> A measurable function $q:(0,a]\to[0,1]$ specifies a population by
> $D\sim\mu,\ S\mid D=d\sim\mathrm{Ber}(q(d)),\ P=\tfrac12+(2S-1)D.$
> The variables attached to distinct new coins are independent. [...]
> Individual magnitudes and signs are not observed.

Section 11.1 (`rare-events.tex`) adds: "a unit keeps its latent state on every
revisit" and "all creation, revisiting, interleaving, and stopping decisions
use only an independent seed and the observed flips."

**Lean.** The finite-horizon law of a padded transcript
([Statements2.lean:59-62][transcriptLaw]):

```lean
def transcriptLaw {m n : ℕ} (pol : List Bool → Option (Fin m)) (d q : Fin m → ℝ)
    (ω : Fin n → Option Bool) : ℝ :=
  ∑ s : Fin m → Bool, (∏ i, if s i then q i else 1 - q i) *
    pathProb pol (fun i => 1/2 + (if s i then d i else -d i)) ω
```

[`pathProb`][pathProb] multiplies, step by step, $p_i$ or $1-p_i$ for the coin
the policy picks, `1` for `none, none`, and `0` for any observation after a
stop. The countable-label law [`creationLaw`][creationLaw] restricts the policy
to the labels below [`coinCap`][coinCap]. That cap is the supremum over the
whole depth-$n$ decision tree, so no label queried within $n$ steps is cut
off. The seed is the algorithm's randomness together with one gap per label,
drawn iid from $\mu$ ([AlgorithmCore.lean:31-35][PopulationSeed]):

```lean
abbrev PopulationSeed (R : Type) := R × (ℕ → Gap)
... := A.randomLaw.prod (Measure.infinitePi (fun _ : ℕ => μ))
```

[`experimentLaw`][experimentLaw] is the Ionescu–Tulcea process built from the
ratios `creationLaw (w·o) / creationLaw w` ([ProcessWeights.lean:10-13][creationTransition]).
A prefix of probability zero moves to `none`. Its defining property, the
finite-prefix identity [`RealizesCreationPrefixes`][RealizesCreationPrefixes],
is a proved theorem ([`process_realization`][process_realization],
[`population_realization`][population_realization]), not an assumption.

| Concept | Paper | Lean | Label | Notes |
|---|---|---|---|---|
| Gap $D\in(0,1/2]$, any law | §2, `core.tex` | [`Gap`][Gap], `[IsProbabilityMeasure μ]` | matches | Atoms, gaps in the support and singular parts are allowed. $D=0$ is excluded, so populations with an atom at $P=1/2$ are excluded, as the paper's formal model says (`core.tex`, and the envelope class in §2.1). $D=1/2$ is allowed. |
| Sign law $q$ | eq. (3) | [`SignLaw`][SignLaw]: measurable, values in $[0,1]$ | matches | $q$ is a function defined everywhere, not a $\mu$-a.e. class; the experiment and target depend on $q$ only $\mu$-a.e., so the supremum is unchanged. |
| One sign per coin, kept on revisits | eq. (3); §11.1 | the sum over `s` outside the product over time in `transcriptLaw` | matches | Signs are never random variables on the sample space; they are summed out of every finite-prefix weight. The gap persists because it is stored in the seed. |
| Independent coins | §2 | iid gap array; independent sign factors | matches | All gaps are drawn at time 0 rather than at creation. They are independent of the algorithm seed and invisible to it, so this agrees in law. |
| Literal iid-tape experiment | eq. (3), Section 1 | [`original_observable_simulation_law`][original_sim] | matches | It proves that the (seed, tape) law of `experimentLaw` equals running the policy on independent per-coin flip tapes. It is outside the Tier 6 lock. The blind upper bound and several later developments use it. The Tier 6 lower bound and the RMS transfer chain do not; they work from the finite-prefix identity. |
| Target $\theta=\int q\,d\mu$ | §2 | [`signMean`][signMean] | matches | The paper's Section 1 writes $\theta(G)=P_G(P>1/2)$. Lean defines $G_{\mu,q}$ (`populationParameterLaw`, `SmoothDensity.latentLaw`), but proves $\theta=G(P>1/2)$ only for laws with a density. That it holds for every law is one line from `populationParameterLaw_integral` but is not stated, and the converse (every $G$ is some $G_{\mu,q}$) is not formalized. |

**For the reviewer.** Is summing each sign once, outside the time product, the
persistent-sign model you intend? Is a pre-drawn, label-indexed gap array an
acceptable reading of "draw a fresh gap at creation"? Is it acceptable that
the $G$-form of the claims rests on an unformalized disintegration?

## 2. Adaptive policies

**Paper** (Section 2, `core.tex`):

> An algorithm has an independent random seed, creates finitely many coins
> before each observation, selects one of its coins, and receives its next
> Bernoulli observation. It stops after $T$ observations and returns a real
> number $\widehat\theta$. [...] Finite internal computation between
> observations is implicit.

**Lean** ([AlgorithmCore.lean:20-26][AdaptiveEstimator]):

```lean
structure AdaptiveEstimator (R : Type) [MeasurableSpace R] where
  randomLaw : Measure R
  probability : IsProbabilityMeasure randomLaw
  policy : R → List Bool → Option ℕ
  policy_measurable : MeasurableCreationPolicy policy
  output : R × ProcessTape → ℝ
  output_measurable : Measurable output
```

The policy maps the seed and the outcomes so far to a label (`some i`) or to
`none`, meaning stop. A new label creates a coin and an old one revisits it.
[`populationPolicy`][populationPolicy] passes only `u.1`, the algorithm's own
seed, and [`populationOutput`][populationOutput] only `(z.1.1, z.2)`, the seed
and the tape. The gap array is never passed. Measurability means that each set
`{u | pol u xs = a}` is measurable ([Tier5/Model.lean:21-23][MeasurableCreationPolicy]).
`Option ℕ` and `Option Bool` carry the discrete σ-algebra
([Tier5/Model.lean:19][OptionNatSigma], [Tier4/Model.lean:17][OptionBoolSigma]),
so the output is jointly measurable for the seed σ-algebra times the cylinder
σ-algebra on tapes.

| Point | Label | Notes |
|---|---|---|
| Seed spaces are `R : Type` (universe 0), with any σ-algebra | narrower | Includes every standard Borel space. The lower bound and the upper witness range over the same class, so the two-sided law concerns one object. |
| Only measurable policies and outputs | narrower | Needed anyway for $E\,T$ and the risk to be defined. The paper's own observation model (Appendix G, `appendix-lower-foundations.tex`) also uses $F_n=\sigma(U,X_1,\dots,X_n)$ with $T$ a stopping time. |
| One seed drawn up front | matches | Fresh randomness used between steps can be pre-drawn into the seed. The Lean upper algorithm does exactly that, with seed `ℕ → ℕ × ℝ` ([SeedInput.lean:23-26][BatchSeed]). |
| No finite-computation or computability constraint | wider | Strengthens the lower bounds. The upper witness is noncomputable and uses real-valued seeds, so the paper's "finite internal computation" is not checked on either side. |
| Chosen labels are not passed back to the policy | matches | They are a deterministic function of the seed and the outcomes. |
| Output defined when $T=\infty$ | wider | The paper does not define $\widehat\theta$ there. Under a finite budget these paths have probability zero ([`creation_stops`][creation_stops]). |
| Knowledge of $\mu$ | matches | In [`minimaxRisk`][minimaxRisk] the algorithm is chosen after $\mu$, so the benchmark may know $\mu$. The blind upper statement chooses the family before $\mu$ ([BlindUpper/Specification.lean:11-16][BlindUpperSpec]). |
| Revealed and selected magnitudes | wider | Separate structures. The lower bounds are proved for the general `OracleEstimator` class, whose seed carries an arbitrary seed-measurable gap array. [`SelectedSemanticsStatement`][SelectedSemantics] fixes creation and reuse. |

**For the reviewer.** Does every algorithm you intend embed in
(`R : Type`, measurable policy, measurable output)? Is it acceptable that
neither side checks the "finite internal computation" clause?

## 3. Physical-flip cost

**Paper** (Section 2, `core.tex`): "We count observations, not arithmetic
operations or independent random bits." Section 11.1: "Every requested
observation costs one, including the first on a unit; units created but never
observed have no statistical effect."

**Lean** ([StoppingModel.lean:23-24][totalProcessWork], [AlgorithmModel.lean:24-26][expectedWork]):

```lean
def totalProcessWork (x : ProcessTape) : ℝ≥0∞ :=
  ⨆ n : ℕ, ENNReal.ofReal (workOf (processPrefix n x))

def expectedWork ... : ℝ≥0∞ :=
  ∫⁻ z, totalProcessWork z.2 ∂experimentLaw μ A q
```

[`workOf`][workOf] counts the `some` entries of a prefix. Every flip counts,
including the first flip of a coin and every revisit. Seeds and computation
are free. Work takes values in $[0,\infty]$, so infinite expected work is
representable; it simply fails a budget.

- **Label: matches.** A coin exists in Lean only once it is flipped, so on
  every path the number of coins is at most $T$. The paper's remark that a
  fixed fee per new coin changes cost by at most a constant factor is
  therefore immediate in the Lean model. No separate creation-cost model is
  formalized.
- **Almost-sure stopping** is a theorem: finite expected work under one
  measure forces stopping almost surely ([`CreationStopsStatement`][CreationStops],
  proved as [`creation_stops`][creation_stops]). No named Tier 6 theorem
  applies it to `experimentLaw`. Proofs apply it inline, for example
  [ConfidenceTransfer/Terminal.lean:30][TerminalStops] and
  [RareAboveTwo/TerminalInformation.lean:26][TerminalInfoStops].
  The magnitude-oracle models have a named version,
  [`oracle_stops_of_budget`][oracle_stops].

## 4. The expected budget

**Paper** (Section 2, equation (4)):
$R_\mu(B)=\inf_{\mathcal A:\sup_q E_{\mu,q}T\le B}\ \sup_q\bigl(E_{\mu,q}(\widehat\theta-\theta)^2\bigr)^{1/2}$.
"These are expected-budget criteria, not deterministic maximum-work criteria."

**Lean** ([AlgorithmModel.lean:28-30][UniformBudget]):

```lean
def UniformBudget ... (B : ℝ) : Prop :=
  ∀ q : SignLaw, expectedWork μ A q ≤ ENNReal.ofReal B
```

- **Label: matches.** The budget and the risk range over the same unrestricted
  class of sign laws.
- $B$ is real. `ENNReal.ofReal` sends $B<0$ to $0$, which does not matter
  because the theorems assume $B\ge1$ (ordinary laws) or $B>0$ (general-law
  rare-event results). [`BudgetClassNonemptyStatement`][BudgetNonempty] gives
  a zero-work estimator for $B\ge0$, and `minimaxRisk_le_one`
  ([Tier6/Full.lean:24][minimaxRisk_le_one]) bounds the minimax value by 1.
- **Hard caps** (Appendix R). [`PathwiseCap`][PathwiseCap] bounds the flips on
  every seed value and every admissible path. That is stricter than an
  almost-sure cap, and the two-sided hard-cap results do not depend on the
  difference. [`hardMinimaxRisk`][hardMinimaxRisk] and
  [`hardRareMinimaxRisk`][hardRareMinimaxRisk] are defined in proof files
  that no lock covers. The paper never writes down the rare hard-cap risk;
  its constraint applies under every prior, not only rare ones.

## 5. The global rarity constraint

**Paper** (Section 11.1, `rare-events.tex`):
$\mathcal Q_\rho(\mu)=\{q \text{ measurable}: \int q\,d\mu\le\rho\}$, with the
budget and the risk taken over $\mathcal Q_\rho(\mu)$. "The global constraint
does not impose $q(d)\le\rho$ pointwise."

**Lean** ([RareAboveTwo/Model.lean:19-32][RarePrior]):

```lean
def RarePrior (μ : Measure Gap) (ρ : ℝ) (q : SignLaw) : Prop := signMean μ q.val ≤ ρ

def RareBudget ... (ρ B : ℝ) : Prop :=
  ∀ q : SignLaw, RarePrior μ ρ q → expectedWork μ A q ≤ ENNReal.ofReal B

def rareMinimaxRisk (μ : Measure Gap) [IsProbabilityMeasure μ] (ρ B : ℝ) : ℝ≥0∞ :=
  sInf {t | ∃ (R : Type) (_ : MeasurableSpace R) (A : AdaptiveEstimator R),
    RareBudget μ A ρ B ∧ t = rareRisk μ A ρ}
```

- **Label: matches.** Rarity is the integral constraint. The budget binds only
  on $\mathcal Q_\rho$, so the admissible class is larger than under
  `UniformBudget`: an algorithm may be arbitrarily expensive on priors that
  are not rare.
- The range $0<\rho\le1/4$ appears only as a theorem hypothesis. For $\rho<0$
  the class is empty and the rare risk is 0, a harmless artifact.
- The critical-law results (Theorem 11.2) use parallel definitions on the real
  line ([CriticalRareModel.lean:12-29][CriticalRareModel]). They are proved
  equivalent to the definitions here by
  [`critical_budget_equivalence`][critical_budget_eq] and
  [`critical_risk_equivalence`][critical_risk_eq].

## 6. The risk

**Paper**: the inner term of equation (4), and equation (5) for confidence:
$r_\mu(B,\delta)=\inf_{\mathcal A:\sup_q E_{\mu,q}T\le B}\inf\{r\ge0:\sup_q P_{\mu,q}(|\widehat\theta-\theta|>r)\le\delta\}$.
Equation (6) defines $\omega_\mu(h)=h\,E_\mu\min\{h^{-1},D^{-1}\}$.

**Lean** ([TestingModel.lean:9-11][squaredRisk], [AlgorithmModel.lean:32-41][maximalRMSRisk]):

```lean
def squaredRisk (P : Measure Ω) (f : Ω → ℝ) (a : ℝ) : ℝ≥0∞ :=
  ∫⁻ x, ENNReal.ofReal ((f x-a)^2) ∂P

def maximalRMSRisk ... : ℝ≥0∞ :=
  ⨆ q : SignLaw, rootMeanRisk (experimentLaw μ A q) (populationOutput A) (signMean μ q.val)

def minimaxRisk (μ : Measure Gap) [IsProbabilityMeasure μ] (B : ℝ) : ℝ≥0∞ :=
  sInf {r | ∃ (R : Type) (_ : MeasurableSpace R) (A : AdaptiveEstimator R),
    UniformBudget μ A B ∧ r = maximalRMSRisk μ A}
```

- **Label: matches.** The mean squared error is a lower integral with values
  in $[0,\infty]$. No integrability is assumed, and infinite risk is kept.
- [`modulus`][modulus] is $\int\min\{1,h/d\}\,d\mu$, which equals
  $\omega_\mu(h)$ for $h>0$.
- The confidence radius [`minimaxConfidenceRadius`][minimaxConfidenceRadius]
  merges the paper's two infima into one infimum over pairs $(A, r)$ with the
  same value. It uses the strict event $|\widehat\theta-\theta|>r$, as in
  equation (5). Its frozen statement carries the coefficients $1/64$ and
  $8192$ in the type.

## 7. Theorem chain from the single-coin obstruction to the population bound

**Paper.** Theorem S.7 (`rms-localization.tex`) and Theorem H.3, display
(154) (`appendix-transfer-foundations.tex`):
$R_{\mu,\rho}(B)\ge\min\{b,\sqrt{J/B}\}/128$ whenever every capped observable
one-coin estimator with bias at most $b$ satisfies $V\,E_0T\ge J$.

**Lean, final statement** ([RMSLocalization/CommonPair.lean:39][minimax_rms]):

```lean
theorem minimax_rms_of_obstruction (μ : Measure Gap) [IsProbabilityMeasure μ]
    {ρ b J B : ℝ} (hρ : 0 < ρ) (hρ4 : ρ ≤ 1/4)
    (hb : 0 < b) (hJ : 0 < J) (hB : 0 < B)
    (hobs : NullVarianceObstruction μ (gapParameter false) (gapParameter true) ρ b J) :
    ENNReal.ofReal (min b (Real.sqrt (J/B))/128) ≤ rareMinimaxRisk μ ρ B
```

The per-estimator form is [`rms_rate_of_obstruction`][rms_rate_obs] (line 30).
The saved audit [results/rms-localization-20261105](../results/rms-localization-20261105/README.md)
pins both exact types, with standard axioms only, at checkpoint `8ed8754`. No
existing Lean file changed between that checkpoint and `43d9fba`.

| Step | Paper | Lean | Label and notes |
|---|---|---|---|
| 0. Single-coin premise | Theorem S.3 hypothesis; $\mathcal X_\rho$, $V$, $E_0T$ in §H | [`NullVarianceObstruction`][NullVarianceObstruction] | matches. It quantifies over every seed space and law, every one-coin [`StoppedProcedure`][StoppedProcedure] with a deterministic cap and bounded output, and every $V\ge0$ that bounds the mixture variance over [`CappedPrior`][CappedPrior] ($q\le1/2$ pointwise, $\int q\le\rho$). If the bias is at most $b$ on that class, then $J\le V\,E_0T$, where $E_0T$ is the work under the all-negative prior. |
| 1. One common pair for every capped policy | Theorem S.3 | [`common_pair_of_obstruction`][common_pair_obs], [`common_pair_bound`][common_pair_bound] | matches. The quantifier order `∃ q r, ∀ ν A m` is the policy uniformity. The bound is $1-\mathrm{Aff}\le(42\delta^2/J)\,E_0T$ on the law of (seed, stopped word). The pair is mixed half-and-half with the constant $c=\rho$, as in the S.3 proof, so $q,r\ge\rho/2$. That departs from the H.3 proof's route, not from either statement. |
| 2. Midpoint hybrid and work accounting | Lemma H.2 | [`finite_population_hybrid_decomposition`][hybrid], [`localSimulation`][localSimulation], [`localSimulation_affinity_le`][affinity_le], [`null_work_le_twice_population_work`][null_work], [`finite_population_transfer`][finite_transfer] | matches. Each hybrid term becomes a one-coin procedure. It charges only the genuine coin's flips and reads the other coins from midpoint-population tapes held in its seed, consumed in order so that revisits see the same coin. The null work is at most twice the midpoint work, and the local midpoint works sum to the population midpoint work. The midpoint prior lies in the budget class by convexity ([`mixPrior_rare`][mixPrior_rare]). |
| 3. Countable labels and the private seed | S.7 proof; H.2 proof | [`creation_null_hellinger`][creation_null], [`creationPopulationWeight_eq_finite`][creation_eq_finite], [`observable_population_hellinger_bound`][observable_pop], [`observable_null_hellinger`][observable_null] | matches. For each seed the policy is cut to its finitely many queried labels, and the bound holds seed by seed. The seed stays in the observed law, so integrating over seeds is valid. |
| 4. Unbounded stopping | paragraph after Lemma H.2; S.7 proof | [`terminal_null_hellinger`][terminal_null], [`observable_terminal_affinity_bound`][terminal_affinity] | narrower, harmless. The bound passes to any finite-valued measurable decision of (seed, full tape) by a limit of affinities, which follows the paper's limit argument. It does not bound the total variation of the whole transcript. S.7 claims only terminal binary decisions. |
| 5. Testing and constants | S.7 proof; end of H.3 proof | [`component_pair_uniform`][component_pair], [`pair_rms_risk`][pair_rms], [`rms_rate_of_common_pair`][rms_rate_cp] | matches. With $s=\min\{b,\sqrt{J/B}\}/32$ and $\kappa=42/(1024B)$, $2\kappa B=21/256\le1/10$; the Boolean affinity bound $7/8<9/10$ then gives RMS at least $s/4$, the coefficient $1/128$. Lean uses affinity where H.3 uses total variation. |

**How conditional the result is.** No Lean theorem proves
`NullVarianceObstruction` for any gap law. The only consequence derived from
it directly is $b<\rho/2$ ([`obstruction_bias_lt_half`][bias_lt_half]). The
downstream premise [`CommonPairBound`][CommonPairBound], which
`rms_rate_of_common_pair` consumes, *is* Lean-proved for the quadratic
critical law, with $b=\rho/32$ and an existential constant in $J$
([`critical_common_pair_bound`][critical_cp], by a separate route). No theorem
states the composed RMS bound for that law. The critical RMS law itself is
Lean-checked separately ([`critical_minimax_lower_bound`][critical_lower]).

**Side result.** The selected-type KL transfer (Theorem S.2,
`TypedConfidence`) is stated on a directly defined tape model and is not used
by the RMS theorem.

## 8. Rare-event functionals

| Concept | Paper | Lean | Label and notes |
|---|---|---|---|
| Dyadic bands, costs $a_j$, entropy $G$, $\Gamma_\sigma$ | §13.1, eq. (60) | [EntropyTail/Model.lean:16-32][EntropyTailModel] | matches. Band $j$ is $(2^{-(j+2)},2^{-(j+1)}]$. Mathlib's $\log 0=0$ gives the paper's convention for zero coordinates. $\Gamma$ is a supremum over finite prefixes and may be $\infty$. |
| Selection $\mathcal K_{\mu,\rho}(B)$ | eq. (61) | [`selection`][selection] | matches. The infimum is over all $\sigma\le\mu$ in $[0,\infty]$; infinite entropy is never treated as zero. |
| Closed quantile $Q(B)$ with a fractional boundary atom | §14.2 eqs. (67)-(69); §14.6.1 | [`closedQuantileValue`][closedQuantile] | matches the general-law definition. The finite formula (67) is not restated in Lean. |
| Two-sided law | Theorem 13.2, eq. (63) | [`EntropyTailLawStatement`][EntropyTailLaw] | narrower. The constants come first, then $\rho$, $B$ and $\mu$, as in the paper. Lean does not state $c<C$, or that (61) and the three-piece form (62) are equivalent. |
| Coefficients $10^{-17}$ and $28000$ | eq. (128) states $33000$ | [`ExplicitLawStatement`][ExplicitLaw]; [`entropy_tail_upper_explicit`][tail_upper_explicit] | Lean's 28000 is stronger than the paper's 33000. [`paper_comparison`][paper_comparison] states (128) itself. The lower coefficient is reached through $\mathcal K\le Q$ and a direct closed-quantile bound, so Lean does not check the constant bookkeeping in Appendix E. |
| $R\le30001\,Q$ for every law | §14.6, Corollary 14.6 | [`closed_quantile_upper_30001`][closed_quantile_30001] | It runs $R\le28000\,\mathcal K'\le28000\,Q$. It is not the direct finite-law construction. |
| Lemma 13.1, attainment for finite laws | `entropy-tail-statement.tex` | [`BandwiseSuffixStatement`][BandwiseSuffix] | matches in form (61). The split of the remainder in form (62) relies on the paper-only equivalence. |
| Proof-vehicle $\mathcal K'$ | §18 | [`quantile_selectionValue_le`][bridge_le], [`quantile_selectionValue_eq`][bridge_eq] | $\mathcal K'\le\mathcal K$ for every measure, and $\mathcal K'=\mathcal K$ for every finite measure, hence for every probability law. |

**Name collisions.** `budgetScale` means $1/(4\sqrt B)$ in `Tier6` and
$(\sqrt B)^{-1}$ in `EntropyTailQuantile`. Each of `EntropyTailUpperStatement`,
`entropy_tail_upper`, `band`, `bandCost` and `costEntropy` also has two
meanings, in the `EntropyTail` and `EntropyTailQuantile` or
`EntropyTailExecution` namespaces. Check the namespace of every name you
read.

## 9. Where Lean is wider or narrower than the paper

| Item | Direction | Consequence |
|---|---|---|
| Seed spaces in universe 0; measurable algorithms only | narrower | Lower bounds transfer if every intended algorithm embeds. |
| No computability constraint; output defined when $T=\infty$ | wider | Strengthens the lower bounds; irrelevant under a finite budget. |
| $\theta=P_G(P>1/2)$ for general $G$ | partial | Lean works with $(\mu,q)$; the general $G$ form is a paper step. |
| Theorem 2.2's $\sup_q E Y^2\le23\,I_\mu$ | narrower | The locked [`Observable713Statement`][Observable713] states extended variance at most $23\,I_\mu$. The second-moment bound is proved only inside [`output_variance_le`][output_variance_le], not as a stated theorem. |
| Theorem 2.1's hidden-model confidence coefficient $15/(256\sqrt2)$ | narrower | Rests on the per-algorithm [`hidden_confidence_lower`][hidden_conf], which is axiom-audited but not an exact-type target. The minimax step is one `le_sInf`. The frozen confidence characterization carries $1/64$. |
| Hard-cap fallback (Theorem R.1) | wider | Lean needs the base-rule premise only at the $(\mu,q)$ where it concludes, and allows any $M\ge0$. |
| Hard-cap critical rate | wider | Lean covers every $B>0$; Theorem 11.2 states $B\ge1$. |
| Explicit upper coefficients | see §10 | 512, 28000, 30001 and others are in companion theorems, not in the locked types. |

## 10. What protects the statements, and the limits

- **What an audit checks.** Each audit restates a fixed target type, ascribes
  the registered theorem to it, and runs `#print axioms` on every registered
  declaration, allowing only the three standard axioms. Audits that use
  `validate_reports` also reject a `declaration uses 'sorry'` warning. The
  Uniform713 audit and the CriticalEntropy audit use their own exact-type
  paths.
- **Kernel trust.** No independent kernel replay such as `lean4checker` is
  run. `#print axioms` cannot see a declaration admitted with
  `set_option debug.skipKernelTC true`; the textual source scanner, which bans
  that option, is the only guard against it. Mathlib `.olean` files come from
  the cache for the pinned revision `9bdd0bc`, with Lean `v4.36.0-rc1`.
- **Locks.** `FROZEN.sha256`, the Tier 3-6 manifests, the 15 specification
  lock files, `HardBudget/SPECIFICATION.sha256`, the Uniform713 targets, the
  Route A lock and `blind_upper_components.json` were all recomputed and match.
  The locks have no external anchor: the hash of `TIER6_FROZEN.sha256` is
  recorded nowhere else, so one commit could change a specification, its lock
  and the verifier together. `HardBudget/SPECIFICATION.sha256` hashes only the
  specification bytes, not its imports.
- **Frozen before proof?** Git confirms that the lock commit precedes all the
  proofs for Confidence, OracleLower, RareAboveTwo, Observable713, HardBudget,
  EntropyTail (whose proof drafts were written outside the repository) and
  QuantileComparison. For BlindUpper and CriticalUpper it confirms only that
  the specification precedes the final assembly. For StoppingProgram the
  order is visible only in the history of the contributing branch. For Tier 6
  the lock arrives with the foundation proofs, one commit before the full
  theorem. CriticalPsi and EntropyTailQuantile rely on recorded timestamps
  only. UnbiasedConverse, ClosedQuantile, CriticalAllSizes, CriticalEntropy
  and EntropyTailLower were introduced with their proofs. For the latter
  groups, judge each statement on its content.
- **Unlocked definitions.** These carry the main content of Lean-checked rows
  but no lock covers them: [`rareConfidenceRadius`][rareConfidenceRadius],
  [`hardMinimaxRisk`][hardMinimaxRisk], [`hardRareMinimaxRisk`][hardRareMinimaxRisk],
  `populationPath` and the `ObservableSimulation` bridge. The CriticalEntropy
  [`CriticalMinimaxLowerStatement`][CriticalMinimaxLower] lives in a file
  named `Specification.lean` that imports its own proof. Its underlying
  `criticalMinimaxRisk` and `CriticalUniformBudget` are hash-pinned by
  review-time dependency snapshots. At `43d9fba`, 42 of the 70 verifiers
  that run Lake reference no lock. Their statements are protected by git history and by the
  source hashes in the published records.
- **Explicit constants.** Locked types that state their coefficients: Tier 6
  ($1/64$), Confidence ($1/64$, $8192$), OracleLower ($1/64$,
  $15/(256\sqrt2)$), Observable713 ($23$, $31$, $713$), UnbiasedConverse
  ($1/16$), StoppingProgram ($16$) and EntropyTailQuantile ($33000$). Locked
  types that assert only a positive constant: BlindUpper, EntropyTail,
  ClosedQuantile, RareAboveTwo and CriticalUpper; the unlocked
  `CriticalMinimaxLowerStatement` also asserts only a positive constant. The
  coefficients 512 ([`minimax_upper_bound`][minimax_upper_bound]), 28000
  ([`entropy_tail_upper_explicit`][tail_upper_explicit]), 30001 and 100000
  (critical upper) are in the types of audited companion theorems, and
  $512/(1-\alpha)$ and $8192/(1-\alpha)$ in inline audit statements for the
  row below one. The above-two coefficient $1/256$ appears only as the
  witness inside the proof of `rare_supported_lower`; no stated type carries
  it. The 512 companions use only locked Tier 6 definitions.
- **Instances.** Inline audit statements are elaborated after the proof
  modules are imported, so an imported instance could change how their type
  classes resolve. The tree has 137 `instance` declarations and two global
  `attribute [instance]` lines. Both of those register structure-field
  projections and cannot change how `MeasurableSpace R` resolves for a bound
  `R : Type`.
- **CI versus local records.** Run 42003950396 on `43d9fba` passed all five
  jobs. The published `results/` records come from local Windows runs, often
  with cached dependencies. `verify_entropy_tail_components.py` and
  `verify_entropy_tail_assembly.py` do not run in CI. The lock they check is
  checked in CI by `verify_entropy_tail_upper.py`.

## 11. Questions for the reviewer

1. Is the finite-prefix law in `transcriptLaw`, with each sign summed once
   outside the time product, the experiment of equation (3)? Is a pre-drawn,
   label-indexed gap array equivalent to creating coins on demand?
2. Does every algorithm you intend (independent seed, adaptive label choice,
   fresh randomization between steps) embed in `AdaptiveEstimator` with a seed
   space in universe 0? The lower bounds transfer only if it does.
3. Is a budget uniform over all sign laws (`UniformBudget`), and for rare
   events over $\mathcal Q_\rho$ only (`RareBudget`), the benchmark you intend?
4. Is `NullVarianceObstruction` the obstruction you would actually prove for a
   given law? It uses mixture variance, bias over the pointwise class
   $q\le1/2$, work under the all-negative prior, a deterministic cap and
   bounded output. For which laws is it known? Lean proves only the
   downstream `CommonPairBound`, and only for the quadratic critical law.
5. Is it acceptable that the $G$-form of the claims, $\theta=P_G(P>1/2)$ over
   all $G$ with $|P-1/2|\sim\mu$, rests on an unformalized disintegration?
6. Are the paper-only steps acceptable as stated: $c<C$ and the equivalence of
   (61) with (62) in Theorem 13.2, the constant bookkeeping of Appendix E, the
   second-moment sentence of Theorem 2.2, and the remark on charging for coin
   creation?
7. For each explicit coefficient you cite, read the companion theorem whose
   type carries it (section 10), not the locked existential target.
8. Read `hardMinimaxRisk`, `hardRareMinimaxRisk`, `rareConfidenceRadius` and
   `CriticalMinimaxLowerStatement` directly; no lock fixes them.
9. If kernel trust matters, rebuild with Lean `v4.36.0-rc1` and Mathlib
   `9bdd0bc` and replay the environment with `lean4checker`.

## Corrections made while preparing this brief

- Section 2's Formal scope and the Section 18 table credited the coefficient
  512 to `distribution_blind_upper`, whose locked type asserts only a positive
  constant. They now cite [`minimax_upper_bound`][minimax_upper_bound], and
  [RESULTS.md](RESULTS.md) and the toolkit docstring were aligned.
- Section 18's entropy-tail row now attributes 28000 to
  `entropy_tail_upper_explicit` rather than to the locked specification.
- Section 18 said the bridge gives $\mathcal K'=\mathcal K$ "for every finite
  law", meaning finitely supported laws. Lean proves it for every finite
  measure, hence for every probability law, and the text now says so.

Related guides: [claims and assumptions](RESULTS.md),
[verification by task](VERIFY.md#choose-checks-by-task),
[Lean concept map](../lean/README.md).

[transcriptLaw]: https://github.com/davidiach/adaptive-threshold-estimation/blob/43d9fba720332fe7f3b5dfbcfef137839e6cfef5/lean/ThresholdHC/Statements2.lean#L59-L62
[pathProb]: https://github.com/davidiach/adaptive-threshold-estimation/blob/43d9fba720332fe7f3b5dfbcfef137839e6cfef5/lean/ThresholdHC/Statements2.lean#L48-L55
[workOf]: https://github.com/davidiach/adaptive-threshold-estimation/blob/43d9fba720332fe7f3b5dfbcfef137839e6cfef5/lean/ThresholdHC/Statements2.lean#L65-L66
[creationLaw]: https://github.com/davidiach/adaptive-threshold-estimation/blob/43d9fba720332fe7f3b5dfbcfef137839e6cfef5/lean/ThresholdHC/Tier5/CreationModel.lean#L18-L21
[coinCap]: https://github.com/davidiach/adaptive-threshold-estimation/blob/43d9fba720332fe7f3b5dfbcfef137839e6cfef5/lean/ThresholdHC/Tier5/CreationModel.lean#L13-L15
[ProcessRealization]: https://github.com/davidiach/adaptive-threshold-estimation/blob/43d9fba720332fe7f3b5dfbcfef137839e6cfef5/lean/ThresholdHC/Tier6/Specification.lean#L10-L18
[process_realization]: https://github.com/davidiach/adaptive-threshold-estimation/blob/43d9fba720332fe7f3b5dfbcfef137839e6cfef5/lean/ThresholdHC/Tier6/Process.lean#L119
[population_realization]: https://github.com/davidiach/adaptive-threshold-estimation/blob/43d9fba720332fe7f3b5dfbcfef137839e6cfef5/lean/ThresholdHC/Tier6/Full.lean#L12
[RealizesCreationPrefixes]: https://github.com/davidiach/adaptive-threshold-estimation/blob/43d9fba720332fe7f3b5dfbcfef137839e6cfef5/lean/ThresholdHC/Tier5/Model.lean#L28-L36
[CreationStops]: https://github.com/davidiach/adaptive-threshold-estimation/blob/43d9fba720332fe7f3b5dfbcfef137839e6cfef5/lean/ThresholdHC/Tier5/Model.lean#L67-L77
[creation_stops]: https://github.com/davidiach/adaptive-threshold-estimation/blob/43d9fba720332fe7f3b5dfbcfef137839e6cfef5/lean/ThresholdHC/Tier5/StoppingBase.lean#L84
[MeasurableCreationPolicy]: https://github.com/davidiach/adaptive-threshold-estimation/blob/43d9fba720332fe7f3b5dfbcfef137839e6cfef5/lean/ThresholdHC/Tier5/Model.lean#L21-L23
[OptionNatSigma]: https://github.com/davidiach/adaptive-threshold-estimation/blob/43d9fba720332fe7f3b5dfbcfef137839e6cfef5/lean/ThresholdHC/Tier5/Model.lean#L19
[OptionBoolSigma]: https://github.com/davidiach/adaptive-threshold-estimation/blob/43d9fba720332fe7f3b5dfbcfef137839e6cfef5/lean/ThresholdHC/Tier4/Model.lean#L17
[creationTransition]: https://github.com/davidiach/adaptive-threshold-estimation/blob/43d9fba720332fe7f3b5dfbcfef137839e6cfef5/lean/ThresholdHC/Tier6/ProcessWeights.lean#L10-L13
[experimentLaw]: https://github.com/davidiach/adaptive-threshold-estimation/blob/43d9fba720332fe7f3b5dfbcfef137839e6cfef5/lean/ThresholdHC/Tier6/AlgorithmModel.lean#L10-L16
[expectedWork]: https://github.com/davidiach/adaptive-threshold-estimation/blob/43d9fba720332fe7f3b5dfbcfef137839e6cfef5/lean/ThresholdHC/Tier6/AlgorithmModel.lean#L24-L26
[UniformBudget]: https://github.com/davidiach/adaptive-threshold-estimation/blob/43d9fba720332fe7f3b5dfbcfef137839e6cfef5/lean/ThresholdHC/Tier6/AlgorithmModel.lean#L28-L30
[maximalRMSRisk]: https://github.com/davidiach/adaptive-threshold-estimation/blob/43d9fba720332fe7f3b5dfbcfef137839e6cfef5/lean/ThresholdHC/Tier6/AlgorithmModel.lean#L32-L41
[minimaxRisk]: https://github.com/davidiach/adaptive-threshold-estimation/blob/43d9fba720332fe7f3b5dfbcfef137839e6cfef5/lean/ThresholdHC/Tier6/AlgorithmModel.lean#L39-L41
[BudgetNonempty]: https://github.com/davidiach/adaptive-threshold-estimation/blob/43d9fba720332fe7f3b5dfbcfef137839e6cfef5/lean/ThresholdHC/Tier6/AlgorithmModel.lean#L59-L62
[minimaxRisk_le_one]: https://github.com/davidiach/adaptive-threshold-estimation/blob/43d9fba720332fe7f3b5dfbcfef137839e6cfef5/lean/ThresholdHC/Tier6/Full.lean#L24-L31
[SignLaw]: https://github.com/davidiach/adaptive-threshold-estimation/blob/43d9fba720332fe7f3b5dfbcfef137839e6cfef5/lean/ThresholdHC/Tier6/AlgorithmCore.lean#L18
[AdaptiveEstimator]: https://github.com/davidiach/adaptive-threshold-estimation/blob/43d9fba720332fe7f3b5dfbcfef137839e6cfef5/lean/ThresholdHC/Tier6/AlgorithmCore.lean#L20-L26
[PopulationSeed]: https://github.com/davidiach/adaptive-threshold-estimation/blob/43d9fba720332fe7f3b5dfbcfef137839e6cfef5/lean/ThresholdHC/Tier6/AlgorithmCore.lean#L31-L35
[populationPolicy]: https://github.com/davidiach/adaptive-threshold-estimation/blob/43d9fba720332fe7f3b5dfbcfef137839e6cfef5/lean/ThresholdHC/Tier6/AlgorithmCore.lean#L43-L44
[populationOutput]: https://github.com/davidiach/adaptive-threshold-estimation/blob/43d9fba720332fe7f3b5dfbcfef137839e6cfef5/lean/ThresholdHC/Tier6/AlgorithmCore.lean#L51-L52
[Gap]: https://github.com/davidiach/adaptive-threshold-estimation/blob/43d9fba720332fe7f3b5dfbcfef137839e6cfef5/lean/ThresholdHC/Tier6/HardPairModel.lean#L14
[modulus]: https://github.com/davidiach/adaptive-threshold-estimation/blob/43d9fba720332fe7f3b5dfbcfef137839e6cfef5/lean/ThresholdHC/Tier6/HardPairModel.lean#L16-L18
[signMean]: https://github.com/davidiach/adaptive-threshold-estimation/blob/43d9fba720332fe7f3b5dfbcfef137839e6cfef5/lean/ThresholdHC/Tier6/HardPairModel.lean#L26
[squaredRisk]: https://github.com/davidiach/adaptive-threshold-estimation/blob/43d9fba720332fe7f3b5dfbcfef137839e6cfef5/lean/ThresholdHC/Tier6/TestingModel.lean#L9-L11
[totalProcessWork]: https://github.com/davidiach/adaptive-threshold-estimation/blob/43d9fba720332fe7f3b5dfbcfef137839e6cfef5/lean/ThresholdHC/Tier3/StoppingModel.lean#L23-L24
[original_sim]: https://github.com/davidiach/adaptive-threshold-estimation/blob/43d9fba720332fe7f3b5dfbcfef137839e6cfef5/lean/ThresholdHC/ObservableSimulation/OriginalExperiment.lean#L42-L45
[BatchSeed]: https://github.com/davidiach/adaptive-threshold-estimation/blob/43d9fba720332fe7f3b5dfbcfef137839e6cfef5/lean/ThresholdHC/BlindUpper/SeedInput.lean#L23-L26
[BlindUpperSpec]: https://github.com/davidiach/adaptive-threshold-estimation/blob/43d9fba720332fe7f3b5dfbcfef137839e6cfef5/lean/ThresholdHC/BlindUpper/Specification.lean#L11-L16
[minimax_upper_bound]: https://github.com/davidiach/adaptive-threshold-estimation/blob/43d9fba720332fe7f3b5dfbcfef137839e6cfef5/lean/ThresholdHC/BlindUpper/Full.lean#L57-L58
[SelectedSemantics]: https://github.com/davidiach/adaptive-threshold-estimation/blob/43d9fba720332fe7f3b5dfbcfef137839e6cfef5/lean/ThresholdHC/OracleLower/Specification.lean#L21-L30
[oracle_stops]: https://github.com/davidiach/adaptive-threshold-estimation/blob/43d9fba720332fe7f3b5dfbcfef137839e6cfef5/lean/ThresholdHC/OracleLower/Nonvacuity.lean#L10-L18
[hidden_conf]: https://github.com/davidiach/adaptive-threshold-estimation/blob/43d9fba720332fe7f3b5dfbcfef137839e6cfef5/lean/ThresholdHC/OracleLower/Confidence.lean#L71-L76
[TerminalStops]: https://github.com/davidiach/adaptive-threshold-estimation/blob/43d9fba720332fe7f3b5dfbcfef137839e6cfef5/lean/ThresholdHC/ConfidenceTransfer/Terminal.lean#L30-L33
[TerminalInfoStops]: https://github.com/davidiach/adaptive-threshold-estimation/blob/43d9fba720332fe7f3b5dfbcfef137839e6cfef5/lean/ThresholdHC/RareAboveTwo/TerminalInformation.lean#L26-L29
[PathwiseCap]: https://github.com/davidiach/adaptive-threshold-estimation/blob/43d9fba720332fe7f3b5dfbcfef137839e6cfef5/lean/ThresholdHC/HardBudget/Specification.lean#L20-L22
[hardMinimaxRisk]: https://github.com/davidiach/adaptive-threshold-estimation/blob/43d9fba720332fe7f3b5dfbcfef137839e6cfef5/lean/ThresholdHC/HardBudget/Ordinary.lean#L10-L12
[hardRareMinimaxRisk]: https://github.com/davidiach/adaptive-threshold-estimation/blob/43d9fba720332fe7f3b5dfbcfef137839e6cfef5/lean/ThresholdHC/HardBudget/RareModel.lean#L9-L11
[RarePrior]: https://github.com/davidiach/adaptive-threshold-estimation/blob/43d9fba720332fe7f3b5dfbcfef137839e6cfef5/lean/ThresholdHC/RareAboveTwo/Model.lean#L19-L32
[RareBudget]: https://github.com/davidiach/adaptive-threshold-estimation/blob/43d9fba720332fe7f3b5dfbcfef137839e6cfef5/lean/ThresholdHC/RareAboveTwo/Model.lean#L21-L23
[rareMinimaxRisk]: https://github.com/davidiach/adaptive-threshold-estimation/blob/43d9fba720332fe7f3b5dfbcfef137839e6cfef5/lean/ThresholdHC/RareAboveTwo/Model.lean#L30-L32
[CriticalRareModel]: https://github.com/davidiach/adaptive-threshold-estimation/blob/43d9fba720332fe7f3b5dfbcfef137839e6cfef5/lean/ThresholdHC/CriticalEntropy/CriticalRareModel.lean#L12-L29
[critical_budget_eq]: https://github.com/davidiach/adaptive-threshold-estimation/blob/43d9fba720332fe7f3b5dfbcfef137839e6cfef5/lean/ThresholdHC/HardBudget/CriticalTransport.lean#L48-L49
[critical_risk_eq]: https://github.com/davidiach/adaptive-threshold-estimation/blob/43d9fba720332fe7f3b5dfbcfef137839e6cfef5/lean/ThresholdHC/HardBudget/CriticalTransport.lean#L59-L60
[minimaxConfidenceRadius]: https://github.com/davidiach/adaptive-threshold-estimation/blob/43d9fba720332fe7f3b5dfbcfef137839e6cfef5/lean/ThresholdHC/Confidence/Model.lean#L15-L32
[rareConfidenceRadius]: https://github.com/davidiach/adaptive-threshold-estimation/blob/43d9fba720332fe7f3b5dfbcfef137839e6cfef5/lean/ThresholdHC/ConfidenceTransfer/CommonPairRate.lean#L64-L68
[CommonPairBound]: https://github.com/davidiach/adaptive-threshold-estimation/blob/43d9fba720332fe7f3b5dfbcfef137839e6cfef5/lean/ThresholdHC/ConfidenceTransfer/CommonPairRate.lean#L11
[NullVarianceObstruction]: https://github.com/davidiach/adaptive-threshold-estimation/blob/43d9fba720332fe7f3b5dfbcfef137839e6cfef5/lean/ThresholdHC/ConfidenceLocalization/Obstruction.lean#L11-L21
[bias_lt_half]: https://github.com/davidiach/adaptive-threshold-estimation/blob/43d9fba720332fe7f3b5dfbcfef137839e6cfef5/lean/ThresholdHC/ConfidenceLocalization/Obstruction.lean#L23
[StoppedProcedure]: https://github.com/davidiach/adaptive-threshold-estimation/blob/43d9fba720332fe7f3b5dfbcfef137839e6cfef5/lean/ThresholdHC/CriticalEntropy/StoppedModel.lean#L24
[CappedPrior]: https://github.com/davidiach/adaptive-threshold-estimation/blob/43d9fba720332fe7f3b5dfbcfef137839e6cfef5/lean/ThresholdHC/CriticalEntropy/GoodGapModel.lean#L10-L12
[common_pair_obs]: https://github.com/davidiach/adaptive-threshold-estimation/blob/43d9fba720332fe7f3b5dfbcfef137839e6cfef5/lean/ThresholdHC/ConfidenceLocalization/CommonPair.lean#L13
[common_pair_bound]: https://github.com/davidiach/adaptive-threshold-estimation/blob/43d9fba720332fe7f3b5dfbcfef137839e6cfef5/lean/ThresholdHC/ConfidenceLocalization/ConfidenceRate.lean#L13
[hybrid]: https://github.com/davidiach/adaptive-threshold-estimation/blob/43d9fba720332fe7f3b5dfbcfef137839e6cfef5/lean/ThresholdHC/CriticalEntropy/FinitePopulation.lean#L317
[localSimulation]: https://github.com/davidiach/adaptive-threshold-estimation/blob/43d9fba720332fe7f3b5dfbcfef137839e6cfef5/lean/ThresholdHC/CriticalEntropy/LocalSimulation.lean#L13-L27
[affinity_le]: https://github.com/davidiach/adaptive-threshold-estimation/blob/43d9fba720332fe7f3b5dfbcfef137839e6cfef5/lean/ThresholdHC/CriticalEntropy/PopulationTransfer.lean#L41
[null_work]: https://github.com/davidiach/adaptive-threshold-estimation/blob/43d9fba720332fe7f3b5dfbcfef137839e6cfef5/lean/ThresholdHC/CriticalEntropy/MidpointWork.lean#L83
[finite_transfer]: https://github.com/davidiach/adaptive-threshold-estimation/blob/43d9fba720332fe7f3b5dfbcfef137839e6cfef5/lean/ThresholdHC/CriticalEntropy/PopulationTransfer.lean#L117
[mixPrior_rare]: https://github.com/davidiach/adaptive-threshold-estimation/blob/43d9fba720332fe7f3b5dfbcfef137839e6cfef5/lean/ThresholdHC/StoppingProgram/PriorMixtures.lean#L41
[creation_null]: https://github.com/davidiach/adaptive-threshold-estimation/blob/43d9fba720332fe7f3b5dfbcfef137839e6cfef5/lean/ThresholdHC/RMSLocalization/Creation.lean#L12
[creation_eq_finite]: https://github.com/davidiach/adaptive-threshold-estimation/blob/43d9fba720332fe7f3b5dfbcfef137839e6cfef5/lean/ThresholdHC/CriticalEntropy/CreationPopulation.lean#L19
[observable_pop]: https://github.com/davidiach/adaptive-threshold-estimation/blob/43d9fba720332fe7f3b5dfbcfef137839e6cfef5/lean/ThresholdHC/CriticalEntropy/SeededPopulationTransfer.lean#L12
[observable_null]: https://github.com/davidiach/adaptive-threshold-estimation/blob/43d9fba720332fe7f3b5dfbcfef137839e6cfef5/lean/ThresholdHC/RMSLocalization/Observable.lean#L18
[terminal_null]: https://github.com/davidiach/adaptive-threshold-estimation/blob/43d9fba720332fe7f3b5dfbcfef137839e6cfef5/lean/ThresholdHC/RMSLocalization/Terminal.lean#L12
[terminal_affinity]: https://github.com/davidiach/adaptive-threshold-estimation/blob/43d9fba720332fe7f3b5dfbcfef137839e6cfef5/lean/ThresholdHC/RareAboveTwo/TerminalInformation.lean#L56
[component_pair]: https://github.com/davidiach/adaptive-threshold-estimation/blob/43d9fba720332fe7f3b5dfbcfef137839e6cfef5/lean/ThresholdHC/AdditiveConfidence/ComponentPair.lean#L10
[pair_rms]: https://github.com/davidiach/adaptive-threshold-estimation/blob/43d9fba720332fe7f3b5dfbcfef137839e6cfef5/lean/ThresholdHC/RMSLocalization/PairRisk.lean#L11
[rms_rate_cp]: https://github.com/davidiach/adaptive-threshold-estimation/blob/43d9fba720332fe7f3b5dfbcfef137839e6cfef5/lean/ThresholdHC/RMSLocalization/CommonPair.lean#L10
[rms_rate_obs]: https://github.com/davidiach/adaptive-threshold-estimation/blob/43d9fba720332fe7f3b5dfbcfef137839e6cfef5/lean/ThresholdHC/RMSLocalization/CommonPair.lean#L30
[minimax_rms]: https://github.com/davidiach/adaptive-threshold-estimation/blob/43d9fba720332fe7f3b5dfbcfef137839e6cfef5/lean/ThresholdHC/RMSLocalization/CommonPair.lean#L39-L45
[critical_cp]: https://github.com/davidiach/adaptive-threshold-estimation/blob/43d9fba720332fe7f3b5dfbcfef137839e6cfef5/lean/ThresholdHC/ConfidenceTransfer/CriticalRate.lean#L12
[critical_lower]: https://github.com/davidiach/adaptive-threshold-estimation/blob/43d9fba720332fe7f3b5dfbcfef137839e6cfef5/lean/ThresholdHC/CriticalEntropy/CriticalMinimax.lean#L32
[CriticalMinimaxLower]: https://github.com/davidiach/adaptive-threshold-estimation/blob/43d9fba720332fe7f3b5dfbcfef137839e6cfef5/lean/ThresholdHC/CriticalEntropy/Specification.lean#L633-L638
[Observable713]: https://github.com/davidiach/adaptive-threshold-estimation/blob/43d9fba720332fe7f3b5dfbcfef137839e6cfef5/lean/ThresholdHC/Observable713/Specification.lean#L15-L24
[output_variance_le]: https://github.com/davidiach/adaptive-threshold-estimation/blob/43d9fba720332fe7f3b5dfbcfef137839e6cfef5/lean/ThresholdHC/Observable713/Realization.lean#L73-L90
[EntropyTailModel]: https://github.com/davidiach/adaptive-threshold-estimation/blob/43d9fba720332fe7f3b5dfbcfef137839e6cfef5/lean/ThresholdHC/EntropyTail/Model.lean#L16-L32
[selection]: https://github.com/davidiach/adaptive-threshold-estimation/blob/43d9fba720332fe7f3b5dfbcfef137839e6cfef5/lean/ThresholdHC/EntropyTail/Model.lean#L35-L45
[EntropyTailLaw]: https://github.com/davidiach/adaptive-threshold-estimation/blob/43d9fba720332fe7f3b5dfbcfef137839e6cfef5/lean/ThresholdHC/EntropyTail/Specification.lean#L16-L20
[tail_upper_explicit]: https://github.com/davidiach/adaptive-threshold-estimation/blob/43d9fba720332fe7f3b5dfbcfef137839e6cfef5/lean/ThresholdHC/EntropyTail/Upper.lean#L17-L19
[bridge_le]: https://github.com/davidiach/adaptive-threshold-estimation/blob/43d9fba720332fe7f3b5dfbcfef137839e6cfef5/lean/ThresholdHC/EntropyTail/Bridge.lean#L114-L115
[bridge_eq]: https://github.com/davidiach/adaptive-threshold-estimation/blob/43d9fba720332fe7f3b5dfbcfef137839e6cfef5/lean/ThresholdHC/EntropyTail/Bridge.lean#L128-L129
[closedQuantile]: https://github.com/davidiach/adaptive-threshold-estimation/blob/43d9fba720332fe7f3b5dfbcfef137839e6cfef5/lean/ThresholdHC/EntropyTailQuantile/Model.lean#L47-L66
[ExplicitLaw]: https://github.com/davidiach/adaptive-threshold-estimation/blob/43d9fba720332fe7f3b5dfbcfef137839e6cfef5/lean/ThresholdHC/EntropyTailSharp/Specification.lean#L11-L15
[paper_comparison]: https://github.com/davidiach/adaptive-threshold-estimation/blob/43d9fba720332fe7f3b5dfbcfef137839e6cfef5/lean/ThresholdHC/EntropyTailSharp/Full.lean#L94-L97
[closed_quantile_30001]: https://github.com/davidiach/adaptive-threshold-estimation/blob/43d9fba720332fe7f3b5dfbcfef137839e6cfef5/lean/ThresholdHC/EntropyTailExecution/UpperTheorem.lean#L92-L97
[BandwiseSuffix]: https://github.com/davidiach/adaptive-threshold-estimation/blob/43d9fba720332fe7f3b5dfbcfef137839e6cfef5/lean/ThresholdHC/BandwiseSuffix/Specification.lean#L17-L23
