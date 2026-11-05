import ThresholdHC.QuantileOptimality.Full
noncomputable section
set_option linter.unusedVariables false
open MeasureTheory Real Filter Set
open scoped BigOperators Topology ENNReal Classical
open ThresholdHC.Tier6 (Gap)
open ThresholdHC.BandwiseSuffix (packet)
open ThresholdHC.EntropyTailQuantile ThresholdHC.OptimalQuantile
open ThresholdHC.QuantileSharpLaw ThresholdHC.QuantileOptimality

example : ∀ (e : ℝ) (d : Gap),
    IsFiniteMeasure (packet e d) :=
  @ThresholdHC.QuantileOptimality.packet_finite

example : ∀ (σ : Measure Gap) {c : ℝ} (hc : 0 ≤ c) (j : ℕ),
    bandCost (ENNReal.ofReal c • σ) j = c*bandCost σ j :=
  @ThresholdHC.QuantileOptimality.bandCost_smul

example : ∀ (σ : Measure Gap) {c : ℝ} (hc : 0 ≤ c),
    measureCostEntropy (ENNReal.ofReal c • σ) = ENNReal.ofReal c*measureCostEntropy σ :=
  @ThresholdHC.QuantileOptimality.measureCostEntropy_smul

example : ∀ {e : ℝ} (he : 0 ≤ e) (d : Gap),
    (packet e d).real univ=e*(d : ℝ)^2 :=
  @ThresholdHC.QuantileOptimality.packet_real_mass

example : ∀ {e : ℝ} (he : 0 ≤ e) (d : Gap) (j : ℕ),
    bandCost (packet e d) j = if d ∈ band j then e else 0 :=
  @ThresholdHC.QuantileOptimality.packet_real_bandCost

example : ∀ {e : ℝ} (he : 0 ≤ e) (d : Gap),
    measureCostEntropy (packet e d) ≤ ENNReal.ofReal e :=
  @ThresholdHC.QuantileOptimality.packet_entropy_le

example : ∀ {e : ℝ} (he : 0 ≤ e) (d : Gap),
    (measureCostEntropy (packet e d)).toReal ≤ e :=
  @ThresholdHC.QuantileOptimality.packet_entropy_toReal_le

example : ∀ (μ : Measure Gap) [IsProbabilityMeasure μ]
    {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (d : Gap)
    (hs : ∀ᵐ x : Gap ∂μ, (d : ℝ) ≤ (x : ℝ)) (hm : ρ ≤ μ.real {d}),
    quantileThreshold μ ρ=(d : ℝ) :=
  @ThresholdHC.QuantileOptimality.quantileThreshold_at_min_atom

example : ∀ (μ : Measure Gap) [IsProbabilityMeasure μ]
    {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (d : Gap)
    (hs : ∀ᵐ x : Gap ∂μ, (d : ℝ) ≤ (x : ℝ)) (hm : ρ ≤ μ.real {d}),
    quantileTail μ ρ = ENNReal.ofReal ρ • Measure.dirac d :=
  @ThresholdHC.QuantileOptimality.quantileTail_at_min_atom

example : ∀ {m : ℕ} (x : Option (Fin m) → ℝ) (f : ℝ → ℝ),
    (∑ i, f (packedCosts x i)) = ∑ i, f (x i) :=
  @ThresholdHC.QuantileOptimality.packedCosts_sum

example : ∀ {m : ℕ} (x : Option (Fin m) → ℝ),
    costEntropy (packedCosts x)=costEntropy x :=
  @ThresholdHC.QuantileOptimality.packedCosts_entropy

example : ∀ {m : ℕ} {x : Option (Fin m) → ℝ} (hx : ∀ i, 0 ≤ x i)
    (i : Fin (m+1)),
    0 ≤ packedCosts x i :=
  @ThresholdHC.QuantileOptimality.packedCosts_nonneg

example : ∀ {k m : ℕ} (v : Fin m → ℝ),
    costEntropy (Fin.append (0 : Fin k → ℝ) v)=costEntropy v :=
  @ThresholdHC.QuantileOptimality.costEntropy_zero_append

example : ∀ {k m : ℕ} {a : Fin (k+m) → ℝ} {v : Fin m → ℝ}
    (ha : ∀ i, 0 ≤ a i) (hv : ∀ i, 0 ≤ v i) (hblock : ∀ i, v i ≤ a (Fin.natAdd k i)),
    costEntropy v ≤ costEntropy a :=
  @ThresholdHC.QuantileOptimality.costEntropy_tail_block_le

example : ∀ {m n : ℕ} (hn : m+2 ≤ n) {η : ℝ} (hη : 0 < η) (hη1 : η ≤ 1)
    (j : Fin m),
    coreGap hn η hη hη1 j ∈ band (n-(j.val+1)) :=
  @ThresholdHC.QuantileOptimality.coreGap_band_index

example : ∀ {m n : ℕ} (hn : m+2 ≤ n) {x : Option (Fin m) → ℝ}
    (hx : ∀ i, 0 ≤ x i) {η : ℝ} (hη : 0 < η) (hη1 : η ≤ 1),
    ENNReal.ofReal (inverseScale n x*costEntropy x) ≤
      measureCostEntropy (realizingCore hn x η hη hη1) :=
  @ThresholdHC.QuantileOptimality.realizingCore_entropy_lower

example : ∀ {m n : ℕ} (hn : m+2 ≤ n) {x : Option (Fin m) → ℝ}
    (hx : ∀ i, 0 ≤ x i) {η : ℝ} (hη : 0 < η) (hη1 : η ≤ 1),
    ENNReal.ofReal (inverseScale n x*costEntropy x) ≤
      measureCostEntropy (quantileCore (realizingLaw hn x η hη hη1) (chosenRarity m x)) :=
  @ThresholdHC.QuantileOptimality.quantileCore_entropy_lower

example : ∀ {m : ℕ} (n : ℕ) (x : Option (Fin m) → ℝ),
    packet (inverseScale n x) (edgeGap n)=ENNReal.ofReal (chosenRarity m x) • Measure.dirac (edgeGap n) :=
  @ThresholdHC.QuantileOptimality.tail_packet_identity

example : ∀ {m : ℕ} (n : ℕ) {x : Option (Fin m) → ℝ} (hx : ∀ i, 0 ≤ x i),
    boundaryAtom n x=packet (inverseScale n x) (edgeGap n)+boundaryCore n x :=
  @ThresholdHC.QuantileOptimality.boundaryAtom_split

example : ∀ {m n : ℕ} (hn : m+2 ≤ n) {x : Option (Fin m) → ℝ}
    (hx : ∀ i, 0 ≤ x i) {η : ℝ} (hη : 0 < η) (hη1 : η ≤ 1),
    realizingLaw hn x η hη hη1 = packet (inverseScale n x) (edgeGap n)+realizingCore hn x η hη hη1 :=
  @ThresholdHC.QuantileOptimality.realizingLaw_split

example : ∀ {m n : ℕ} (hn : m+2 ≤ n) {x : Option (Fin m) → ℝ}
    (hx : ∀ i, 0 ≤ x i) {η : ℝ} (hη : 0 < η) (hη1 : η ≤ 1),
    quantileCore (realizingLaw hn x η hη hη1) (chosenRarity m x)=realizingCore hn x η hη hη1 :=
  @ThresholdHC.QuantileOptimality.realizingLaw_quantileCore

example : ∀ {m n : ℕ} (hn : m+2 ≤ n) (x : Option (Fin m) → ℝ)
    {η : ℝ} (hη : 0 < η) (hη1 : η ≤ 1),
    boundaryCore n x ≤ realizingCore hn x η hη hη1 :=
  @ThresholdHC.QuantileOptimality.boundaryCore_le_realizingCore

example : ∀ {m n : ℕ} (hn : m+2 ≤ n) (x : Option (Fin m) → ℝ)
    {η : ℝ} (hη : 0 < η) (hη1 : η ≤ 1) (j : Fin m),
    packet (inverseScale n x*x (some j)) (coreGap hn η hη hη1 j) ≤ realizingCore hn x η hη hη1 :=
  @ThresholdHC.QuantileOptimality.skipped_packet_le_realizingCore

example : FiniteSharpnessStatement :=
  @ThresholdHC.QuantileOptimality.finite_sharpness

example : ∀ (k : ℝ),
    UniversalFactor k ↔ scalarRoot ≤ k :=
  @ThresholdHC.QuantileOptimality.universalFactor_iff

example : ∀ (k : ℝ),
    FiniteUniversalFactor k ↔ scalarRoot ≤ k :=
  @ThresholdHC.QuantileOptimality.finiteUniversalFactor_iff

example : ∀ (k : ℝ),
    UniversalFactor k ↔ FiniteUniversalFactor k :=
  @ThresholdHC.QuantileOptimality.general_and_finite_factors_iff

example : ∀ (n : ℕ),
    edgeGap n ∈ band n :=
  @ThresholdHC.QuantileOptimality.edgeGap_band

example : ∀ {n : ℕ} (i : Fin n) {η : ℝ} (hη : 0 < η) (hη1 : η ≤ 1),
    aboveGap i η hη hη1 ∈ band i.rev.val :=
  @ThresholdHC.QuantileOptimality.aboveGap_band

example : ∀ {n : ℕ} (i : Fin n) {η : ℝ} (hη : 0 < η) (hη1 : η ≤ 1),
    bandEdge n < (aboveGap i η hη hη1 : ℝ) :=
  @ThresholdHC.QuantileOptimality.aboveGap_gt_boundary

example : ∀ {n : ℕ} (i : Fin n) {η : ℝ} (hη : 0 < η) (hη1 : η ≤ 1)
    (hi : i.val+1 < n),
    (aboveGap i η hη hη1 : ℝ) < 1/2 :=
  @ThresholdHC.QuantileOptimality.aboveGap_lt_half

example : ∀ {m : ℕ} (n : ℕ) (x : Option (Fin m) → ℝ) (η : ℝ),
    ∀ᵐ z : Gap ∂keptMeasure n x η, bandEdge n ≤ (z : ℝ) :=
  @ThresholdHC.QuantileOptimality.keptMeasure_support_lower

example : ∀ {m : ℕ} (n : ℕ) {x : Option (Fin m) → ℝ}
    (hx : ∀ i, 0 ≤ x i) {η : ℝ} (hη : 0 ≤ η) (hη1 : η ≤ 1),
    (measureCostEntropy (keptMeasure n x η)).toReal ≤
      inverseScale n x*finiteEnvelope (chosenRarity m x) (1+x none) (bandEdge n) :=
  @ThresholdHC.QuantileOptimality.keptMeasure_entropy_bound

example : ∀ {m n : ℕ} (hn : m+2 ≤ n) (x : Option (Fin m) → ℝ)
    {η : ℝ} (hη : 0 < η) (hη1 : η ≤ 1),
    realizingLaw hn x η hη hη1-keptMeasure n x η=skippedAtoms hn x η hη hη1 :=
  @ThresholdHC.QuantileOptimality.realizingLaw_sub_kept

example : ∀ {m n : ℕ} (hn : m+2 ≤ n) {x : Option (Fin m) → ℝ}
    (hx : ∀ i, 0 ≤ x i) {η h : ℝ} (hη : 0 < η) (hη1 : η ≤ 1)
    (hh : 0 ≤ h) (hsmall : h ≤ bandEdge n),
    tailModulus (skippedAtoms hn x η hη hη1) h =
      (h*chosenRarity m x/bandEdge n)*(1+η)*dyadicCost m x :=
  @ThresholdHC.QuantileOptimality.skippedAtoms_tailModulus

example : ∀ {m : ℕ} (n : ℕ) {x : Option (Fin m) → ℝ} (hx : ∀ i, 0 ≤ x i),
    0 < inverseScale n x :=
  @ThresholdHC.QuantileOptimality.inverseScale_pos

example : ∀ {m : ℕ} (n : ℕ) {x : Option (Fin m) → ℝ} (hx : ∀ i, 0 ≤ x i),
    (boundaryAtom n x).real univ=chosenRarity m x*(1+x none) :=
  @ThresholdHC.QuantileOptimality.boundaryAtom_mass

example : ∀ {m n : ℕ} (hn : m+2 ≤ n) {x : Option (Fin m) → ℝ}
    (hx : ∀ i, 0 ≤ x i) {η : ℝ} (hη : 0 < η) (hη1 : η ≤ 1),
    (skippedAtoms hn x η hη hη1).real univ =
      chosenRarity m x*(∑ j : Fin m, x (some j)*((2 : ℝ)^j.val*(1+η))^2) :=
  @ThresholdHC.QuantileOptimality.skippedAtoms_mass

example : ∀ {m : ℕ} {x : Option (Fin m) → ℝ} (hx : ∀ i, 0 ≤ x i)
    {η : ℝ} (hη : 0 ≤ η) (hη1 : η ≤ 1),
    (easyAtom x η).real univ=easyMass m x η :=
  @ThresholdHC.QuantileOptimality.easyAtom_mass

example : ∀ {m n : ℕ} (hn : m+2 ≤ n) {x : Option (Fin m) → ℝ}
    (hx : ∀ i, 0 ≤ x i) {η : ℝ} (hη : 0 < η) (hη1 : η ≤ 1),
    (realizingLaw hn x η hη hη1).real univ=1 :=
  @ThresholdHC.QuantileOptimality.realizingLaw_mass

example : ∀ {m n : ℕ} (hn : m+2 ≤ n) {x : Option (Fin m) → ℝ}
    (hx : ∀ i, 0 ≤ x i) {η : ℝ} (hη : 0 < η) (hη1 : η ≤ 1),
    IsProbabilityMeasure (realizingLaw hn x η hη hη1) :=
  @ThresholdHC.QuantileOptimality.realizingLaw_probability

example : ∀ {m n : ℕ} (hn : m+2 ≤ n) {η : ℝ} (hη : 0 < η) (hη1 : η ≤ 1)
    (j : Fin m),
    bandEdge n < (coreGap hn η hη hη1 j : ℝ) :=
  @ThresholdHC.QuantileOptimality.coreGap_gt_edge

example : ∀ {m n : ℕ} (hn : m+2 ≤ n) {η : ℝ} (hη : 0 < η) (hη1 : η ≤ 1)
    (j : Fin m),
    (coreGap hn η hη hη1 j : ℝ) < 1/2 :=
  @ThresholdHC.QuantileOptimality.coreGap_lt_half

example : ∀ {ι : Type*} (s : Finset ι) (e : ι → ℝ) (d : ι → Gap)
    {t : ℝ} (ht : ∀ i, t ≤ (d i : ℝ)),
    ∀ᵐ z : Gap ∂(∑ i ∈ s, packet (e i) (d i)), t ≤ (z : ℝ) :=
  @ThresholdHC.QuantileOptimality.packet_sum_support_lower

example : ∀ {m n : ℕ} (hn : m+2 ≤ n) (x : Option (Fin m) → ℝ)
    {η : ℝ} (hη : 0 < η) (hη1 : η ≤ 1),
    ∀ᵐ z : Gap ∂realizingLaw hn x η hη hη1, bandEdge n ≤ (z : ℝ) :=
  @ThresholdHC.QuantileOptimality.realizingLaw_support_lower

example : ∀ {m n : ℕ} (hn : m+2 ≤ n) (x : Option (Fin m) → ℝ)
    {η : ℝ} (hη : 0 < η) (hη1 : η ≤ 1),
    (realizingLaw hn x η hη hη1).support.Finite :=
  @ThresholdHC.QuantileOptimality.realizingLaw_support_finite

example : ∀ {m n : ℕ} (hn : m+2 ≤ n) (x : Option (Fin m) → ℝ)
    {η : ℝ} (hη : 0 < η) (hη1 : η ≤ 1),
    keptMeasure n x η ≤ realizingLaw hn x η hη hη1 :=
  @ThresholdHC.QuantileOptimality.keptMeasure_le_law

example : ∀ {m n : ℕ} (hn : m+2 ≤ n) (x : Option (Fin m) → ℝ)
    {η : ℝ} (hη : 0 < η) (hη1 : η ≤ 1),
    boundaryAtom n x ≤ realizingLaw hn x η hη hη1 :=
  @ThresholdHC.QuantileOptimality.boundaryAtom_le_law

example : ∀ {m : ℕ} (n : ℕ) {x : Option (Fin m) → ℝ}
    (hx : ∀ i, 0 ≤ x i),
    (boundaryAtom n x).real {edgeGap n} = chosenRarity m x*(1+x none) :=
  @ThresholdHC.QuantileOptimality.boundaryAtom_mass_at_edge

example : ∀ {m n : ℕ} (hn : m+2 ≤ n) {x : Option (Fin m) → ℝ}
    (hx : ∀ i, 0 ≤ x i) {η : ℝ} (hη : 0 < η) (hη1 : η ≤ 1),
    chosenRarity m x ≤ (realizingLaw hn x η hη hη1).real {edgeGap n} :=
  @ThresholdHC.QuantileOptimality.realizingLaw_atom_lower

example : ∀ {m n : ℕ} (hn : m+2 ≤ n) {x : Option (Fin m) → ℝ}
    (hx : ∀ i, 0 ≤ x i) {η : ℝ} (hη : 0 < η) (hη1 : η ≤ 1),
    quantileTail (realizingLaw hn x η hη hη1) (chosenRarity m x) =
      ENNReal.ofReal (chosenRarity m x) • Measure.dirac (edgeGap n) :=
  @ThresholdHC.QuantileOptimality.realizingLaw_quantileTail

example : Tendsto bandEdge atTop (𝓝 (0 : ℝ)) :=
  @ThresholdHC.QuantileOptimality.bandEdge_tendsto_zero

example : ∀ (m : ℕ),
    Tendsto (fun N : ℕ => bandEdge (m+N+2)) atTop (𝓝 (0 : ℝ)) :=
  @ThresholdHC.QuantileOptimality.shifted_bandEdge_tendsto_zero

example : ∀ {m : ℕ} (x : Option (Fin m) → ℝ),
    Tendsto (fun N : ℕ =>
      sqrt (finiteEnvelope (chosenRarity m x) (1+x none) (bandEdge (m+N+2)))+
        (1+bandEdge N)*dyadicCost m x) atTop (𝓝 (sqrt (1+x none)+dyadicCost m x)) :=
  @ThresholdHC.QuantileOptimality.finite_price_tendsto

example : ∀ {m : ℕ} (x : Option (Fin m) → ℝ) {k C : ℝ}
    (hprice : k*(sqrt (1+x none)+dyadicCost m x) < C),
    ∃ N : ℕ, k*(sqrt (finiteEnvelope (chosenRarity m x) (1+x none) (bandEdge (m+N+2)))+
      (1+bandEdge N)*dyadicCost m x) < C :=
  @ThresholdHC.QuantileOptimality.exists_finite_price_witness

example : ∀ {m : ℕ} {x : Option (Fin m) → ℝ} (hx : ∀ i, 0 ≤ x i),
    1 ≤ upperMass m x :=
  @ThresholdHC.QuantileOptimality.upperMass_ge_one

example : ∀ {m : ℕ} {x : Option (Fin m) → ℝ} (hx : ∀ i, 0 ≤ x i),
    0 < chosenRarity m x :=
  @ThresholdHC.QuantileOptimality.chosenRarity_pos

example : ∀ {m : ℕ} {x : Option (Fin m) → ℝ} (hx : ∀ i, 0 ≤ x i),
    chosenRarity m x ≤ 1/4 :=
  @ThresholdHC.QuantileOptimality.chosenRarity_le_quarter

example : ∀ {m : ℕ} {x : Option (Fin m) → ℝ} (hx : ∀ i, 0 ≤ x i) (η : ℝ),
    1 ≤ massScale m x η :=
  @ThresholdHC.QuantileOptimality.massScale_ge_one

example : ∀ {m : ℕ} {x : Option (Fin m) → ℝ} (hx : ∀ i, 0 ≤ x i)
    {η : ℝ} (hη : 0 ≤ η) (hη1 : η ≤ 1),
    massScale m x η ≤ upperMass m x :=
  @ThresholdHC.QuantileOptimality.massScale_le_upperMass

example : ∀ {m : ℕ} {x : Option (Fin m) → ℝ} (hx : ∀ i, 0 ≤ x i)
    {η : ℝ} (hη : 0 ≤ η) (hη1 : η ≤ 1),
    3/4 ≤ easyMass m x η ∧ easyMass m x η ≤ 1 :=
  @ThresholdHC.QuantileOptimality.easyMass_bounds

example : ∀ {e f : ℝ} (he : 0 ≤ e) (hf : 0 ≤ f) (d : Gap),
    packet (e+f) d=packet e d+packet f d :=
  @ThresholdHC.QuantileOptimality.packet_add

example : ∀ {e : ℝ} (he : 0 ≤ e) (d : Gap) (h : ℝ),
    tailModulus (packet e d) h=(e*(d : ℝ)^2)*min 1 (h/(d : ℝ)) :=
  @ThresholdHC.QuantileOptimality.packet_tailModulus

example : ∀ {e : ℝ} (he : 0 ≤ e) (d : Gap) {h : ℝ} (hhd : h ≤ (d : ℝ)),
    tailModulus (packet e d) h=e*h*(d : ℝ) :=
  @ThresholdHC.QuantileOptimality.packet_tailModulus_of_small

example : ∀ {ι : Type*} (s : Finset ι) (μ : ι → Measure Gap)
    [∀ i, IsFiniteMeasure (μ i)] {h : ℝ} (hh : 0 ≤ h),
    tailModulus (∑ i ∈ s, μ i) h=∑ i ∈ s, tailModulus (μ i) h :=
  @ThresholdHC.QuantileOptimality.tailModulus_finset_sum

example : ∀ {ι : Type*} (s : Finset ι) (e : ι → ℝ) (d : ι → Gap)
    (he : ∀ i, 0 ≤ e i),
    (∑ i ∈ s, packet (e i) (d i)).real univ=∑ i ∈ s, e i*(d i : ℝ)^2 :=
  @ThresholdHC.QuantileOptimality.packet_sum_mass

example : ∀ {ρ t G : ℝ} (hρ : 0 < ρ) (ht : 0 < t) (hG : 0 ≤ G),
    sqrt (ρ*(ρ/t^2*G)) = (ρ/t)*sqrt G :=
  @ThresholdHC.QuantileOptimality.atom_root_identity

example : ∀ {ρ A t : ℝ} (hρ : 0 < ρ) (hA : 0 ≤ A),
    0 ≤ finiteEnvelope ρ A t :=
  @ThresholdHC.QuantileOptimality.finiteEnvelope_nonneg

example : ∀ {ρ A t : ℝ} (hρ : 0 < ρ) (hA : 0 ≤ A) (ht : 0 < t),
    (ρ/t^2)*finiteEnvelope ρ A t =
      (ρ/t^2)*A+4+sqrt (2*((ρ/t^2)*A)*4) :=
  @ThresholdHC.QuantileOptimality.finiteEnvelope_scale

example : ∀ (ρ A : ℝ),
    Continuous (finiteEnvelope ρ A) :=
  @ThresholdHC.QuantileOptimality.finiteEnvelope_continuous

example : ∀ (ρ A : ℝ),
    finiteEnvelope ρ A 0=A :=
  @ThresholdHC.QuantileOptimality.finiteEnvelope_zero

example : ∀ {m n : ℕ} (hn : m+2 ≤ n) {x : Option (Fin m) → ℝ}
    (hx : ∀ i, 0 ≤ x i) {η h : ℝ} (hη : 0 < η) (hη1 : η ≤ 1) (hsmall : h ≤ bandEdge n),
    tailModulus (quantileTail (realizingLaw hn x η hη hη1) (chosenRarity m x)) h =
      h*chosenRarity m x/bandEdge n :=
  @ThresholdHC.QuantileOptimality.realizing_tailModulus

example : ∀ {m n : ℕ} (hn : m+2 ≤ n) {x : Option (Fin m) → ℝ}
    (hx : ∀ i, 0 ≤ x i) {η h : ℝ} (hη : 0 < η) (hη1 : η ≤ 1)
    (hh : 0 < h) (hsmall : h ≤ bandEdge n)
    (hclip : (h*chosenRarity m x/bandEdge n)*(1+sqrt (costEntropy x)) ≤ chosenRarity m x),
    ENNReal.ofReal ((h*chosenRarity m x/bandEdge n)*(1+sqrt (costEntropy x))) ≤
      closedQuantileValue (realizingLaw hn x η hη hη1) (chosenRarity m x) (h⁻¹^2) :=
  @ThresholdHC.QuantileOptimality.quantile_lower_explicit_budget

example : ∀ {h : ℝ} (hh : 0 < h),
    budgetScale (h⁻¹^2)=h :=
  @ThresholdHC.QuantileOptimality.budgetScale_invSquare

example : ∀ {m n : ℕ} (hn : m+2 ≤ n) {x : Option (Fin m) → ℝ}
    (hx : ∀ i, 0 ≤ x i) {η h : ℝ} (hη : 0 < η) (hη1 : η ≤ 1)
    (hh : 0 ≤ h) (hsmall : h ≤ bandEdge n),
    selectionCost (realizingLaw hn x η hη hη1) (keptMeasure n x η) (chosenRarity m x) h ≤
      ENNReal.ofReal ((h*chosenRarity m x/bandEdge n)*
        (sqrt (finiteEnvelope (chosenRarity m x) (1+x none) (bandEdge n))+(1+η)*dyadicCost m x)) :=
  @ThresholdHC.QuantileOptimality.kept_selectionCost_bound

example : ∀ {m n : ℕ} (hn : m+2 ≤ n) {x : Option (Fin m) → ℝ}
    (hx : ∀ i, 0 ≤ x i) {η h : ℝ} (hη : 0 < η) (hη1 : η ≤ 1)
    (hh : 0 < h) (hsmall : h ≤ bandEdge n),
    ThresholdHC.EntropyTail.selection (realizingLaw hn x η hη hη1) (chosenRarity m x) (h⁻¹^2) ≤
      ENNReal.ofReal ((h*chosenRarity m x/bandEdge n)*
        (sqrt (finiteEnvelope (chosenRarity m x) (1+x none) (bandEdge n))+(1+η)*dyadicCost m x)) :=
  @ThresholdHC.QuantileOptimality.selection_bound_explicit_budget

example : ∀ (e : ℝ) (d : Gap),
    (packet e d).support ⊆ {d} :=
  @ThresholdHC.QuantileOptimality.packet_support_subset

example : ∀ (e : ℝ) (d : Gap),
    (packet e d).support.Finite :=
  @ThresholdHC.QuantileOptimality.packet_support_finite

example : ∀ {ι : Type*} (s : Finset ι) (e : ι → ℝ) (d : ι → Gap),
    (∑ i ∈ s, packet (e i) (d i)).support.Finite :=
  @ThresholdHC.QuantileOptimality.packet_sum_support_finite

example : ∀ (e : ℝ) (d : Gap),
    ∀ᵐ x : Gap ∂packet e d, (d : ℝ) ≤ (x : ℝ) :=
  @ThresholdHC.QuantileOptimality.packet_support_lower

example : ∀ {m : ℕ} (x : Option (Fin m) → ℝ) (hx : ∀ i, 0 ≤ x i)
    {k : ℝ} (hk : 0 ≤ k)
    (hprice : k*(sqrt (1+x none)+dyadicCost m x) < 1+sqrt (costEntropy x)),
    ∃ (μ : Measure Gap) (_ : IsProbabilityMeasure μ),
      μ.support.Finite ∧ ∃ ρ B : ℝ, 0 < ρ ∧ ρ ≤ 1/4 ∧ 0 < B ∧
        ENNReal.ofReal k*ThresholdHC.EntropyTail.selection μ ρ B < closedQuantileValue μ ρ B :=
  @ThresholdHC.QuantileOptimality.finite_law_witness
#print axioms ThresholdHC.QuantileOptimality.aboveGap_band
#print axioms ThresholdHC.QuantileOptimality.aboveGap_gt_boundary
#print axioms ThresholdHC.QuantileOptimality.aboveGap_lt_half
#print axioms ThresholdHC.QuantileOptimality.atom_root_identity
#print axioms ThresholdHC.QuantileOptimality.bandCost_smul
#print axioms ThresholdHC.QuantileOptimality.bandEdge_tendsto_zero
#print axioms ThresholdHC.QuantileOptimality.boundaryAtom_le_law
#print axioms ThresholdHC.QuantileOptimality.boundaryAtom_mass
#print axioms ThresholdHC.QuantileOptimality.boundaryAtom_mass_at_edge
#print axioms ThresholdHC.QuantileOptimality.boundaryAtom_split
#print axioms ThresholdHC.QuantileOptimality.boundaryCore_le_realizingCore
#print axioms ThresholdHC.QuantileOptimality.budgetScale_invSquare
#print axioms ThresholdHC.QuantileOptimality.chosenRarity_le_quarter
#print axioms ThresholdHC.QuantileOptimality.chosenRarity_pos
#print axioms ThresholdHC.QuantileOptimality.coreGap_band_index
#print axioms ThresholdHC.QuantileOptimality.coreGap_gt_edge
#print axioms ThresholdHC.QuantileOptimality.coreGap_lt_half
#print axioms ThresholdHC.QuantileOptimality.costEntropy_tail_block_le
#print axioms ThresholdHC.QuantileOptimality.costEntropy_zero_append
#print axioms ThresholdHC.QuantileOptimality.easyAtom_mass
#print axioms ThresholdHC.QuantileOptimality.easyMass_bounds
#print axioms ThresholdHC.QuantileOptimality.edgeGap_band
#print axioms ThresholdHC.QuantileOptimality.exists_finite_price_witness
#print axioms ThresholdHC.QuantileOptimality.finiteEnvelope_continuous
#print axioms ThresholdHC.QuantileOptimality.finiteEnvelope_nonneg
#print axioms ThresholdHC.QuantileOptimality.finiteEnvelope_scale
#print axioms ThresholdHC.QuantileOptimality.finiteEnvelope_zero
#print axioms ThresholdHC.QuantileOptimality.finiteUniversalFactor_iff
#print axioms ThresholdHC.QuantileOptimality.finite_law_witness
#print axioms ThresholdHC.QuantileOptimality.finite_price_tendsto
#print axioms ThresholdHC.QuantileOptimality.finite_sharpness
#print axioms ThresholdHC.QuantileOptimality.general_and_finite_factors_iff
#print axioms ThresholdHC.QuantileOptimality.inverseScale_pos
#print axioms ThresholdHC.QuantileOptimality.keptMeasure_entropy_bound
#print axioms ThresholdHC.QuantileOptimality.keptMeasure_le_law
#print axioms ThresholdHC.QuantileOptimality.keptMeasure_support_lower
#print axioms ThresholdHC.QuantileOptimality.kept_selectionCost_bound
#print axioms ThresholdHC.QuantileOptimality.massScale_ge_one
#print axioms ThresholdHC.QuantileOptimality.massScale_le_upperMass
#print axioms ThresholdHC.QuantileOptimality.measureCostEntropy_smul
#print axioms ThresholdHC.QuantileOptimality.packedCosts_entropy
#print axioms ThresholdHC.QuantileOptimality.packedCosts_nonneg
#print axioms ThresholdHC.QuantileOptimality.packedCosts_sum
#print axioms ThresholdHC.QuantileOptimality.packet_add
#print axioms ThresholdHC.QuantileOptimality.packet_entropy_le
#print axioms ThresholdHC.QuantileOptimality.packet_entropy_toReal_le
#print axioms ThresholdHC.QuantileOptimality.packet_finite
#print axioms ThresholdHC.QuantileOptimality.packet_real_bandCost
#print axioms ThresholdHC.QuantileOptimality.packet_real_mass
#print axioms ThresholdHC.QuantileOptimality.packet_sum_mass
#print axioms ThresholdHC.QuantileOptimality.packet_sum_support_finite
#print axioms ThresholdHC.QuantileOptimality.packet_sum_support_lower
#print axioms ThresholdHC.QuantileOptimality.packet_support_finite
#print axioms ThresholdHC.QuantileOptimality.packet_support_lower
#print axioms ThresholdHC.QuantileOptimality.packet_support_subset
#print axioms ThresholdHC.QuantileOptimality.packet_tailModulus
#print axioms ThresholdHC.QuantileOptimality.packet_tailModulus_of_small
#print axioms ThresholdHC.QuantileOptimality.quantileCore_entropy_lower
#print axioms ThresholdHC.QuantileOptimality.quantileTail_at_min_atom
#print axioms ThresholdHC.QuantileOptimality.quantileThreshold_at_min_atom
#print axioms ThresholdHC.QuantileOptimality.quantile_lower_explicit_budget
#print axioms ThresholdHC.QuantileOptimality.realizingCore_entropy_lower
#print axioms ThresholdHC.QuantileOptimality.realizingLaw_atom_lower
#print axioms ThresholdHC.QuantileOptimality.realizingLaw_mass
#print axioms ThresholdHC.QuantileOptimality.realizingLaw_probability
#print axioms ThresholdHC.QuantileOptimality.realizingLaw_quantileCore
#print axioms ThresholdHC.QuantileOptimality.realizingLaw_quantileTail
#print axioms ThresholdHC.QuantileOptimality.realizingLaw_split
#print axioms ThresholdHC.QuantileOptimality.realizingLaw_sub_kept
#print axioms ThresholdHC.QuantileOptimality.realizingLaw_support_finite
#print axioms ThresholdHC.QuantileOptimality.realizingLaw_support_lower
#print axioms ThresholdHC.QuantileOptimality.realizing_tailModulus
#print axioms ThresholdHC.QuantileOptimality.selection_bound_explicit_budget
#print axioms ThresholdHC.QuantileOptimality.shifted_bandEdge_tendsto_zero
#print axioms ThresholdHC.QuantileOptimality.skippedAtoms_mass
#print axioms ThresholdHC.QuantileOptimality.skippedAtoms_tailModulus
#print axioms ThresholdHC.QuantileOptimality.skipped_packet_le_realizingCore
#print axioms ThresholdHC.QuantileOptimality.tailModulus_finset_sum
#print axioms ThresholdHC.QuantileOptimality.tail_packet_identity
#print axioms ThresholdHC.QuantileOptimality.universalFactor_iff
#print axioms ThresholdHC.QuantileOptimality.upperMass_ge_one
