import ThresholdHC.OptimalQuantile.FiniteSharp
noncomputable section
set_option linter.unusedVariables false
open Real Filter
open scoped BigOperators Topology
open ThresholdHC.EntropyTailQuantile ThresholdHC.OptimalQuantile

example : ContinuousOn (fun z : ℝ × ℝ => dualPrice z.1 z.2) scalarDomain :=
  @ThresholdHC.OptimalQuantile.dualPrice_continuousOn

example : ContinuousOn (fun z : ℝ × ℝ => partitionSeries z.1 z.2) scalarDomain :=
  @ThresholdHC.OptimalQuantile.partitionSeries_continuousOn

example : ∀ {k : ℝ} (hk : sqrt 2 ≤ k),
    ContinuousOn (partitionSeries k) (Set.Ici 1) :=
  @ThresholdHC.OptimalQuantile.partitionSeries_continuousOn_tangent

example : exp (3 : ℝ) < 25 :=
  @ThresholdHC.OptimalQuantile.exp_three_lt_twentyfive

example : exp (7/5 : ℝ) < 5 :=
  @ThresholdHC.OptimalQuantile.exp_seven_fifths_lt_five

example : 1 < scalarPeak (sqrt 2) :=
  @ThresholdHC.OptimalQuantile.scalarPeak_lower_endpoint

example : ∀ {price : ℝ} (hp : 3 ≤ price),
    exponentialTail price ≤ exp (-2)/(1-exp (-3)) :=
  @ThresholdHC.OptimalQuantile.exponentialTail_bound_three

example : (5 : ℝ) < exp 2 :=
  @ThresholdHC.OptimalQuantile.exp_two_gt_five

example : scalarPeak (31/20) < 1 :=
  @ThresholdHC.OptimalQuantile.scalarPeak_upper_endpoint

example : ∀ (n : ℕ) {k : ℝ} (hk : 1 ≤ k),
    finiteVectorBound n k ↔ ∀ u : ℝ, 1 ≤ u → finitePartition n k u ≤ 1 :=
  @ThresholdHC.OptimalQuantile.finiteVectorBound_iff_partition

example : ∀ {n : ℕ} {u : ℝ} (hu : 0 < u) (i : Option (Fin n)),
    0 < tangentWeight u i :=
  @ThresholdHC.OptimalQuantile.tangentWeight_pos

example : ∀ {k u : ℝ} (hk : 1 ≤ k) (hu : 1 ≤ u),
    0 ≤ tangentOffset k u :=
  @ThresholdHC.OptimalQuantile.tangentOffset_nonneg

example : ∀ (n : ℕ) (k u : ℝ) (x : Option (Fin n) → ℝ),
    k*((u+(1+x none)/u)/2+dyadicCost n x) =
      1+tangentOffset k u+k*(∑ i, tangentWeight u i*x i) :=
  @ThresholdHC.OptimalQuantile.tangent_price_identity

example : ∀ (n : ℕ) (k u : ℝ),
    finitePartition n k u = ∑ i : Option (Fin n), exp (1-(4*k*tangentOffset k u)*tangentWeight u i) :=
  @ThresholdHC.OptimalQuantile.finitePartition_eq_sum

example : ∀ {k : ℝ} (hk : finiteVectorBound 0 k),
    sqrt 2 ≤ k :=
  @ThresholdHC.OptimalQuantile.finiteVectorBound_zero_requires_sqrt_two

example : ∀ (k : ℝ),
    (∀ n : ℕ, finiteVectorBound n k) ↔ scalarRoot ≤ k :=
  @ThresholdHC.OptimalQuantile.all_finite_bounds_iff_root_unrestricted

example : ∀ {k : ℝ} (hk : k < scalarRoot),
    ∃ n : ℕ, ∃ x : Option (Fin n) → ℝ, (∀ i, 0 ≤ x i) ∧
      k*(sqrt (1+x none)+dyadicCost n x) < 1+sqrt (costEntropy x) :=
  @ThresholdHC.OptimalQuantile.finite_vector_witness_below_root

example : ∀ {I : Type} [Fintype I] (w : I → ℝ) (price : ℝ),
    costEntropy (fun i => exp (1-price*w i)) =
      price*(∑ i, w i*exp (1-price*w i))+
        costTotal (fun i => exp (1-price*w i))*log (costTotal (fun i => exp (1-price*w i))) :=
  @ThresholdHC.OptimalQuantile.exponential_entropy

example : ∀ {I : Type} [Fintype I] (w : I → ℝ) (price : ℝ),
    (∀ x : I → ℝ, (∀ i, 0 ≤ x i) → costEntropy x ≤ price*(∑ i, w i*x i)) ↔
      (∑ i, exp (1-price*w i)) ≤ 1 :=
  @ThresholdHC.OptimalQuantile.weighted_entropy_iff_partition

example : ∀ (n : ℕ) (k u : ℝ),
    finitePartition n k u = exp (1-dualPrice k u/(2*u))+
      ∑ j ∈ Finset.range n, exp (1-dualPrice k u*(2 : ℝ)^j) :=
  @ThresholdHC.OptimalQuantile.finitePartition_eq_range

example : ∀ {k u : ℝ} (hk : sqrt 2 ≤ k) (hu : 1 ≤ u),
    Tendsto (fun n : ℕ => finitePartition n k u) atTop (𝓝 (partitionSeries k u)) :=
  @ThresholdHC.OptimalQuantile.finitePartition_tendsto

example : ∀ {k u : ℝ} (hk : sqrt 2 ≤ k) (hu : 1 ≤ u) (n : ℕ),
    finitePartition n k u ≤ partitionSeries k u :=
  @ThresholdHC.OptimalQuantile.finitePartition_le_series

example : ∀ {k u : ℝ} (hk : sqrt 2 ≤ k) (hu : 1 ≤ u),
    partitionSeries k u ≤ 1 ↔ ∀ n : ℕ, finitePartition n k u ≤ 1 :=
  @ThresholdHC.OptimalQuantile.partitionSeries_le_one_iff

example : ∀ {k : ℝ} (hk : sqrt 2 ≤ k),
    (∀ n : ℕ, finiteVectorBound n k) ↔ ∀ u : ℝ, 1 ≤ u → partitionSeries k u ≤ 1 :=
  @ThresholdHC.OptimalQuantile.all_finite_bounds_iff_series

example : Continuous (fun z : ℝ × ℝ => partitionSeries (max (sqrt 2) z.1) (max 1 z.2)) :=
  @ThresholdHC.OptimalQuantile.partitionSeries_clamped_continuous

example : ContinuousOn scalarPeak (Set.Ici (sqrt 2)) :=
  @ThresholdHC.OptimalQuantile.scalarPeak_continuousOn

example : ∀ {k : ℝ} (hk : sqrt 2 ≤ k),
    ∃ u ∈ Set.Icc (1 : ℝ) (31/20), scalarPeak k = partitionSeries k u ∧
      ∀ v ∈ Set.Icc (1 : ℝ) (31/20), partitionSeries k v ≤ partitionSeries k u :=
  @ThresholdHC.OptimalQuantile.scalarPeak_attained

example : ∀ {k u : ℝ} (hk : sqrt 2 ≤ k)
    (hu : u ∈ Set.Icc (1 : ℝ) (31/20)),
    partitionSeries k u ≤ scalarPeak k :=
  @ThresholdHC.OptimalQuantile.partitionSeries_le_peak

example : StrictAntiOn scalarPeak (Set.Ici (sqrt 2)) :=
  @ThresholdHC.OptimalQuantile.scalarPeak_strictAntiOn

example : ∀ {k : ℝ} (hk : sqrt 2 ≤ k) (hkcap : k ≤ 31/20),
    (∀ u : ℝ, 1 ≤ u → partitionSeries k u ≤ 1) ↔ scalarPeak k ≤ 1 :=
  @ThresholdHC.OptimalQuantile.all_tangents_iff_peak

example : ∀ {k : ℝ} (hk : sqrt 2 ≤ k) (hkcap : k ≤ 31/20),
    (∀ n : ℕ, finiteVectorBound n k) ↔ scalarPeak k ≤ 1 :=
  @ThresholdHC.OptimalQuantile.all_finite_bounds_iff_peak

example : ∀ {k l u : ℝ}
    (hk : sqrt 2 ≤ k) (hkl : k < l) (hu : 1 ≤ u),
    dualPrice k u < dualPrice l u :=
  @ThresholdHC.OptimalQuantile.dualPrice_strict_in_factor

example : ∀ {p q : ℝ} (hp : 2 ≤ p) (hpq : p ≤ q),
    exponentialTail q ≤ exponentialTail p :=
  @ThresholdHC.OptimalQuantile.exponentialTail_antitone

example : ∀ {k l u : ℝ}
    (hk : sqrt 2 ≤ k) (hkl : k < l) (hu : 1 ≤ u),
    partitionSeries l u < partitionSeries k u :=
  @ThresholdHC.OptimalQuantile.partitionSeries_strict_in_factor

example : ∀ {u v : ℝ} (hu : 1 ≤ u) (huv : u ≤ v),
    u+1/u ≤ v+1/v :=
  @ThresholdHC.OptimalQuantile.tangent_sum_mono

example : ∀ (k : ℝ) {u v : ℝ} (hu : 1 ≤ u) (huv : u ≤ v),
    dualPrice k u ≤ dualPrice k v :=
  @ThresholdHC.OptimalQuantile.dualPrice_mono_in_tangent

example : ∀ {k u v : ℝ}
    (hk : sqrt 2 ≤ k) (hku : k ≤ u) (huv : u ≤ v),
    partitionSeries k v ≤ partitionSeries k u :=
  @ThresholdHC.OptimalQuantile.partitionSeries_mono_above_factor

example : ∀ {k u : ℝ} (hk : sqrt 2 ≤ k) (hu : 1 ≤ u),
    2 ≤ dualPrice k u :=
  @ThresholdHC.OptimalQuantile.dualPrice_ge_two

example : ∀ (k : ℝ) {u : ℝ} (hu : u ≠ 0),
    1-dualPrice k u/(2*u) = 2-k^2-(k/u-1)^2 :=
  @ThresholdHC.OptimalQuantile.first_exponent_identity

example : ∀ {g a d : ℝ} (hg : 0 ≤ g) (ha : 0 < a) (hd : 0 ≤ d),
    (∀ t : ℝ, 0 ≤ t → sqrt (t*g) ≤ d+a*t) ↔ g ≤ 4*a*d :=
  @ThresholdHC.OptimalQuantile.scaled_root_bound_iff

example : ∃! k : ℝ, k ∈ Set.Icc (sqrt 2) (31/20) ∧ scalarPeak k = 1 :=
  @ThresholdHC.OptimalQuantile.exists_unique_scalarRoot

example : scalarRoot ∈ Set.Icc (sqrt 2) (31/20) ∧ scalarPeak scalarRoot = 1 :=
  @ThresholdHC.OptimalQuantile.scalarRoot_spec

example : sqrt 2 < scalarRoot ∧ scalarRoot < 31/20 :=
  @ThresholdHC.OptimalQuantile.scalarRoot_interior

example : ∀ {k : ℝ} (hk : sqrt 2 ≤ k),
    scalarPeak k ≤ 1 ↔ scalarRoot ≤ k :=
  @ThresholdHC.OptimalQuantile.scalarPeak_le_one_iff

example : ∀ (n : ℕ),
    finiteVectorBound n scalarRoot :=
  @ThresholdHC.OptimalQuantile.scalarRoot_bounds_all_finite

example : ∀ {k : ℝ} (hk : sqrt 2 ≤ k),
    (∀ n : ℕ, finiteVectorBound n k) ↔ scalarRoot ≤ k :=
  @ThresholdHC.OptimalQuantile.all_finite_bounds_iff_root

example : ∀ (n : ℕ),
    (n : ℝ)+1 ≤ (2 : ℝ)^n :=
  @ThresholdHC.OptimalQuantile.power_two_lower

example : ∀ {price : ℝ} (hp : 2 ≤ price) (n : ℕ),
    exp (1-price*(2 : ℝ)^n) ≤ exp (-1)*(exp (-2))^n :=
  @ThresholdHC.OptimalQuantile.exponential_term_bound

example : ∀ {price : ℝ} (hp : 2 ≤ price),
    Summable (fun n : ℕ => exp (1-price*(2 : ℝ)^n)) :=
  @ThresholdHC.OptimalQuantile.exponentialTail_summable

example : ∀ {a u : ℝ} (ha : 0 ≤ a) (hu : 0 < u),
    sqrt (1+a) ≤ (u+(1+a)/u)/2 :=
  @ThresholdHC.OptimalQuantile.sqrt_tangent

example : ∀ {a : ℝ} (ha : 0 ≤ a),
    ∃ u : ℝ, 1 ≤ u ∧ sqrt (1+a) = (u+(1+a)/u)/2 :=
  @ThresholdHC.OptimalQuantile.sqrt_tangent_attained

example : ∀ {a c g k : ℝ} (ha : 0 ≤ a) (hk : 0 ≤ k),
    (1+sqrt g ≤ k*(sqrt (1+a)+c)) ↔
      ∀ u : ℝ, 1 ≤ u → 1+sqrt g ≤ k*((u+(1+a)/u)/2+c) :=
  @ThresholdHC.OptimalQuantile.price_iff_all_tangents

example : ∀ {I : Type} [Fintype I] (w : I → ℝ)
    (hw : ∀ i, 0 < w i) {k d : ℝ} (hk : 0 < k) (hd : 0 ≤ d),
    (∀ x : I → ℝ, (∀ i, 0 ≤ x i) → sqrt (costEntropy x) ≤ d+k*(∑ i, w i*x i)) ↔
      (∀ x : I → ℝ, (∀ i, 0 ≤ x i) → costEntropy x ≤ (4*k*d)*(∑ i, w i*x i)) :=
  @ThresholdHC.OptimalQuantile.root_price_iff_entropy

example : ∀ {I : Type} [Fintype I] (w : I → ℝ)
    (hw : ∀ i, 0 < w i) {k d : ℝ} (hk : 0 < k) (hd : 0 ≤ d),
    (∀ x : I → ℝ, (∀ i, 0 ≤ x i) → sqrt (costEntropy x) ≤ d+k*(∑ i, w i*x i)) ↔
      (∑ i, exp (1-(4*k*d)*w i)) ≤ 1 :=
  @ThresholdHC.OptimalQuantile.root_price_iff_partition
#print axioms ThresholdHC.OptimalQuantile.all_finite_bounds_iff_peak
#print axioms ThresholdHC.OptimalQuantile.all_finite_bounds_iff_root
#print axioms ThresholdHC.OptimalQuantile.all_finite_bounds_iff_root_unrestricted
#print axioms ThresholdHC.OptimalQuantile.all_finite_bounds_iff_series
#print axioms ThresholdHC.OptimalQuantile.all_tangents_iff_peak
#print axioms ThresholdHC.OptimalQuantile.dualPrice_continuousOn
#print axioms ThresholdHC.OptimalQuantile.dualPrice_ge_two
#print axioms ThresholdHC.OptimalQuantile.dualPrice_mono_in_tangent
#print axioms ThresholdHC.OptimalQuantile.dualPrice_strict_in_factor
#print axioms ThresholdHC.OptimalQuantile.exists_unique_scalarRoot
#print axioms ThresholdHC.OptimalQuantile.exp_seven_fifths_lt_five
#print axioms ThresholdHC.OptimalQuantile.exp_three_lt_twentyfive
#print axioms ThresholdHC.OptimalQuantile.exp_two_gt_five
#print axioms ThresholdHC.OptimalQuantile.exponentialTail_antitone
#print axioms ThresholdHC.OptimalQuantile.exponentialTail_bound_three
#print axioms ThresholdHC.OptimalQuantile.exponentialTail_summable
#print axioms ThresholdHC.OptimalQuantile.exponential_entropy
#print axioms ThresholdHC.OptimalQuantile.exponential_term_bound
#print axioms ThresholdHC.OptimalQuantile.finitePartition_eq_range
#print axioms ThresholdHC.OptimalQuantile.finitePartition_eq_sum
#print axioms ThresholdHC.OptimalQuantile.finitePartition_le_series
#print axioms ThresholdHC.OptimalQuantile.finitePartition_tendsto
#print axioms ThresholdHC.OptimalQuantile.finiteVectorBound_iff_partition
#print axioms ThresholdHC.OptimalQuantile.finiteVectorBound_zero_requires_sqrt_two
#print axioms ThresholdHC.OptimalQuantile.finite_vector_witness_below_root
#print axioms ThresholdHC.OptimalQuantile.first_exponent_identity
#print axioms ThresholdHC.OptimalQuantile.partitionSeries_clamped_continuous
#print axioms ThresholdHC.OptimalQuantile.partitionSeries_continuousOn
#print axioms ThresholdHC.OptimalQuantile.partitionSeries_continuousOn_tangent
#print axioms ThresholdHC.OptimalQuantile.partitionSeries_le_one_iff
#print axioms ThresholdHC.OptimalQuantile.partitionSeries_le_peak
#print axioms ThresholdHC.OptimalQuantile.partitionSeries_mono_above_factor
#print axioms ThresholdHC.OptimalQuantile.partitionSeries_strict_in_factor
#print axioms ThresholdHC.OptimalQuantile.power_two_lower
#print axioms ThresholdHC.OptimalQuantile.price_iff_all_tangents
#print axioms ThresholdHC.OptimalQuantile.root_price_iff_entropy
#print axioms ThresholdHC.OptimalQuantile.root_price_iff_partition
#print axioms ThresholdHC.OptimalQuantile.scalarPeak_attained
#print axioms ThresholdHC.OptimalQuantile.scalarPeak_continuousOn
#print axioms ThresholdHC.OptimalQuantile.scalarPeak_le_one_iff
#print axioms ThresholdHC.OptimalQuantile.scalarPeak_lower_endpoint
#print axioms ThresholdHC.OptimalQuantile.scalarPeak_strictAntiOn
#print axioms ThresholdHC.OptimalQuantile.scalarPeak_upper_endpoint
#print axioms ThresholdHC.OptimalQuantile.scalarRoot_bounds_all_finite
#print axioms ThresholdHC.OptimalQuantile.scalarRoot_interior
#print axioms ThresholdHC.OptimalQuantile.scalarRoot_spec
#print axioms ThresholdHC.OptimalQuantile.scaled_root_bound_iff
#print axioms ThresholdHC.OptimalQuantile.sqrt_tangent
#print axioms ThresholdHC.OptimalQuantile.sqrt_tangent_attained
#print axioms ThresholdHC.OptimalQuantile.tangentOffset_nonneg
#print axioms ThresholdHC.OptimalQuantile.tangentWeight_pos
#print axioms ThresholdHC.OptimalQuantile.tangent_price_identity
#print axioms ThresholdHC.OptimalQuantile.tangent_sum_mono
#print axioms ThresholdHC.OptimalQuantile.weighted_entropy_iff_partition
