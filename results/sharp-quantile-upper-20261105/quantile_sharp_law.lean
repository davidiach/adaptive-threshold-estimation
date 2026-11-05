import ThresholdHC.QuantileSharpLaw.Full
noncomputable section
set_option linter.unusedVariables false
open MeasureTheory Real Filter Set
open scoped BigOperators Topology ENNReal
open ThresholdHC.Tier6 (Gap)
open ThresholdHC.EntropyTailQuantile ThresholdHC.OptimalQuantile ThresholdHC.QuantileSharpLaw

example : ∀ {x : ℝ} (hx : 0 ≤ x),
    x+x^2 ≤ exp x-exp (-x) :=
  @ThresholdHC.QuantileSharpLaw.exp_difference_lower

example : ∀ {p : ℝ} (hp : 0 < p) (hp1 : p ≤ 1),
    p*(1-log p)^2 ≤ 1+binEntropy p :=
  @ThresholdHC.QuantileSharpLaw.binary_entropy_slope_bound

example : ∀ {N D c : ℝ} (hN : 0 ≤ N) (hD : 0 ≤ D) (hc : 0 ≤ c)
    (hbound : N ≤ D+2*c+max 0 (c-1)*sqrt D),
    1+sqrt N ≤ sqrt 2*(sqrt (1+D)+c) :=
  @ThresholdHC.QuantileSharpLaw.boundary_scalar_price

example : ∀ {A E B H c N : ℝ}
    (hA : 0 ≤ A) (hAE : A ≤ E) (hB : 0 ≤ B) (hBc : B ≤ c)
    (hHc : H ≤ 2*c) (hN : 0 ≤ N)
    (hinteraction : N ≤ E+H+costInteraction A B),
    1+sqrt N ≤ sqrt 2*(sqrt (1+(E+costInteraction A 1))+c) :=
  @ThresholdHC.QuantileSharpLaw.unselected_boundary_price

example : ∀ {ι : Type*} [Fintype ι] (v : ι → ℝ) (hv : ∀ i, 0 ≤ v i),
    negMulLog (costTotal v) ≤ ∑ i, negMulLog (v i) :=
  @ThresholdHC.QuantileSharpLaw.negMulLog_sum_le

example : ∀ {ι : Type*} {a : ℝ} {v : ι → ℝ}
    (ha : 0 ≤ a) (hv : ∀ i, 0 ≤ v i) (y : ℝ) (i : Option ι),
    0 ≤ bumpedCost a v y i :=
  @ThresholdHC.QuantileSharpLaw.bumpedCost_nonneg

example : ∀ {ι : Type*} [Fintype ι] (a : ℝ) (v : ι → ℝ) (y : ℝ),
    costTotal (bumpedCost a v y) = a+y^2+costTotal v :=
  @ThresholdHC.QuantileSharpLaw.bumpedCost_total

example : ∀ {ι : Type*} [Fintype ι] (a : ℝ) (v : ι → ℝ) (y : ℝ),
    costEntropy (bumpedCost a v y) = a+y^2+costTotal v+
      negMulLog (a+y^2)+(∑ i, negMulLog (v i))-negMulLog (a+y^2+costTotal v) :=
  @ThresholdHC.QuantileSharpLaw.bumpedCost_entropy

example : ∀ {q A : ℝ} (hM : 0 < q+A),
    q+A+negMulLog q+negMulLog A-negMulLog (q+A) =
      (q+A)*(1+binEntropy (q/(q+A))) :=
  @ThresholdHC.QuantileSharpLaw.binary_homogeneous_identity

example : ∀ {ι : Type*} [Fintype ι] {a y : ℝ} {v : ι → ℝ}
    (ha : 0 ≤ a) (hv : ∀ i, 0 ≤ v i) (hy : 0 < y),
    (a+y^2+costTotal v)*(1+binEntropy ((a+y^2)/(a+y^2+costTotal v))) ≤
      costEntropy (bumpedCost a v y) :=
  @ThresholdHC.QuantileSharpLaw.bumpedCost_binary_lower

example : ∀ {ι : Type*} [Fintype ι] {x y : ι → ℝ} {s t : ℝ}
    (hx : ∀ i, 0 ≤ x i) (hy : ∀ i, 0 ≤ y i) (hs : 0 ≤ s) (ht : 0 ≤ t) (hst : s+t=1),
    s*sqrt (costEntropy x)+t*sqrt (costEntropy y) ≤
      sqrt (costEntropy (fun i => s*x i+t*y i)) :=
  @ThresholdHC.QuantileSharpLaw.rootEntropy_mix

example : ∀ {ι : Type*} [Fintype ι] (e m w : ι → ℝ)
    (he : ∀ i, 0 ≤ e i),
    ConcaveOn ℝ (Set.Icc (0 : ι → ℝ) w) (corePrice e m w) :=
  @ThresholdHC.QuantileSharpLaw.corePrice_concaveOn

example : ∀ {ι : Type*} (i : Option ι),
    0 ≤ boundaryUnit i :=
  @ThresholdHC.QuantileSharpLaw.boundaryUnit_nonneg

example : ∀ {ι : Type*} [Fintype ι],
    costEntropy (boundaryUnit : Option ι → ℝ) = 1 :=
  @ThresholdHC.QuantileSharpLaw.boundaryUnit_entropy

example : ∀ {ι : Type*} [Fintype ι] {v : Option ι → ℝ}
    (hv : ∀ i, 0 ≤ v i),
    1+costEntropy v ≤ costEntropy (fun i => v i+boundaryUnit i) :=
  @ThresholdHC.QuantileSharpLaw.augmented_entropy_lower

example : ∀ {ι : Type*} [Fintype ι] (a : ℝ) (v : ι → ℝ),
    costEntropy (bumpedCost a v 0) = a+costEntropy v+costInteraction a (costTotal v) :=
  @ThresholdHC.QuantileSharpLaw.costEntropy_option_identity

example : ∀ {ι : Type*} [Fintype ι] {v : Option ι → ℝ} (hv : v none=0),
    costEntropy v = costEntropy (fun i => v (some i)) ∧ costTotal v = costTotal (fun i => v (some i)) :=
  @ThresholdHC.QuantileSharpLaw.zero_boundary_entropy

example : ∀ {ι : Type*} [Fintype ι] {v : Option ι → ℝ}
    (hv : v none=0),
    costEntropy (fun i => v i+boundaryUnit i) =
      1+costEntropy v+costInteraction (costTotal v) 1 :=
  @ThresholdHC.QuantileSharpLaw.augmented_entropy_zero_boundary

example : ∀ {ι : Type*} [Fintype ι] (E : ℝ) {b : Option ι → ℝ}
    (hb : b none=0),
    costEntropy (bumpedCost E (fun i => b (some i)) 0) =
      E+costEntropy b+costInteraction E (costTotal b) :=
  @ThresholdHC.QuantileSharpLaw.compressed_entropy_identity

example : ∀ {n : ℕ} {v b : Option (Fin n) → ℝ}
    (hv : ∀ i, 0 ≤ v i) (hb : ∀ i, 0 ≤ b i) (hb0 : b none=0),
    1+sqrt (costEntropy (fun i => v i+b i)) ≤
      scalarRoot*(sqrt (costEntropy (fun i => v i+boundaryUnit i))+fullCoreCost n b) :=
  @ThresholdHC.QuantileSharpLaw.selected_boundary_price

example : ∀ {n : ℕ} {v b : Option (Fin n) → ℝ}
    (hv : ∀ i, 0 ≤ v i) (hb : ∀ i, 0 ≤ b i) (hv0 : v none=0),
    1+sqrt (costEntropy (fun i => v i+b i)) ≤
      scalarRoot*(sqrt (costEntropy (fun i => v i+boundaryUnit i))+fullCoreCost n b) :=
  @ThresholdHC.QuantileSharpLaw.skipped_boundary_price

example : ∀ {n : ℕ} (v b : Option (Fin n) → ℝ)
    (hv : ∀ i, 0 ≤ v i) (hb : ∀ i, 0 ≤ b i),
    1+sqrt (costEntropy (fun i => v i+b i)) ≤
      scalarRoot*(sqrt (costEntropy (fun i => v i+boundaryUnit i))+fullCoreCost n b) :=
  @ThresholdHC.QuantileSharpLaw.core_vector_bound

example : ∀ {n : ℕ} (i : Option (Fin n)),
    1 ≤ coreWeight i :=
  @ThresholdHC.QuantileSharpLaw.coreWeight_ge_one

example : ∀ (n : ℕ) (b : Option (Fin n) → ℝ),
    fullCoreCost n b = ∑ i, coreWeight i*b i :=
  @ThresholdHC.QuantileSharpLaw.fullCoreCost_eq_sum

example : ∀ {n : ℕ} {b : Option (Fin n) → ℝ} (hb : ∀ i, 0 ≤ b i),
    costTotal b ≤ fullCoreCost n b :=
  @ThresholdHC.QuantileSharpLaw.total_le_fullCoreCost

example : exp (-1)+exponentialTail 2 ≤ 1 :=
  @ThresholdHC.QuantileSharpLaw.core_exponential_mass

example : ∀ (n : ℕ),
    (∑ i : Option (Fin n), exp (1-2*coreWeight i)) ≤ 1 :=
  @ThresholdHC.QuantileSharpLaw.coreWeight_partition_bound

example : ∀ {n : ℕ} {b : Option (Fin n) → ℝ} (hb : ∀ i, 0 ≤ b i),
    costEntropy b ≤ 2*fullCoreCost n b :=
  @ThresholdHC.QuantileSharpLaw.costEntropy_le_twice_coreCost

example : ∀ (Z : Measure Gap) [IsFiniteMeasure Z] {t : ℝ} (ht : 0 < t)
    (n : ℕ) (hthigh : t ≤ bandEdge n) (hZ : ∀ᵐ d : Gap ∂Z, t ≤ (d : ℝ)),
    t*fullCoreCost n (outwardCosts n (bandCost Z)) ≤ ∫ d : Gap, (d : ℝ)⁻¹ ∂Z :=
  @ThresholdHC.QuantileSharpLaw.outward_core_work

example : ∀ {a : ℕ → ℝ} {C : ℝ}
    (ha : ∀ j, 0 ≤ a j) (hC : ∀ n, costEntropy (fun i : Fin n => a i.val) ≤ C),
    Summable a :=
  @ThresholdHC.QuantileSharpLaw.summable_of_prefix_entropy_bound

example : ∀ {a : ℕ → ℝ} {C : ℝ}
    (ha : ∀ j, 0 ≤ a j) (hC : ∀ n, costEntropy (fun i : Fin n => a i.val) ≤ C) (n : ℕ),
    costEntropy (bumpedCost (∑' j : ℕ, a (n+j)) (fun i : Fin n => a i.val) 0) ≤ C :=
  @ThresholdHC.QuantileSharpLaw.merged_tail_entropy_le

example : ∀ {n m : ℕ} (a : Fin (n+m) → ℝ) (ha : ∀ i, 0 ≤ a i),
    costEntropy (bumpedCost (∑ j : Fin m, a (Fin.natAdd n j))
      (fun i : Fin n => a (Fin.castAdd m i)) 0) ≤ costEntropy a :=
  @ThresholdHC.QuantileSharpLaw.costEntropy_merge_tail

example : ∀ {n : ℕ} (a : Fin n → ℝ),
    costEntropy (fun i : Fin n => a i.rev) = costEntropy a :=
  @ThresholdHC.QuantileSharpLaw.costEntropy_reverse

example : ∀ (μ : Measure Gap) [IsProbabilityMeasure μ]
    {ρ B : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hB : 0 < B),
    selectionValue μ ρ B ≤ closedQuantileValue μ ρ B ∧
      closedQuantileValue μ ρ B ≤ ENNReal.ofReal scalarRoot*selectionValue μ ρ B :=
  @ThresholdHC.QuantileSharpLaw.quantile_le_scalarRoot_selection

example : ∀ (μ : Measure Gap) [IsProbabilityMeasure μ]
    {ρ B : ℝ} (hρ : 0 < ρ) (hρ4 : ρ ≤ 1/4) (hB : 0 < B),
    ThresholdHC.EntropyTail.selection μ ρ B ≤ closedQuantileValue μ ρ B ∧
      closedQuantileValue μ ρ B ≤ ENNReal.ofReal scalarRoot*ThresholdHC.EntropyTail.selection μ ρ B :=
  @ThresholdHC.QuantileSharpLaw.locked_sharp_quantile_comparison

example : ∀ {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B),
    0 ≤ costInteraction A B :=
  @ThresholdHC.QuantileSharpLaw.costInteraction_nonneg

example : ∀ (A B : ℝ),
    costInteraction A B=costInteraction B A :=
  @ThresholdHC.QuantileSharpLaw.costInteraction_symm

example : ∀ (A : ℝ),
    Continuous (costInteraction A) :=
  @ThresholdHC.QuantileSharpLaw.costInteraction_continuous

example : ∀ {A x : ℝ} (hA : 0 ≤ A) (hx : 0 < x),
    HasDerivAt (costInteraction A) (log ((A+x)/x)) x :=
  @ThresholdHC.QuantileSharpLaw.costInteraction_hasDerivAt

example : ∀ {A : ℝ} (hA : 0 ≤ A),
    MonotoneOn (costInteraction A) (Set.Ici 0) :=
  @ThresholdHC.QuantileSharpLaw.costInteraction_monotoneOn

example : ∀ {A B C : ℝ} (hA : 0 ≤ A) (hAB : A ≤ B) (hC : 0 ≤ C),
    costInteraction A C ≤ costInteraction B C :=
  @ThresholdHC.QuantileSharpLaw.costInteraction_mono_left

example : ∀ {ι : Type*} [Fintype ι] {v b : ι → ℝ}
    (hv : ∀ i, 0 ≤ v i) (hb : ∀ i, 0 ≤ b i),
    costEntropy (fun i => v i+b i) ≤
      costEntropy v+costEntropy b+costInteraction (costTotal v) (costTotal b) :=
  @ThresholdHC.QuantileSharpLaw.costEntropy_add_interaction

example : ∀ {A : ℝ} (hA : 0 ≤ A),
    log (1+A) ≤ sqrt A :=
  @ThresholdHC.QuantileSharpLaw.log_one_add_le_sqrt

example : ∀ {A x : ℝ} (hA : 0 ≤ A) (hx : 1 ≤ x),
    log ((A+x)/x) ≤ sqrt A :=
  @ThresholdHC.QuantileSharpLaw.costInteraction_derivative_bound

example : ∀ {A B : ℝ} (hA : 0 ≤ A) (hB : 1 ≤ B),
    costInteraction A B ≤ costInteraction A 1+(B-1)*sqrt A :=
  @ThresholdHC.QuantileSharpLaw.costInteraction_increment

example : ∀ {ι : Type*} [Fintype ι] (a : ℝ) (v : ι → ℝ),
    Continuous (fun y : ℝ => sqrt (costEntropy (bumpedCost a v y))) :=
  @ThresholdHC.QuantileSharpLaw.bumpedRoot_continuous

example : ∀ {ι : Type*} [Fintype ι] {a x y : ℝ} {v : ι → ℝ}
    (ha : 0 ≤ a) (hv : ∀ i, 0 ≤ v i) (hx : 0 ≤ x) (hxy : x ≤ y),
    sqrt (costEntropy (bumpedCost a v y))-sqrt (costEntropy (bumpedCost a v x)) ≤ y-x :=
  @ThresholdHC.QuantileSharpLaw.bumpedRoot_increment

example : ∀ {ι : Type*} [Fintype ι] {a : ℝ} {v : ι → ℝ}
    (ha : 0 ≤ a) (hv : ∀ i, 0 ≤ v i),
    MonotoneOn (fun y : ℝ => sqrt (costEntropy (bumpedCost a v y))) (Set.Ici 0) :=
  @ThresholdHC.QuantileSharpLaw.bumpedRoot_monotoneOn

example : ∀ {ι : Type*} [Fintype ι] {a x y : ℝ} {v : ι → ℝ}
    (ha : 0 ≤ a) (hv : ∀ i, 0 ≤ v i) (hx : 0 ≤ x) (hy : 0 ≤ y),
    |sqrt (costEntropy (bumpedCost a v y))-sqrt (costEntropy (bumpedCost a v x))| ≤ |y-x| :=
  @ThresholdHC.QuantileSharpLaw.bumpedRoot_abs_increment

example : ∀ {ι : Type*} [Fintype ι] {a e : ℝ} {v : ι → ℝ}
    (ha : 0 ≤ a) (hv : ∀ i, 0 ≤ v i) (he : 0 ≤ e) (he1 : e ≤ 1),
    sqrt (costEntropy (bumpedCost a v 1)) ≤
      e+sqrt (costEntropy (bumpedCost a v (1-e))) :=
  @ThresholdHC.QuantileSharpLaw.skipped_tail_absorption

example : ∀ {t : ℝ} (ht : 0 < t) (htop : t ≤ 1/2),
    ∃ n : ℕ, bandEdge (n+1) < t ∧ t ≤ bandEdge n :=
  @ThresholdHC.QuantileSharpLaw.exists_boundary_band

example : ∀ (V : Measure Gap) {t : ℝ} (n : ℕ)
    (ht : bandEdge (n+1) < t) (hV : ∀ᵐ d : Gap ∂V, t ≤ (d : ℝ)),
    (measureCostEntropy V).toReal = costEntropy (outwardCosts n (bandCost V)) :=
  @ThresholdHC.QuantileSharpLaw.outward_measure_entropy

example : ∀ (n : ℕ) (a b : ℕ → ℝ),
    outwardCosts n (fun j => a j+b j) = (fun i => outwardCosts n a i+outwardCosts n b i) :=
  @ThresholdHC.QuantileSharpLaw.outwardCosts_add

example : ∀ (L V : Measure Gap) [IsFiniteMeasure L] [IsFiniteMeasure V]
    (hLV : measureCostEntropy (L+V) ≠ ⊤) {t : ℝ} (n : ℕ)
    (htlow : bandEdge (n+1) < t) (hthigh : t ≤ bandEdge n)
    (hL : ∀ᵐ d : Gap ∂L, (d : ℝ) ≤ t) (hV : ∀ᵐ d : Gap ∂V, t ≤ (d : ℝ)),
    costEntropy (fun i => outwardCosts n (bandCost V) i+
      (∑' j, bandCost L j)*boundaryUnit i) ≤ (measureCostEntropy (L+V)).toReal :=
  @ThresholdHC.QuantileSharpLaw.merged_measure_entropy

example : ∀ (L : Measure Gap) {t : ℝ} {n j : ℕ}
    (hL : ∀ᵐ d : Gap ∂L, (d : ℝ) ≤ t) (ht : t ≤ bandEdge n) (hj : j < n),
    bandCost L j=0 :=
  @ThresholdHC.QuantileSharpLaw.tail_bandCost_zero

example : ∀ (L V : Measure Gap) [IsFiniteMeasure L] [IsFiniteMeasure V]
    (hLV : measureCostEntropy (L+V) ≠ ⊤) {t : ℝ} (n : ℕ)
    (htlow : bandEdge (n+1) < t) (hthigh : t ≤ bandEdge n)
    (hL : ∀ᵐ d : Gap ∂L, (d : ℝ) ≤ t) (hV : ∀ᵐ d : Gap ∂V, t ≤ (d : ℝ)),
    costEntropy (bumpedCost (bandCost V n+∑' j, bandCost L j)
      (fun i : Fin n => bandCost V i.rev.val) 0) ≤ (measureCostEntropy (L+V)).toReal :=
  @ThresholdHC.QuantileSharpLaw.selected_measure_merge

example : ∀ (σ : Measure Gap) (hσ : measureCostEntropy σ ≠ ⊤) (n : ℕ),
    costEntropy (fun i : Fin n => bandCost σ i.val) ≤ (measureCostEntropy σ).toReal :=
  @ThresholdHC.QuantileSharpLaw.measure_prefix_entropy_bound

example : ∀ (σ : Measure Gap) (hσ : measureCostEntropy σ ≠ ⊤),
    Summable (bandCost σ) :=
  @ThresholdHC.QuantileSharpLaw.bandCost_summable_of_entropy_finite

example : ∀ (σ : Measure Gap) [IsFiniteMeasure σ],
    (∫⁻ d : Gap, ENNReal.ofReal ((d : ℝ)⁻¹^2) ∂σ) =
      ∑' j : ℕ, ENNReal.ofReal (bandCost σ j) :=
  @ThresholdHC.QuantileSharpLaw.inverseSquare_lintegral_eq_bandCost

example : ∀ (σ : Measure Gap) [IsFiniteMeasure σ]
    (hσ : measureCostEntropy σ ≠ ⊤),
    (∫⁻ d : Gap, ENNReal.ofReal ((d : ℝ)⁻¹^2) ∂σ) = ENNReal.ofReal (∑' j, bandCost σ j) :=
  @ThresholdHC.QuantileSharpLaw.inverseSquare_lintegral_eq_ofReal_tsum

example : ∀ (σ : Measure Gap) [IsFiniteMeasure σ]
    (hσ : measureCostEntropy σ ≠ ⊤) {ρ h : ℝ} (hρ : 0 ≤ ρ) (hh : 0 ≤ h)
    (hmass : σ univ ≤ ENNReal.ofReal ρ),
    tailModulus σ h ≤ h*sqrt (ρ*(∑' j, bandCost σ j)) :=
  @ThresholdHC.QuantileSharpLaw.tailModulus_le_sqrt_bandMoment

example : ∀ {T q E : ℝ} (hT : 0 < T) (hq : 0 ≤ q) (hE : 0 ≤ E),
    T*sqrt ((q/T^2)*E) = sqrt (q*E) :=
  @ThresholdHC.QuantileSharpLaw.scaled_root_identity

example : ∀ {n : ℕ} (s : ℝ) (b : Option (Fin n) → ℝ),
    fullCoreCost n (fun i => s*b i) = s*fullCoreCost n b :=
  @ThresholdHC.QuantileSharpLaw.fullCoreCost_smul

example : ∀ {n : ℕ} {v b : Option (Fin n) → ℝ} {T q a M E c : ℝ}
    (hv : ∀ i, 0 ≤ v i) (hb : ∀ i, 0 ≤ b i) (hT : 0 < T) (hq : 0 ≤ q)
    (ha : 0 ≤ a) (haT : a ≤ T) (hE : 0 ≤ E)
    (hM : (T-a)^2 ≤ q*M)
    (hentropy : costEntropy (fun i => v i+M*boundaryUnit i) ≤ E)
    (hwork : q*fullCoreCost n b ≤ T*c),
    T+sqrt (q*costEntropy (fun i => v i+b i)) ≤ scalarRoot*(sqrt (q*E)+a+c) :=
  @ThresholdHC.QuantileSharpLaw.unnormalized_selection_price

example : ∀ {n : ℕ} (i : Fin n),
    bandEdge n*(2 : ℝ)^i.val = bandEdge i.rev.val/2 :=
  @ThresholdHC.QuantileSharpLaw.outward_band_edge

example : ∀ {n : ℕ} {t : ℝ} (ht : t ≤ bandEdge n)
    (i : Fin n) (d : Gap) (hd : d ∈ band i.rev.val),
    t*(2 : ℝ)^i.val ≤ (d : ℝ) :=
  @ThresholdHC.QuantileSharpLaw.outward_band_lower

example : ∀ (t r : ℝ) (σ : Measure Gap),
    ∀ᵐ d : Gap ∂lowerCut t r σ, (d : ℝ) ≤ t :=
  @ThresholdHC.QuantileSharpLaw.lowerCut_support

example : ∀ (μ : Measure Gap) [IsProbabilityMeasure μ]
    {ρ B : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hB : 0 < B)
    (hht : budgetScale B < quantileThreshold μ ρ) (σ : Measure Gap) (hσ : σ ≤ μ),
    closedQuantileValue μ ρ B ≤ ENNReal.ofReal scalarRoot*selectionCost μ σ ρ (budgetScale B) :=
  @ThresholdHC.QuantileSharpLaw.sharp_comparison_pointwise

example : ∀ (n : ℕ) {a : ℕ → ℝ} (ha : ∀ j, 0 ≤ a j) (i : Option (Fin n)),
    0 ≤ outwardCosts n a i :=
  @ThresholdHC.QuantileSharpLaw.outwardCosts_nonneg

example : ∀ (n : ℕ) (a : ℕ → ℝ) (f : ℝ → ℝ),
    (∑ i, f (outwardCosts n a i)) = ∑ j : Fin (n+1), f (a j.val) :=
  @ThresholdHC.QuantileSharpLaw.outwardCosts_sum

example : ∀ (n : ℕ) (a : ℕ → ℝ),
    costTotal (outwardCosts n a) = costTotal (fun i : Fin (n+1) => a i.val) :=
  @ThresholdHC.QuantileSharpLaw.outwardCosts_total

example : ∀ (n : ℕ) (a : ℕ → ℝ),
    costEntropy (outwardCosts n a) = costEntropy (fun i : Fin (n+1) => a i.val) :=
  @ThresholdHC.QuantileSharpLaw.outwardCosts_entropy

example : ∀ {n : ℕ} (a y : ℝ) (v : Fin n → ℝ),
    costEntropy (bumpedCost a (fun i : Fin n => v i.rev) y) = costEntropy (bumpedCost a v y) :=
  @ThresholdHC.QuantileSharpLaw.bumpedCost_entropy_rev

example : ∀ {ι : Type*} [Fintype ι] {a y : ℝ} {v : ι → ℝ}
    (ha : 0 ≤ a) (hv : ∀ i, 0 ≤ v i) (hy : 0 < y),
    0 < costEntropy (bumpedCost a v y) :=
  @ThresholdHC.QuantileSharpLaw.bumpedCost_positive

example : ∀ {ι : Type*} [Fintype ι] {a y : ℝ} {v : ι → ℝ}
    (ha : 0 ≤ a) (hv : ∀ i, 0 ≤ v i) (hy : 0 < y),
    HasDerivAt (fun z : ℝ => costEntropy (bumpedCost a v z))
      (2*y*(1-log ((a+y^2)/(a+y^2+costTotal v)))) y :=
  @ThresholdHC.QuantileSharpLaw.bumpedCost_hasDerivAt

example : ∀ {ι : Type*} [Fintype ι] {a y : ℝ} {v : ι → ℝ}
    (ha : 0 ≤ a) (hv : ∀ i, 0 ≤ v i) (hy : 0 < y),
    HasDerivAt (fun z : ℝ => sqrt (costEntropy (bumpedCost a v z)))
      (y*(1-log ((a+y^2)/(a+y^2+costTotal v)))/sqrt (costEntropy (bumpedCost a v y))) y :=
  @ThresholdHC.QuantileSharpLaw.bumpedRoot_hasDerivAt

example : ∀ {ι : Type*} [Fintype ι] {a y : ℝ} {v : ι → ℝ}
    (ha : 0 ≤ a) (hv : ∀ i, 0 ≤ v i) (hy : 0 < y),
    y*(1-log ((a+y^2)/(a+y^2+costTotal v)))/sqrt (costEntropy (bumpedCost a v y)) ≤ 1 :=
  @ThresholdHC.QuantileSharpLaw.bumpedRoot_slope_le_one

example : ∀ {l : ℕ → ℝ} (hl : Summable l) (n : ℕ)
    (hz : ∀ j < n, l j=0),
    (∑' j : ℕ, l (n+j)) = ∑' j, l j :=
  @ThresholdHC.QuantileSharpLaw.tail_sum_after_zeros

example : ∀ {a v l : ℕ → ℝ} (hl : Summable l) (n : ℕ)
    (hsum : ∀ j, a j=v j+l j) (hv : ∀ j, n < j → v j=0) (hz : ∀ j < n, l j=0),
    (∑' j : ℕ, a (n+j)) = v n+∑' j, l j :=
  @ThresholdHC.QuantileSharpLaw.tail_sum_split

example : ∀ {a v l : ℕ → ℝ} {C : ℝ} (n : ℕ)
    (hv : ∀ j, 0 ≤ v j) (hl : ∀ j, 0 ≤ l j) (hsum : ∀ j, a j=v j+l j)
    (hV : ∀ j, n < j → v j=0) (hL : ∀ j < n, l j=0)
    (hC : ∀ m, costEntropy (fun i : Fin m => a i.val) ≤ C),
    costEntropy (bumpedCost (v n+∑' j, l j) (fun i : Fin n => v i.rev.val) 0) ≤ C :=
  @ThresholdHC.QuantileSharpLaw.selected_tail_merge

example : ∀ {ι : Type*} [Fintype ι] {v : Option ι → ℝ} {e M R : ℝ}
    (hv : ∀ i, 0 ≤ v i) (he : 0 ≤ e) (he1 : e ≤ 1) (hM : (1-e)^2 ≤ M)
    (hR : sqrt (costEntropy (fun i => v i+M*boundaryUnit i)) ≤ R),
    sqrt (costEntropy (fun i => v i+boundaryUnit i)) ≤ e+R :=
  @ThresholdHC.QuantileSharpLaw.augmented_tail_absorption

example : ∀ {n : ℕ} {v b : Option (Fin n) → ℝ} {e M R c : ℝ}
    (hv : ∀ i, 0 ≤ v i) (hb : ∀ i, 0 ≤ b i) (he : 0 ≤ e) (he1 : e ≤ 1)
    (hM : (1-e)^2 ≤ M) (hR : sqrt (costEntropy (fun i => v i+M*boundaryUnit i)) ≤ R)
    (hc : fullCoreCost n b ≤ c),
    1+sqrt (costEntropy (fun i => v i+b i)) ≤ scalarRoot*(R+e+c) :=
  @ThresholdHC.QuantileSharpLaw.normalized_selection_price

example : ∀ {ι : Type*} [Fintype ι] (e m w v : ι → ℝ)
    (he : ∀ i, 0 ≤ e i) (hv : v ∈ Set.Icc (0 : ι → ℝ) w),
    ∃ z ∈ Set.Icc (0 : ι → ℝ) w, (∀ i, z i=0 ∨ z i=w i) ∧ corePrice e m w z ≤ corePrice e m w v :=
  @ThresholdHC.QuantileSharpLaw.exists_corePrice_vertex

example : ∀ {ι : Type*} [Fintype ι] (e m v b : ι → ℝ)
    (he : ∀ i, 0 ≤ e i) (hv : ∀ i, 0 ≤ v i) (hb : ∀ i, 0 ≤ b i),
    ∃ z d : ι → ℝ, (∀ i, 0 ≤ z i) ∧ (∀ i, 0 ≤ d i) ∧
      (∀ i, z i+d i=v i+b i) ∧ (∀ i, z i=0 ∨ d i=0) ∧
      sqrt (costEntropy (fun i => z i+e i))+(∑ i, m i*d i) ≤
        sqrt (costEntropy (fun i => v i+e i))+(∑ i, m i*b i) :=
  @ThresholdHC.QuantileSharpLaw.exists_disjoint_core_split
#print axioms ThresholdHC.QuantileSharpLaw.augmented_entropy_lower
#print axioms ThresholdHC.QuantileSharpLaw.augmented_entropy_zero_boundary
#print axioms ThresholdHC.QuantileSharpLaw.augmented_tail_absorption
#print axioms ThresholdHC.QuantileSharpLaw.bandCost_summable_of_entropy_finite
#print axioms ThresholdHC.QuantileSharpLaw.binary_entropy_slope_bound
#print axioms ThresholdHC.QuantileSharpLaw.binary_homogeneous_identity
#print axioms ThresholdHC.QuantileSharpLaw.boundaryUnit_entropy
#print axioms ThresholdHC.QuantileSharpLaw.boundaryUnit_nonneg
#print axioms ThresholdHC.QuantileSharpLaw.boundary_scalar_price
#print axioms ThresholdHC.QuantileSharpLaw.bumpedCost_binary_lower
#print axioms ThresholdHC.QuantileSharpLaw.bumpedCost_entropy
#print axioms ThresholdHC.QuantileSharpLaw.bumpedCost_entropy_rev
#print axioms ThresholdHC.QuantileSharpLaw.bumpedCost_hasDerivAt
#print axioms ThresholdHC.QuantileSharpLaw.bumpedCost_nonneg
#print axioms ThresholdHC.QuantileSharpLaw.bumpedCost_positive
#print axioms ThresholdHC.QuantileSharpLaw.bumpedCost_total
#print axioms ThresholdHC.QuantileSharpLaw.bumpedRoot_abs_increment
#print axioms ThresholdHC.QuantileSharpLaw.bumpedRoot_continuous
#print axioms ThresholdHC.QuantileSharpLaw.bumpedRoot_hasDerivAt
#print axioms ThresholdHC.QuantileSharpLaw.bumpedRoot_increment
#print axioms ThresholdHC.QuantileSharpLaw.bumpedRoot_monotoneOn
#print axioms ThresholdHC.QuantileSharpLaw.bumpedRoot_slope_le_one
#print axioms ThresholdHC.QuantileSharpLaw.compressed_entropy_identity
#print axioms ThresholdHC.QuantileSharpLaw.corePrice_concaveOn
#print axioms ThresholdHC.QuantileSharpLaw.coreWeight_ge_one
#print axioms ThresholdHC.QuantileSharpLaw.coreWeight_partition_bound
#print axioms ThresholdHC.QuantileSharpLaw.core_exponential_mass
#print axioms ThresholdHC.QuantileSharpLaw.core_vector_bound
#print axioms ThresholdHC.QuantileSharpLaw.costEntropy_add_interaction
#print axioms ThresholdHC.QuantileSharpLaw.costEntropy_le_twice_coreCost
#print axioms ThresholdHC.QuantileSharpLaw.costEntropy_merge_tail
#print axioms ThresholdHC.QuantileSharpLaw.costEntropy_option_identity
#print axioms ThresholdHC.QuantileSharpLaw.costEntropy_reverse
#print axioms ThresholdHC.QuantileSharpLaw.costInteraction_continuous
#print axioms ThresholdHC.QuantileSharpLaw.costInteraction_derivative_bound
#print axioms ThresholdHC.QuantileSharpLaw.costInteraction_hasDerivAt
#print axioms ThresholdHC.QuantileSharpLaw.costInteraction_increment
#print axioms ThresholdHC.QuantileSharpLaw.costInteraction_mono_left
#print axioms ThresholdHC.QuantileSharpLaw.costInteraction_monotoneOn
#print axioms ThresholdHC.QuantileSharpLaw.costInteraction_nonneg
#print axioms ThresholdHC.QuantileSharpLaw.costInteraction_symm
#print axioms ThresholdHC.QuantileSharpLaw.exists_boundary_band
#print axioms ThresholdHC.QuantileSharpLaw.exists_corePrice_vertex
#print axioms ThresholdHC.QuantileSharpLaw.exists_disjoint_core_split
#print axioms ThresholdHC.QuantileSharpLaw.exp_difference_lower
#print axioms ThresholdHC.QuantileSharpLaw.fullCoreCost_eq_sum
#print axioms ThresholdHC.QuantileSharpLaw.fullCoreCost_smul
#print axioms ThresholdHC.QuantileSharpLaw.inverseSquare_lintegral_eq_bandCost
#print axioms ThresholdHC.QuantileSharpLaw.inverseSquare_lintegral_eq_ofReal_tsum
#print axioms ThresholdHC.QuantileSharpLaw.locked_sharp_quantile_comparison
#print axioms ThresholdHC.QuantileSharpLaw.log_one_add_le_sqrt
#print axioms ThresholdHC.QuantileSharpLaw.lowerCut_support
#print axioms ThresholdHC.QuantileSharpLaw.measure_prefix_entropy_bound
#print axioms ThresholdHC.QuantileSharpLaw.merged_measure_entropy
#print axioms ThresholdHC.QuantileSharpLaw.merged_tail_entropy_le
#print axioms ThresholdHC.QuantileSharpLaw.negMulLog_sum_le
#print axioms ThresholdHC.QuantileSharpLaw.normalized_selection_price
#print axioms ThresholdHC.QuantileSharpLaw.outwardCosts_add
#print axioms ThresholdHC.QuantileSharpLaw.outwardCosts_entropy
#print axioms ThresholdHC.QuantileSharpLaw.outwardCosts_nonneg
#print axioms ThresholdHC.QuantileSharpLaw.outwardCosts_sum
#print axioms ThresholdHC.QuantileSharpLaw.outwardCosts_total
#print axioms ThresholdHC.QuantileSharpLaw.outward_band_edge
#print axioms ThresholdHC.QuantileSharpLaw.outward_band_lower
#print axioms ThresholdHC.QuantileSharpLaw.outward_core_work
#print axioms ThresholdHC.QuantileSharpLaw.outward_measure_entropy
#print axioms ThresholdHC.QuantileSharpLaw.quantile_le_scalarRoot_selection
#print axioms ThresholdHC.QuantileSharpLaw.rootEntropy_mix
#print axioms ThresholdHC.QuantileSharpLaw.scaled_root_identity
#print axioms ThresholdHC.QuantileSharpLaw.selected_boundary_price
#print axioms ThresholdHC.QuantileSharpLaw.selected_measure_merge
#print axioms ThresholdHC.QuantileSharpLaw.selected_tail_merge
#print axioms ThresholdHC.QuantileSharpLaw.sharp_comparison_pointwise
#print axioms ThresholdHC.QuantileSharpLaw.skipped_boundary_price
#print axioms ThresholdHC.QuantileSharpLaw.skipped_tail_absorption
#print axioms ThresholdHC.QuantileSharpLaw.summable_of_prefix_entropy_bound
#print axioms ThresholdHC.QuantileSharpLaw.tailModulus_le_sqrt_bandMoment
#print axioms ThresholdHC.QuantileSharpLaw.tail_bandCost_zero
#print axioms ThresholdHC.QuantileSharpLaw.tail_sum_after_zeros
#print axioms ThresholdHC.QuantileSharpLaw.tail_sum_split
#print axioms ThresholdHC.QuantileSharpLaw.total_le_fullCoreCost
#print axioms ThresholdHC.QuantileSharpLaw.unnormalized_selection_price
#print axioms ThresholdHC.QuantileSharpLaw.unselected_boundary_price
#print axioms ThresholdHC.QuantileSharpLaw.zero_boundary_entropy
