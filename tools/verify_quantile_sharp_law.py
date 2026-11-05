"""Audit entropy Lipschitz bounds and the sharp finite core reduction."""

import subprocess

from verify_blind_upper_components import LEAN, validate_reports


def audit_input():
    source = """
import ThresholdHC.QuantileSharpLaw.CoreReduction
noncomputable section
set_option linter.unusedVariables false
open Real Filter
open scoped BigOperators Topology
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
""".lstrip()
    roots = {
        'ThresholdHC.QuantileSharpLaw.augmented_entropy_lower',
        'ThresholdHC.QuantileSharpLaw.augmented_entropy_zero_boundary',
        'ThresholdHC.QuantileSharpLaw.binary_entropy_slope_bound',
        'ThresholdHC.QuantileSharpLaw.binary_homogeneous_identity',
        'ThresholdHC.QuantileSharpLaw.boundaryUnit_entropy',
        'ThresholdHC.QuantileSharpLaw.boundaryUnit_nonneg',
        'ThresholdHC.QuantileSharpLaw.boundary_scalar_price',
        'ThresholdHC.QuantileSharpLaw.bumpedCost_binary_lower',
        'ThresholdHC.QuantileSharpLaw.bumpedCost_entropy',
        'ThresholdHC.QuantileSharpLaw.bumpedCost_hasDerivAt',
        'ThresholdHC.QuantileSharpLaw.bumpedCost_nonneg',
        'ThresholdHC.QuantileSharpLaw.bumpedCost_positive',
        'ThresholdHC.QuantileSharpLaw.bumpedCost_total',
        'ThresholdHC.QuantileSharpLaw.bumpedRoot_abs_increment',
        'ThresholdHC.QuantileSharpLaw.bumpedRoot_continuous',
        'ThresholdHC.QuantileSharpLaw.bumpedRoot_hasDerivAt',
        'ThresholdHC.QuantileSharpLaw.bumpedRoot_increment',
        'ThresholdHC.QuantileSharpLaw.bumpedRoot_monotoneOn',
        'ThresholdHC.QuantileSharpLaw.bumpedRoot_slope_le_one',
        'ThresholdHC.QuantileSharpLaw.compressed_entropy_identity',
        'ThresholdHC.QuantileSharpLaw.corePrice_concaveOn',
        'ThresholdHC.QuantileSharpLaw.coreWeight_ge_one',
        'ThresholdHC.QuantileSharpLaw.coreWeight_partition_bound',
        'ThresholdHC.QuantileSharpLaw.core_exponential_mass',
        'ThresholdHC.QuantileSharpLaw.core_vector_bound',
        'ThresholdHC.QuantileSharpLaw.costEntropy_add_interaction',
        'ThresholdHC.QuantileSharpLaw.costEntropy_le_twice_coreCost',
        'ThresholdHC.QuantileSharpLaw.costEntropy_option_identity',
        'ThresholdHC.QuantileSharpLaw.costInteraction_continuous',
        'ThresholdHC.QuantileSharpLaw.costInteraction_derivative_bound',
        'ThresholdHC.QuantileSharpLaw.costInteraction_hasDerivAt',
        'ThresholdHC.QuantileSharpLaw.costInteraction_increment',
        'ThresholdHC.QuantileSharpLaw.costInteraction_mono_left',
        'ThresholdHC.QuantileSharpLaw.costInteraction_monotoneOn',
        'ThresholdHC.QuantileSharpLaw.costInteraction_nonneg',
        'ThresholdHC.QuantileSharpLaw.costInteraction_symm',
        'ThresholdHC.QuantileSharpLaw.exists_corePrice_vertex',
        'ThresholdHC.QuantileSharpLaw.exists_disjoint_core_split',
        'ThresholdHC.QuantileSharpLaw.exp_difference_lower',
        'ThresholdHC.QuantileSharpLaw.fullCoreCost_eq_sum',
        'ThresholdHC.QuantileSharpLaw.log_one_add_le_sqrt',
        'ThresholdHC.QuantileSharpLaw.negMulLog_sum_le',
        'ThresholdHC.QuantileSharpLaw.rootEntropy_mix',
        'ThresholdHC.QuantileSharpLaw.selected_boundary_price',
        'ThresholdHC.QuantileSharpLaw.skipped_boundary_price',
        'ThresholdHC.QuantileSharpLaw.skipped_tail_absorption',
        'ThresholdHC.QuantileSharpLaw.total_le_fullCoreCost',
        'ThresholdHC.QuantileSharpLaw.unselected_boundary_price',
        'ThresholdHC.QuantileSharpLaw.zero_boundary_entropy',
    }
    return source + "".join("#print axioms " + name + "\n" for name in sorted(roots)), roots


def main():
    source, roots = audit_input()
    subprocess.run(["lake", "build", "ThresholdHC.QuantileSharpLaw.CoreReduction"], cwd=LEAN, check=True)
    run = subprocess.run(["lake", "env", "lean", "--stdin"], cwd=LEAN, input=source, text=True,
                         encoding="utf-8", capture_output=True)
    output = run.stdout + run.stderr
    print(output, end="")
    validate_reports(output, run.returncode, roots)
    print(f"Verified {len(roots)} transitive axiom reports")


if __name__ == "__main__":
    main()
