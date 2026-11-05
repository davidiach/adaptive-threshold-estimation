"""Audit the entropy Lipschitz component of the sharp law reduction."""

import subprocess

from verify_blind_upper_components import LEAN, validate_reports


def audit_input():
    source = """
import ThresholdHC.QuantileSharpLaw.Lipschitz
noncomputable section
set_option linter.unusedVariables false
open Real Filter
open scoped BigOperators Topology
open ThresholdHC.EntropyTailQuantile ThresholdHC.QuantileSharpLaw

example : ∀ {x : ℝ} (hx : 0 ≤ x),
    x+x^2 ≤ exp x-exp (-x) :=
  @ThresholdHC.QuantileSharpLaw.exp_difference_lower

example : ∀ {p : ℝ} (hp : 0 < p) (hp1 : p ≤ 1),
    p*(1-log p)^2 ≤ 1+binEntropy p :=
  @ThresholdHC.QuantileSharpLaw.binary_entropy_slope_bound

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
""".lstrip()
    roots = {
        'ThresholdHC.QuantileSharpLaw.binary_entropy_slope_bound',
        'ThresholdHC.QuantileSharpLaw.binary_homogeneous_identity',
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
        'ThresholdHC.QuantileSharpLaw.exp_difference_lower',
        'ThresholdHC.QuantileSharpLaw.negMulLog_sum_le',
        'ThresholdHC.QuantileSharpLaw.skipped_tail_absorption',
    }
    return source + "".join("#print axioms " + name + "\n" for name in sorted(roots)), roots


def main():
    source, roots = audit_input()
    subprocess.run(["lake", "build", "ThresholdHC.QuantileSharpLaw.Lipschitz"], cwd=LEAN, check=True)
    run = subprocess.run(["lake", "env", "lean", "--stdin"], cwd=LEAN, input=source, text=True,
                         encoding="utf-8", capture_output=True)
    output = run.stdout + run.stderr
    print(output, end="")
    validate_reports(output, run.returncode, roots)
    print(f"Verified {len(roots)} transitive axiom reports")


if __name__ == "__main__":
    main()
