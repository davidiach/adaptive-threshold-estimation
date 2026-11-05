"""Audit the finite-vector scalar characterization for the quantile factor."""

import subprocess

from verify_blind_upper_components import LEAN, validate_reports


def audit_input():
    source = """
import ThresholdHC.OptimalQuantile.Finite
noncomputable section
set_option linter.unusedVariables false
open Real
open scoped BigOperators
open ThresholdHC.EntropyTailQuantile ThresholdHC.OptimalQuantile

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

example : ∀ {I : Type} [Fintype I] (w : I → ℝ) (price : ℝ),
    costEntropy (fun i => exp (1-price*w i)) =
      price*(∑ i, w i*exp (1-price*w i))+
        costTotal (fun i => exp (1-price*w i))*log (costTotal (fun i => exp (1-price*w i))) :=
  @ThresholdHC.OptimalQuantile.exponential_entropy

example : ∀ {I : Type} [Fintype I] (w : I → ℝ) (price : ℝ),
    (∀ x : I → ℝ, (∀ i, 0 ≤ x i) → costEntropy x ≤ price*(∑ i, w i*x i)) ↔
      (∑ i, exp (1-price*w i)) ≤ 1 :=
  @ThresholdHC.OptimalQuantile.weighted_entropy_iff_partition

example : ∀ {g a d : ℝ} (hg : 0 ≤ g) (ha : 0 < a) (hd : 0 ≤ d),
    (∀ t : ℝ, 0 ≤ t → sqrt (t*g) ≤ d+a*t) ↔ g ≤ 4*a*d :=
  @ThresholdHC.OptimalQuantile.scaled_root_bound_iff

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
""".lstrip()
    roots = {
        'ThresholdHC.OptimalQuantile.exponential_entropy',
        'ThresholdHC.OptimalQuantile.finitePartition_eq_sum',
        'ThresholdHC.OptimalQuantile.finiteVectorBound_iff_partition',
        'ThresholdHC.OptimalQuantile.price_iff_all_tangents',
        'ThresholdHC.OptimalQuantile.root_price_iff_entropy',
        'ThresholdHC.OptimalQuantile.root_price_iff_partition',
        'ThresholdHC.OptimalQuantile.scaled_root_bound_iff',
        'ThresholdHC.OptimalQuantile.sqrt_tangent',
        'ThresholdHC.OptimalQuantile.sqrt_tangent_attained',
        'ThresholdHC.OptimalQuantile.tangentOffset_nonneg',
        'ThresholdHC.OptimalQuantile.tangentWeight_pos',
        'ThresholdHC.OptimalQuantile.tangent_price_identity',
        'ThresholdHC.OptimalQuantile.weighted_entropy_iff_partition',
    }
    return source + "".join("#print axioms " + name + "\n" for name in sorted(roots)), roots


def main():
    source, roots = audit_input()
    subprocess.run(["lake", "build", "ThresholdHC.OptimalQuantile.Finite"], cwd=LEAN, check=True)
    run = subprocess.run(["lake", "env", "lean", "--stdin"], cwd=LEAN, input=source, text=True,
                         encoding="utf-8", capture_output=True)
    output = run.stdout + run.stderr
    print(output, end="")
    validate_reports(output, run.returncode, roots)
    print(f"Verified {len(roots)} transitive axiom reports")


if __name__ == "__main__":
    main()
