"""Audit countable band entropy transport and its canonical Gamma bridge.

Destination columns are locally summable; no global finite moment is assumed.
Constructing the band cells from an increasing-gap coupling remains separate.
"""

import subprocess
from verify_blind_upper_components import LEAN, validate_reports


def audit_input():
    source = """
import ThresholdHC.ArbitraryLawAdaptation.GammaTransport
noncomputable section
set_option linter.unusedVariables false
open MeasureTheory Filter
open scoped BigOperators ENNReal Topology
open ThresholdHC.ArbitraryLawAdaptation ThresholdHC.EntropyTailQuantile
open ThresholdHC.Tier6 (Gap)

example : ∀ a : ℕ → ℝ, countableEntropy a =
    ⨆ n : ℕ, ENNReal.ofReal (costEntropy (fun i : Fin n => a i.val)) := fun _ => rfl
example : ∀ (a : ℕ → ℝ) (n : ℕ),
    ENNReal.ofReal (costEntropy (fun i : Fin n => a i.val)) ≤ countableEntropy a :=
  prefix_le_countableEntropy
example : ∀ {a b : ℕ → ℝ} (ha : ∀ i, 0 ≤ a i) (hab : ∀ i, a i ≤ b i),
    countableEntropy a ≤ countableEntropy b := @countableEntropy_mono
example : ∀ {v : ℕ → ℕ → ℝ} {a : ℕ → ℝ} {C : ℝ≥0∞}
    (hv : ∀ j, Tendsto (fun n => v n j) atTop (𝓝 (a j)))
    (hbound : ∀ n, countableEntropy (v n) ≤ C), countableEntropy a ≤ C :=
  @countableEntropy_limit_le
example {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ] :
    ∀ {b : ι → ℝ} (hb : ∀ i, 0 ≤ b i) (dest : ι → Option κ),
    costEntropy (fun k => ∑ i, if dest i = some k then b i else 0) ≤ costEntropy b :=
  @costEntropy_partial_pushforward ι κ _ _ _
example {ι : Type*} [Fintype ι] : ∀ {b : ι → ℝ} (hb : ∀ i, 0 ≤ b i)
    (dest : ι → ℕ) (m : ℕ),
    costEntropy (fun j : Fin m => ∑ i, if dest i = j.val then b i else 0) ≤ costEntropy b :=
  @costEntropy_finite_destination_prefix ι _
example : Tendsto (fun n : ℕ => (Finset.range n).product (Finset.range n)) atTop atTop :=
  tendsto_square_ranges
example : ∀ {b : ℕ × ℕ → ℝ} (hb : Summable b),
    Tendsto (fun n => ∑ x : Fin n × Fin n, b (x.1.val,x.2.val)) atTop (𝓝 (∑' x, b x)) :=
  @summable_tendsto_square

example : ∀ (b : ℕ × ℕ → ℝ) (dest : ℕ × ℕ → ℕ) (n j : ℕ),
    partialTransport b dest n j =
      ∑ x : Fin n × Fin n, if dest (x.1.val,x.2.val) = j then b (x.1.val,x.2.val) else 0 :=
  fun _ _ _ _ => rfl
example : ∀ {b : ℕ × ℕ → ℝ} (hb : ∀ x, 0 ≤ b x) (dest : ℕ × ℕ → ℕ) (n j : ℕ),
    0 ≤ partialTransport b dest n j := @partialTransport_nonneg
example : ∀ {a : ℕ → ℝ} {f b : ℕ × ℕ → ℝ}
    (ha : ∀ i, 0 ≤ a i) (hf : ∀ x, 0 ≤ f x) (hb : ∀ x, 0 ≤ b x)
    (hrow : ∀ i n, (∑ k : Fin n, f (i,k.val)) ≤ a i)
    (hcost : ∀ x, b x ≤ bandContraction x.2*f x) (dest : ℕ × ℕ → ℕ) (n m : ℕ),
    costEntropy (fun j : Fin m => partialTransport b dest n j.val) ≤
      3*costEntropy (fun i : Fin n => a i.val) := @partialTransport_entropy_le
example : ∀ {a : ℕ → ℝ} {f b : ℕ × ℕ → ℝ}
    (ha : ∀ i, 0 ≤ a i) (hf : ∀ x, 0 ≤ f x) (hb : ∀ x, 0 ≤ b x)
    (hrow : ∀ i n, (∑ k : Fin n, f (i,k.val)) ≤ a i)
    (hcost : ∀ x, b x ≤ bandContraction x.2*f x) (dest : ℕ × ℕ → ℕ) (n : ℕ),
    countableEntropy (partialTransport b dest n) ≤ 3*countableEntropy a :=
  @partialTransport_countableEntropy_le
example : ∀ {b : ℕ × ℕ → ℝ} (dest : ℕ × ℕ → ℕ)
    (hcol : ∀ j, Summable (fun x => if dest x = j then b x else 0)) (j : ℕ),
    Tendsto (fun n => partialTransport b dest n j) atTop
      (𝓝 (∑' x, if dest x = j then b x else 0)) := @partialTransport_tendsto
example : ∀ {a : ℕ → ℝ} {f b : ℕ × ℕ → ℝ}
    (ha : ∀ i, 0 ≤ a i) (hf : ∀ x, 0 ≤ f x) (hb : ∀ x, 0 ≤ b x)
    (hrow : ∀ i n, (∑ k : Fin n, f (i,k.val)) ≤ a i)
    (hcost : ∀ x, b x ≤ bandContraction x.2*f x) (dest : ℕ × ℕ → ℕ)
    (hcol : ∀ j, Summable (fun x => if dest x = j then b x else 0)),
    countableEntropy (fun j => ∑' x, if dest x = j then b x else 0) ≤
      3*countableEntropy a := @countable_band_transport_three

example : ∀ (σ : Measure Gap) [IsFiniteMeasure σ],
    countableEntropy (fun j => (ThresholdHC.EntropyTail.bandCost σ j).toReal) =
      ThresholdHC.EntropyTail.gamma σ := @countableEntropy_bandCosts_eq_gamma
example : ∀ (σ τ : Measure Gap) [IsFiniteMeasure σ] [IsFiniteMeasure τ]
    {f b : ℕ × ℕ → ℝ} (hf : ∀ x, 0 ≤ f x) (hb : ∀ x, 0 ≤ b x)
    (hrow : ∀ i n, (∑ k : Fin n, f (i,k.val)) ≤ (ThresholdHC.EntropyTail.bandCost τ i).toReal)
    (hcost : ∀ x, b x ≤ bandContraction x.2*f x) (dest : ℕ × ℕ → ℕ)
    (hcol : ∀ j, Summable (fun x => if dest x = j then b x else 0))
    (hband : ∀ j, (ThresholdHC.EntropyTail.bandCost σ j).toReal =
      ∑' x, if dest x = j then b x else 0),
    ThresholdHC.EntropyTail.gamma σ ≤ 3*ThresholdHC.EntropyTail.gamma τ :=
  @gamma_le_three_of_band_transport
"""
    roots = {"ThresholdHC.ArbitraryLawAdaptation." + name for name in [
        "countableEntropy", "prefix_le_countableEntropy", "countableEntropy_mono",
        "countableEntropy_limit_le", "costEntropy_partial_pushforward",
        "costEntropy_finite_destination_prefix", "tendsto_square_ranges", "summable_tendsto_square",
        "partialTransport", "partialTransport_nonneg", "partialTransport_entropy_le",
        "partialTransport_countableEntropy_le", "partialTransport_tendsto",
        "countable_band_transport_three", "countableEntropy_bandCosts_eq_gamma",
        "gamma_le_three_of_band_transport",
    ]}
    return source + "".join("#print axioms " + name + "\n" for name in sorted(roots)), roots


def main():
    source, roots = audit_input()
    subprocess.run(["lake", "build", "ThresholdHC.ArbitraryLawAdaptation.GammaTransport"],
                   cwd=LEAN, check=True)
    run = subprocess.run(["lake", "env", "lean", "-j1", "--stdin"], cwd=LEAN, input=source,
                         text=True, encoding="utf-8", capture_output=True)
    output = run.stdout + run.stderr
    print(output, end="")
    validate_reports(output, run.returncode, roots)
    print(f"Verified {source.count('example ')} exact statements and {len(roots)} transitive reports")


if __name__ == "__main__":
    main()
