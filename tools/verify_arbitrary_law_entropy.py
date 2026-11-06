"""Exact types and transitive axioms for finite arbitrary-law entropy transports.

This audit does not establish countable measure transport, pilot concentration,
the robust statistical continuation, or the full adaptive controller.
"""

import subprocess
from verify_blind_upper_components import LEAN, validate_reports


def audit_input():
    source = """
import ThresholdHC.ArbitraryLawAdaptation.BandPenalty
noncomputable section
set_option linter.unusedVariables false
open Real
open scoped BigOperators
open ThresholdHC.EntropyTailQuantile ThresholdHC.ArbitraryLawAdaptation
variable {ι κ : Type*} [Fintype ι] [Fintype κ]

example : ∀ {a p : ι → ℝ} (ha : ∀ i, 0 ≤ a i) (hp : ∀ i, 0 ≤ p i)
    (hsupport : ∀ i, a i ≠ 0 → 0 < p i) (hpsum : (∑ i, p i) ≤ 1),
    costEntropy a ≤ ∑ i, a i * (1-log (p i)) := @costEntropy_le_supported_reference ι _

example : ∀ {a : ι → ℝ} (ha : ∀ i, 0 ≤ a i),
    costEntropy a = ∑ i, a i * (1-log (a i/costTotal a)) := @costEntropy_eq_reference_sum ι _

example : ∀ {a : ι → ℝ} {b : ι × κ → ℝ} {p : κ → ℝ} {L : ℝ}
    (ha : ∀ i, 0 ≤ a i) (hb : ∀ x, 0 ≤ b x)
    (hp : ∀ k, 0 < p k) (hpsum : (∑ k, p k) ≤ 1)
    (hrow : ∀ i, (∑ k, b (i,k)) ≤ a i)
    (hcode : ∀ i, (∑ k, b (i,k)*(-log (p k))) ≤ L*a i),
    costEntropy b ≤ costEntropy a + L*costTotal a := @costEntropy_transport_bound ι κ _ _

example : ∀ (s : Finset ι) {a : ι → ℝ} (ha : ∀ i, 0 ≤ a i),
    negMulLog (∑ i ∈ s, a i) ≤ ∑ i ∈ s, negMulLog (a i) := @negMulLog_sum_le ι

example : ∀ {b : ι × κ → ℝ} (hb : ∀ x, 0 ≤ b x),
    costEntropy (fun k => ∑ i, b (i,k)) ≤ costEntropy b := @costEntropy_merge ι κ _ _

example : ∀ {a : ι → ℝ} {f b : ι × κ → ℝ} {p r : κ → ℝ} {L : ℝ}
    (ha : ∀ i, 0 ≤ a i) (hf : ∀ x, 0 ≤ f x) (hb : ∀ x, 0 ≤ b x)
    (hrow : ∀ i, (∑ k, f (i,k)) ≤ a i)
    (hcost : ∀ x, b x ≤ r x.2*f x) (hr : ∀ k, r k ≤ 1)
    (hp : ∀ k, 0 < p k) (hpsum : (∑ k, p k) ≤ 1)
    (hL : 0 ≤ L) (hcode : ∀ k, r k*(-log (p k)) ≤ L),
    costEntropy b ≤ costEntropy a + L*costTotal a := @costEntropy_contracting_transport ι κ _ _

example [DecidableEq κ] : ∀ {b : ι → ℝ} (hb : ∀ i, 0 ≤ b i) (dest : ι → κ),
    costEntropy (fun k => ∑ i, if dest i = k then b i else 0) ≤ costEntropy b :=
  @costEntropy_pushforward ι κ _ _ _

example : bandContraction = fun k : ℕ => min 1 (4*(1/4:ℝ)^k) := rfl
example : ∀ k : ℕ, 0 ≤ bandContraction k := bandContraction_nonneg
example : ∀ k : ℕ, bandContraction k ≤ 1 := bandContraction_le_one
example : ∀ k : ℕ, (1/4:ℝ)^k*((k:ℝ)+2) ≤ 2 := quarter_power_linear
example : ∀ k : ℕ, bandContraction k*((k:ℝ)+1) ≤ 2 := bandContraction_weighted
example : ∀ n : ℕ, (∑ k : Fin n, (1/2:ℝ)^(k.val+1)) = 1-(1/2:ℝ)^n := half_power_sum
example : ∀ k : ℕ, bandContraction k*(-log ((1/2:ℝ)^(k+1))) ≤ 2 := bandContraction_code

example : ∀ {n : ℕ} {a : ι → ℝ} {f b : ι × Fin n → ℝ}
    (ha : ∀ i, 0 ≤ a i) (hf : ∀ x, 0 ≤ f x) (hb : ∀ x, 0 ≤ b x)
    (hrow : ∀ i, (∑ k, f (i,k)) ≤ a i)
    (hcost : ∀ x, b x ≤ bandContraction x.2.val*f x),
    costEntropy b ≤ 3*costEntropy a := @finite_band_transport_three ι _
"""
    roots = {"ThresholdHC.ArbitraryLawAdaptation." + name for name in [
        "costEntropy_le_supported_reference", "costEntropy_eq_reference_sum",
        "costEntropy_transport_bound", "negMulLog_sum_le", "costEntropy_merge",
        "costEntropy_contracting_transport", "costEntropy_pushforward",
        "bandContraction", "bandContraction_nonneg", "bandContraction_le_one",
        "quarter_power_linear", "bandContraction_weighted", "half_power_sum",
        "bandContraction_code", "finite_band_transport_three",
    ]}
    return source + "".join("#print axioms " + name + "\n" for name in sorted(roots)), roots


def main():
    source, roots = audit_input()
    subprocess.run(["lake", "build", "ThresholdHC.ArbitraryLawAdaptation.BandPenalty"],
                   cwd=LEAN, check=True)
    run = subprocess.run(["lake", "env", "lean", "-j1", "--stdin"], cwd=LEAN, input=source,
                         text=True, encoding="utf-8", capture_output=True)
    output = run.stdout + run.stderr
    print(output, end="")
    validate_reports(output, run.returncode, roots)
    print(f"Verified {len(roots)} exact statements and transitive axiom reports")


if __name__ == "__main__":
    main()
