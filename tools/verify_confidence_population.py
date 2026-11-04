"""Check the finite adaptive-population KL identity and the null-work transfer."""

import subprocess

from verify_blind_upper_components import LEAN, validate_reports
from verify_quarter_smoothing import audit_input as check_smoothing_spec


PREFIX = "ThresholdHC.ConfidenceTransfer."


def audit_input(module="CommonPairRate"):
    check_smoothing_spec()
    target = ["import " + PREFIX + module, "noncomputable section",
              "open MeasureTheory InformationTheory ThresholdHC.ConfidenceTransfer",
              "open ThresholdHC.CriticalEntropy", "open scoped ENNReal NNReal",
              "local instance : MeasurableSpace (Option Bool) := ⊤"]
    target += """
example {D : Type} [MeasurableSpace D] {m N : ℕ} (μ : Measure D) [IsProbabilityMeasure μ]
    (pol : List Bool → Option (Fin m)) (d q r : D → ℝ)
    (dm : Measurable d) (qm : Measurable q) (rm : Measurable r)
    (ds : ∀ x, 0 ≤ d x ∧ d x ≤ 1/2) (qs : ∀ x, 0 ≤ q x ∧ q x ≤ 1)
    (rs : ∀ x, 0 ≤ r x ∧ r x ≤ 1) :
    let W := fun u => finiteWeightMeasure (finitePopulationWeight (n := N) μ pol d u)
    let a := fun x => (3*q x+r x)/4
    let b := fun x => (q x+3*r x)/4
    klDiv (W (fun _ => a)) (W (fun _ => b)) =
      ∑ i : Fin m, klDiv (W (fun _ => a)) (W (fun j => if j=i then b else a)) := by
  simpa only [add_comm (q _) (3*r _)] using
    (quarter_population_hybrid_kl (n := N) μ pol d q r dm qm rm ds qs rs)
""".strip().splitlines()
    names = ["finite_weight_kl", "finite_weight_gibbs", "population_hybrid_kl",
             "quarter_coin_mass", "quarter_population_hybrid_kl"]
    if module != "Hybrid":
        target += """
example {D : Type} [MeasurableSpace D] {m N : ℕ}
    (μ : Measure D) [IsProbabilityMeasure μ] (p₀ p₁ q r : D → unitInterval)
    (h₀ : Measurable p₀) (h₁ : Measurable p₁) (hq : Measurable q) (hr : Measurable r)
    (hq' : ∀ x, (q x : ℝ) ≤ 1/2) (hr' : ∀ x, (r x : ℝ) ≤ 1/2)
    (d : D → ℝ) (dm : Measurable d) (ds : ∀ x, 0 ≤ d x ∧ d x ≤ 1/2)
    (dn : ∀ᵐ x ∂μ, (p₀ x : ℝ) = 1/2-d x) (dp : ∀ᵐ x ∂μ, (p₁ x : ℝ) = 1/2+d x)
    (pol : List Bool → Option (Fin m)) (κ : ℝ) (hk : 0 ≤ κ)
    (bound : let ν := Measure.pi (fun _ : Fin m =>
        parameterTapeLaw (populationParameterLaw μ p₀ p₁ (quarterPrior q r)))
      ∀ i : Fin m, let A := localSimulationProcedure i N pol
        1-(hellingerAffinity (cappedTranscriptLaw μ ν p₀ p₁ q A N)
                             (cappedTranscriptLaw μ ν p₀ p₁ r A N)).toReal ≤
          κ*(populationExpectedWork μ ν p₀ p₁ (fun _ => 0) A).toReal) :
    let W := fun u => finiteWeightMeasure (finitePopulationWeight (n := N) μ pol d (fun _ => u))
    klDiv (W (fun x => (3*(q x : ℝ)+(r x : ℝ))/4))
      (W (fun x => (3*(r x : ℝ)+(q x : ℝ))/4)) ≤
        ENNReal.ofReal ((16/3)*κ*(finitePopulationExpectedWork μ p₀ p₁ (quarterPrior q r) pol N).toReal) :=
  finite_null_work_kl μ p₀ p₁ q r h₀ h₁ hq hr hq' hr' d dm ds dn dp pol κ hk bound
""".strip().splitlines()
        names += ["quarterPrior", "measurable_quarterPrior", "finite_null_work_kl"]
    if module in ("Testing", "CommonPairRate"):
        names += ["LocalNullWorkBound", "creation_null_work_kl", "smoothedSign",
                  "smoothedSign_rare", "smoothedSign_separation", "observable_null_work_kl",
                  "stopped_observable_kl_eq_iSup", "stopped_null_work_kl", "pair_confidence_work"]
        target += """
open ThresholdHC.Tier3 ThresholdHC.Tier6 ThresholdHC.RareAboveTwo ThresholdHC.ObservableSimulation
variable {R : Type} [MeasurableSpace R] (μ : Measure Gap) [IsProbabilityMeasure μ]
  (A : AdaptiveEstimator R) (q r : SignLaw) (hq : ∀ d, q.val d ≤ 1/2)
  (hr : ∀ d, r.val d ≤ 1/2) {κ B ρ ε δ : ℝ} (hk : 0 ≤ κ) (hb : 0 ≤ B)
  (loc : LocalNullWorkBound μ (gapParameter false) (gapParameter true) (signUnit q) (signUnit r) κ)
example (N : ℕ) :
    klDiv (observablePrefixLaw μ A (smoothedSign q r) N) (observablePrefixLaw μ A (smoothedSign r q) N) ≤
      ENNReal.ofReal ((16/3)*κ*∫ z, ThresholdHC.workOf (processPrefix N z.2)
        ∂experimentLaw μ A (smoothedSign q r)) := observable_null_work_kl μ A q r hq hr N κ hk loc
example (w : expectedWork μ A (smoothedSign q r) ≤ ENNReal.ofReal B)
    (w' : expectedWork μ A (smoothedSign r q) < ∞) :
    klDiv (observableDecisionLaw μ A (smoothedSign q r) id) (observableDecisionLaw μ A (smoothedSign r q) id)
      ≤ ENNReal.ofReal ((16/3)*κ*B) := stopped_null_work_kl μ A q r hq hr κ B hk hb loc w w'
example (d : 0 < δ) (d' : δ ≤ 1/4) (rq : RarePrior μ ρ q) (rr : RarePrior μ ρ r)
    (w : RareBudget μ A ρ B) (conf : ∀ s : SignLaw, RarePrior μ ρ s →
      ThresholdHC.Confidence.failureProbability μ A s ε ≤ ENNReal.ofReal δ)
    (sep : 4*ε < signMean μ q.val - signMean μ r.val) :
    Real.log (1/δ)/4 ≤ (16/3)*κ*B :=
  pair_confidence_work μ A q r hb hk d d' rq rr hq hr loc w conf sep
""".strip().splitlines()
    if module == "CommonPairRate":
        names += ["CommonPairBound", "confidence_rate_of_common_pair",
                  "rareConfidenceRadius", "minimax_confidence_rate_of_common_pair"]
        target += """
example {b J : ℝ} (hpos : 0 < b) (hj : 0 < J) (hb' : 0 < B) (d : 0 < δ) (d' : δ ≤ 1/4)
    (cp : CommonPairBound μ ρ b J) :
    ENNReal.ofReal ((1/128) * min b (Real.sqrt (J*Real.log (1/δ)/B))) ≤ rareConfidenceRadius μ ρ B δ := by
  convert minimax_confidence_rate_of_common_pair μ hpos hj hb' d d' cp using 2
  ring
""".strip().splitlines()
    roots = {PREFIX + name for name in names}
    return "\n".join(target + ["#print axioms " + root for root in sorted(roots)]) + "\n", roots


def main():
    source, roots = audit_input()
    subprocess.run(["lake", "build", PREFIX + "CommonPairRate"], cwd=LEAN, check=True)
    run = subprocess.run(["lake", "env", "lean", "--stdin"], cwd=LEAN, input=source,
                         text=True, encoding="utf-8", capture_output=True)
    output = run.stdout + run.stderr
    print(output, end="")
    validate_reports(output, run.returncode, roots)
    print(f"Verified {len(roots)} transitive axiom reports")


if __name__ == "__main__":
    main()
