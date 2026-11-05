"""Audit finite-law realization and sharpness of the quantile factor."""

import subprocess

from verify_blind_upper_components import LEAN, validate_reports


def audit_input():
    source = """
import ThresholdHC.QuantileOptimality.CoreMeasure
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
""".lstrip()
    roots = {
        'ThresholdHC.QuantileOptimality.aboveGap_band',
        'ThresholdHC.QuantileOptimality.aboveGap_gt_boundary',
        'ThresholdHC.QuantileOptimality.aboveGap_lt_half',
        'ThresholdHC.QuantileOptimality.bandCost_smul',
        'ThresholdHC.QuantileOptimality.boundaryAtom_le_law',
        'ThresholdHC.QuantileOptimality.boundaryAtom_mass',
        'ThresholdHC.QuantileOptimality.boundaryAtom_mass_at_edge',
        'ThresholdHC.QuantileOptimality.boundaryAtom_split',
        'ThresholdHC.QuantileOptimality.boundaryCore_le_realizingCore',
        'ThresholdHC.QuantileOptimality.chosenRarity_le_quarter',
        'ThresholdHC.QuantileOptimality.chosenRarity_pos',
        'ThresholdHC.QuantileOptimality.coreGap_gt_edge',
        'ThresholdHC.QuantileOptimality.coreGap_lt_half',
        'ThresholdHC.QuantileOptimality.easyAtom_mass',
        'ThresholdHC.QuantileOptimality.easyMass_bounds',
        'ThresholdHC.QuantileOptimality.edgeGap_band',
        'ThresholdHC.QuantileOptimality.inverseScale_pos',
        'ThresholdHC.QuantileOptimality.keptMeasure_le_law',
        'ThresholdHC.QuantileOptimality.massScale_ge_one',
        'ThresholdHC.QuantileOptimality.massScale_le_upperMass',
        'ThresholdHC.QuantileOptimality.measureCostEntropy_smul',
        'ThresholdHC.QuantileOptimality.packet_add',
        'ThresholdHC.QuantileOptimality.packet_entropy_le',
        'ThresholdHC.QuantileOptimality.packet_entropy_toReal_le',
        'ThresholdHC.QuantileOptimality.packet_finite',
        'ThresholdHC.QuantileOptimality.packet_real_bandCost',
        'ThresholdHC.QuantileOptimality.packet_real_mass',
        'ThresholdHC.QuantileOptimality.packet_sum_mass',
        'ThresholdHC.QuantileOptimality.packet_sum_support_finite',
        'ThresholdHC.QuantileOptimality.packet_sum_support_lower',
        'ThresholdHC.QuantileOptimality.packet_support_finite',
        'ThresholdHC.QuantileOptimality.packet_support_lower',
        'ThresholdHC.QuantileOptimality.packet_support_subset',
        'ThresholdHC.QuantileOptimality.packet_tailModulus',
        'ThresholdHC.QuantileOptimality.packet_tailModulus_of_small',
        'ThresholdHC.QuantileOptimality.quantileTail_at_min_atom',
        'ThresholdHC.QuantileOptimality.quantileThreshold_at_min_atom',
        'ThresholdHC.QuantileOptimality.realizingLaw_atom_lower',
        'ThresholdHC.QuantileOptimality.realizingLaw_mass',
        'ThresholdHC.QuantileOptimality.realizingLaw_probability',
        'ThresholdHC.QuantileOptimality.realizingLaw_quantileCore',
        'ThresholdHC.QuantileOptimality.realizingLaw_quantileTail',
        'ThresholdHC.QuantileOptimality.realizingLaw_split',
        'ThresholdHC.QuantileOptimality.realizingLaw_support_finite',
        'ThresholdHC.QuantileOptimality.realizingLaw_support_lower',
        'ThresholdHC.QuantileOptimality.skippedAtoms_mass',
        'ThresholdHC.QuantileOptimality.skipped_packet_le_realizingCore',
        'ThresholdHC.QuantileOptimality.tailModulus_finset_sum',
        'ThresholdHC.QuantileOptimality.tail_packet_identity',
        'ThresholdHC.QuantileOptimality.upperMass_ge_one',
    }
    return source + "".join("#print axioms " + name + "\n" for name in sorted(roots)), roots


def main():
    source, roots = audit_input()
    subprocess.run(["lake", "build", "ThresholdHC.QuantileOptimality.CoreMeasure"], cwd=LEAN, check=True)
    run = subprocess.run(["lake", "env", "lean", "--stdin"], cwd=LEAN, input=source, text=True,
                         encoding="utf-8", capture_output=True)
    output = run.stdout + run.stderr
    print(output, end="")
    validate_reports(output, run.returncode, roots)
    print(f"Verified {len(roots)} transitive axiom reports")


if __name__ == "__main__":
    main()
