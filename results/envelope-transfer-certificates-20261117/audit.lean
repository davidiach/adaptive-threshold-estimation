import ThresholdHC.EnvelopeTransferCertificates.Transfer
open ThresholdHC.EnvelopeTransferCertificates
open MeasureTheory
open scoped ENNReal BigOperators
open ThresholdHC.Tier6 ThresholdHC.FiniteLawCertificates
open ThresholdHC.DeterministicCertificates ThresholdHC.ArbitraryLawAdaptation ThresholdHC.EntropyTail

example {n : ℕ} (z : ℚ) (d : Fin n → Gap) (w : Fin n → ℚ)
    (hz : 0 ≤ z) (hw : ∀ i, 0 ≤ w i) (hs : z+∑ i,w i=1) :
    IsProbabilityMeasure (extendedAtomic z d w) :=
  extendedAtomic_probability z d w hz hw hs

example {n : ℕ} (z : ℚ) (d : Fin n → Gap) (w : Fin n → ℚ) :
    extendedAtomic z d w {0} = ENNReal.ofReal (z:ℝ) :=
  extendedAtomic_zero z d w

example {n : ℕ} (z : ℚ) (d : Fin n → Gap) (w : Fin n → ℚ)
    (hz : 0 ≤ z) (hw : ∀ i, 0 ≤ w i) (f : ℝ → ℝ) :
    (∫ x, f x ∂extendedAtomic z d w) = (z:ℝ)*f 0 + ∑ i, (w i:ℝ)*f (d i) :=
  extended_integral z d w hz hw f

example {n : ℕ} (z : ℚ) (d : Fin n → Gap) (w : Fin n → ℚ)
    {ρ B : ℝ} (hρ : 0 < ρ) (hB : 0 < B) (hz : ρ ≤ (z:ℝ)) :
    zeroSelection (extendedAtomic z d w) ρ B = ENNReal.ofReal ρ :=
  fallback_selection z d w hρ hB hz

example {n : ℕ} (z : ℚ) (d : Fin n → Gap) (w : Fin n → ℚ)
    (hz : z < 1) :
    extendedAtomic z d w = zeroAtomLaw (z:ℝ) (atomicMeasure d (fun i => w i/(1-z))) :=
  normalized_identity z d w hz

example {n : ℕ} (z : ℚ) (d : Fin n → Gap) (w s : Fin n → ℚ)
    (hz : z < 1) {ρ : ℝ}
    (hcore : ThresholdHC.EntropyTailQuantile.quantileCore
      (atomicMeasure d (fun i => w i/(1-z))) ρ =
        atomicMeasure d (fun i => (w i/(1-z))*s i)) :
    ENNReal.ofReal (1-(z:ℝ)) • ThresholdHC.EntropyTailQuantile.quantileCore
      (atomicMeasure d (fun i => w i/(1-z))) ρ = atomicMeasure d (fun i => w i*s i) :=
  scaled_core z d w s hz hcore

example {n : ℕ} (c : Fin (n+1) → ℚ) (hc : Antitone c) :
    Antitone (extendCDF c) :=
  extendCDF_antitone c hc

example (pairs : List (Gap × Gap)) : Measurable (pointMap pairs) :=
  pointMap_measurable pairs

example (pairs : List (Gap × Gap)) {r : ℝ} (hr : 1 ≤ r)
    (hp : ∀ p ∈ pairs, (p.1:ℝ) ≤ (p.2:ℝ) ∧ (p.2:ℝ) ≤ r*(p.1:ℝ)) :
    ∀ x : Gap, (x:ℝ) ≤ (pointMap pairs x:ℝ) ∧ (pointMap pairs x:ℝ) ≤ r*(x:ℝ) :=
  pointMap_bounds pairs hr hp

example (pairs : List (Gap × Gap))
    (hp : ∀ p ∈ pairs, ∃ j, p.1 ∈ ThresholdHC.EntropyTail.band j ∧ p.2 ∈ ThresholdHC.EntropyTail.band j) :
    ∀ j, pointMap pairs ⁻¹' ThresholdHC.EntropyTail.band j = ThresholdHC.EntropyTail.band j :=
  pointMap_bands pairs hp

example {n m : ℕ} (e : Fin m → Gap) (w : Fin n → ℚ)
    (hw : ∀ i, 0 ≤ w i) (route : Fin n → Fin m) :
    atomicMeasure (fun i => e (route i)) w =
      atomicMeasure e (fun j => ∑ i, if route i=j then w i else 0) :=
  atomic_group e w hw route

example (μ μ₀ : Measure Gap) [IsProbabilityMeasure μ] [IsProbabilityMeasure μ₀]
    (T : Gap → Gap) (hm : Measurable T) (r η ρ B : ℚ) (hr : 1 ≤ r)
    (hρ : 0 < ρ) (hρ1 : ρ ≤ 1/4) (hB : 0 < B)
    (hη : tvDist μ μ₀ / 2 ≤ (η:ℝ))
    (hd : ∀ d : Gap, (d:ℝ) ≤ (T d:ℝ) ∧ (T d:ℝ) ≤ (r:ℝ)*(d:ℝ))
    (hb : ∀ j, T ⁻¹' band j = band j)
    (input output : Interval) (hi : Contains input (selection (μ₀.map T) (ρ:ℝ) (B:ℝ)).toReal)
    (hc : transferCheck input output r η ρ = true) :
    Contains output (selection μ (ρ:ℝ) (B:ℝ)).toReal :=
  transfer_original μ μ₀ T hm r η ρ B hr hρ hρ1 hB hη hd hb input output hi hc
#print axioms ThresholdHC.EnvelopeTransferCertificates.atomic_group
#print axioms ThresholdHC.EnvelopeTransferCertificates.common_band
#print axioms ThresholdHC.EnvelopeTransferCertificates.extendCDF
#print axioms ThresholdHC.EnvelopeTransferCertificates.extendCDF_antitone
#print axioms ThresholdHC.EnvelopeTransferCertificates.extendCDF_nonneg
#print axioms ThresholdHC.EnvelopeTransferCertificates.extendedAtomic
#print axioms ThresholdHC.EnvelopeTransferCertificates.extendedAtomic_finite
#print axioms ThresholdHC.EnvelopeTransferCertificates.extendedAtomic_probability
#print axioms ThresholdHC.EnvelopeTransferCertificates.extendedAtomic_zero
#print axioms ThresholdHC.EnvelopeTransferCertificates.extended_integral
#print axioms ThresholdHC.EnvelopeTransferCertificates.fallback_selection
#print axioms ThresholdHC.EnvelopeTransferCertificates.map_atomic
#print axioms ThresholdHC.EnvelopeTransferCertificates.map_atomic_gap
#print axioms ThresholdHC.EnvelopeTransferCertificates.normalized_identity
#print axioms ThresholdHC.EnvelopeTransferCertificates.pointMap
#print axioms ThresholdHC.EnvelopeTransferCertificates.pointMap_bands
#print axioms ThresholdHC.EnvelopeTransferCertificates.pointMap_bounds
#print axioms ThresholdHC.EnvelopeTransferCertificates.pointMap_measurable
#print axioms ThresholdHC.EnvelopeTransferCertificates.scaled_core
#print axioms ThresholdHC.EnvelopeTransferCertificates.transferCheck
#print axioms ThresholdHC.EnvelopeTransferCertificates.transferCheck_sound
#print axioms ThresholdHC.EnvelopeTransferCertificates.transfer_original
