import ThresholdHC.FiniteLawCertificates.Oracles
open ThresholdHC.FiniteLawCertificates
open MeasureTheory
open scoped ENNReal BigOperators
open ThresholdHC.Tier6 ThresholdHC.DeterministicCertificates

example {n : ℕ} (d : Fin n → Gap) (w : Fin n → ℚ)
    (hw : ∀ i, 0 ≤ w i) (hs : ∑ i, w i = 1) : IsProbabilityMeasure (atomicMeasure d w) :=
  atomicMeasure_probability d w hw hs

example {n : ℕ} (d : Fin n → Gap) (w : Fin n → ℚ) (hw : ∀ i, 0 ≤ w i) (f : Gap → ℝ) :
    (∫ x, f x ∂atomicMeasure d w) = ∑ i, (w i:ℝ)*f (d i) := integral_atomic d w hw f

example {n : ℕ} (d : Fin n → Gap) (w s : Fin n → ℚ)
    (hw : ∀ i, 0 ≤ w i) (hsum : ∑ i, w i = 1) {ρ t : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (r : ℚ) (hr : r ≤ 1)
    (hbelow : (∑ i, if (d i:ℝ) < t then (w i:ℝ) else 0) < ρ)
    (habove : ρ ≤ ∑ i, if (d i:ℝ) ≤ t then (w i:ℝ) else 0)
    (hb : (r:ℝ) = (ρ-(∑ i, if (d i:ℝ) < t then (w i:ℝ) else 0)) /
      (∑ i, if (d i:ℝ) = t then (w i:ℝ) else 0))
    (hs : ∀ i, s i = if (d i:ℝ) < t then 0 else if (d i:ℝ) = t then 1-r else 1) :
    ThresholdHC.EntropyTailQuantile.quantileCore (atomicMeasure d w) ρ =
      atomicMeasure d (fun i => w i*s i) :=
  quantileCore_atomic d w s hw hsum hρ hρ1 r hr hbelow habove hb hs

example {n m : ℕ} (g w s : Fin n → ℚ) (labels : Fin m → ℕ) (ρ B : ℚ)
    (hg : ∀ i, 0 < g i ∧ g i ≤ 1/2) (hw : ∀ i, 0 ≤ w i)
    (hs : ∀ i, 0 ≤ s i ∧ s i ≤ 1) (hρ : 0 ≤ ρ) (hB : 0 < B)
    (hi : Function.Injective labels) (hc : ∀ i, ∃ j, inBand (g i) (labels j) = true) :
    min (ENNReal.ofReal (ρ:ℝ)) (ThresholdHC.EntropyTail.selectionObjective
      (atomicMeasure (points g hg) w) (ρ:ℝ) (B:ℝ)
      (atomicMeasure (points g hg) (fun i => w i*s i))) =
      ENNReal.ofReal (objectiveExpr g w s labels ρ B).eval :=
  capped_objective_eq g w s labels ρ B hg hw hs hρ hB hi hc

example {n m : ℕ} (g w s : Fin n → ℚ) (labels : Fin m → ℕ) (ρ B : ℚ)
    (hg : ∀ i, 0 < g i ∧ g i ≤ 1/2) (hw : ∀ i, 0 ≤ w i)
    (hs : ∀ i, 0 ≤ s i ∧ s i ≤ 1) (hρ : 0 ≤ ρ) (hB : 0 < B)
    (hi : Function.Injective labels) (hc : ∀ i, ∃ j, inBand (g i) (labels j) = true)
    {claimed : Interval} {c : Evidence}
    (h : accepted (objectiveExpr g w s labels ρ B) claimed c = true) :
    Contains claimed (min (ENNReal.ofReal (ρ:ℝ)) (ThresholdHC.EntropyTail.selectionObjective
      (atomicMeasure (points g hg) w) (ρ:ℝ) (B:ℝ)
      (atomicMeasure (points g hg) (fun i => w i*s i)))).toReal :=
  objective_accepted_sound g w s labels ρ B hg hw hs hρ hB hi hc h

example {n m : ℕ} (g w s : Fin n → ℚ) (labels : Fin m → ℕ) (ρ B : ℚ)
    (hg : ∀ i, 0 < g i ∧ g i ≤ 1/2) (hw : ∀ i, 0 ≤ w i)
    (hs : ∀ i, 0 ≤ s i ∧ s i ≤ 1) (hρ : 0 ≤ ρ) (hB : 0 < B)
    (hi : Function.Injective labels) (hc : ∀ i, ∃ j, inBand (g i) (labels j) = true)
    {claimed : Interval} {c : Evidence}
    (h : accepted (objectiveExpr g w s labels ρ B) claimed c = true) :
    (ThresholdHC.EntropyTail.selection (atomicMeasure (points g hg) w) (ρ:ℝ) (B:ℝ)).toReal ≤
      (claimed.upper:ℝ) := selection_upper g w s labels ρ B hg hw hs hρ hB hi hc h

example {n : ℕ} (g w s : Fin n → ℚ) (B : ℚ)
    (hg : ∀ i, 0 < g i ∧ g i ≤ 1/2) (hw : ∀ i, 0 ≤ w i)
    (hs : ∀ i, 0 ≤ s i ∧ s i ≤ 1) :
    (atomicMeasure (points g hg) w-atomicMeasure (points g hg) (fun i => w i*s i)).restrict
      {x : Gap | 1 ≤ (B:ℝ)*(x:ℝ)^2} = atomicMeasure (points g hg) (tailWeights g w s B) :=
  tailMeasure_eq g w s B hg hw hs

example {n : ℕ} (g w : Fin n → ℚ) (hg : ∀ i, 0 < g i ∧ g i ≤ 1/2)
    (hw : ∀ i, 0 ≤ w i) (heads tails : ℕ) :
    nullPrefixIntegral (atomicMeasure (points g hg) w) heads tails =
      (nullPrefixValue g w heads tails:ℝ) := nullPrefix_eq g w hg hw heads tails

example {n : ℕ} (g v : Fin n → ℚ) (M : ℚ) (hg : ∀ i, 0 < g i ∧ g i ≤ 1/2)
    (hv : ∀ i, 0 ≤ v i) :
    (∫ x : Gap, min 1 (1/((M:ℝ)*(x:ℝ)^2)^2) ∂atomicMeasure (points g hg) v) =
      (errorValue g v M:ℝ) := errorIntegral_eq g v M hg hv

example {n : ℕ} (g v : Fin n → ℚ) (M : ℚ) (hg : ∀ i, 0 < g i ∧ g i ≤ 1/2)
    (hv : ∀ i, 0 ≤ v i) {claimed : Interval} {c : Evidence}
    (h : accepted (tailWorkExpr g v M) claimed c = true) :
    Contains claimed (tailWorkIntegral (atomicMeasure (points g hg) v) (M:ℝ)) :=
  tailWork_accepted_sound g v M hg hv h
#print axioms ThresholdHC.FiniteLawCertificates.atomicMeasure
#print axioms ThresholdHC.FiniteLawCertificates.atomicMeasure_add
#print axioms ThresholdHC.FiniteLawCertificates.atomicMeasure_finite
#print axioms ThresholdHC.FiniteLawCertificates.atomicMeasure_le
#print axioms ThresholdHC.FiniteLawCertificates.atomicMeasure_probability
#print axioms ThresholdHC.FiniteLawCertificates.atomicMeasure_real
#print axioms ThresholdHC.FiniteLawCertificates.atomicMeasure_restrict
#print axioms ThresholdHC.FiniteLawCertificates.atomicMeasure_smul
#print axioms ThresholdHC.FiniteLawCertificates.atomicMeasure_sub
#print axioms ThresholdHC.FiniteLawCertificates.atomicMeasure_univ
#print axioms ThresholdHC.FiniteLawCertificates.bandCost_atomic
#print axioms ThresholdHC.FiniteLawCertificates.capped_objective_eq
#print axioms ThresholdHC.FiniteLawCertificates.costs
#print axioms ThresholdHC.FiniteLawCertificates.costs_cast
#print axioms ThresholdHC.FiniteLawCertificates.costs_nonneg
#print axioms ThresholdHC.FiniteLawCertificates.errorIntegral_eq
#print axioms ThresholdHC.FiniteLawCertificates.errorValue
#print axioms ThresholdHC.FiniteLawCertificates.gamma_atomic
#print axioms ThresholdHC.FiniteLawCertificates.gamma_rational
#print axioms ThresholdHC.FiniteLawCertificates.inBand
#print axioms ThresholdHC.FiniteLawCertificates.integrable_atomic
#print axioms ThresholdHC.FiniteLawCertificates.integral_atomic
#print axioms ThresholdHC.FiniteLawCertificates.inverseIntegral_eq
#print axioms ThresholdHC.FiniteLawCertificates.inverseValue
#print axioms ThresholdHC.FiniteLawCertificates.lintegral_atomic
#print axioms ThresholdHC.FiniteLawCertificates.lintegral_ofReal_atomic
#print axioms ThresholdHC.FiniteLawCertificates.nullPrefixIntegral
#print axioms ThresholdHC.FiniteLawCertificates.nullPrefixValue
#print axioms ThresholdHC.FiniteLawCertificates.nullPrefix_eq
#print axioms ThresholdHC.FiniteLawCertificates.objectiveExpr
#print axioms ThresholdHC.FiniteLawCertificates.objectiveExpr_eval
#print axioms ThresholdHC.FiniteLawCertificates.objectiveExpr_nonneg
#print axioms ThresholdHC.FiniteLawCertificates.objective_accepted_sound
#print axioms ThresholdHC.FiniteLawCertificates.points
#print axioms ThresholdHC.FiniteLawCertificates.points_mem_band
#print axioms ThresholdHC.FiniteLawCertificates.quantileCore_atomic
#print axioms ThresholdHC.FiniteLawCertificates.quantileThreshold_eq_of_mass
#print axioms ThresholdHC.FiniteLawCertificates.resolvedMeasure_eq
#print axioms ThresholdHC.FiniteLawCertificates.resolvedWeights
#print axioms ThresholdHC.FiniteLawCertificates.selected_le
#print axioms ThresholdHC.FiniteLawCertificates.selection_upper
#print axioms ThresholdHC.FiniteLawCertificates.sqrt_reciprocal
#print axioms ThresholdHC.FiniteLawCertificates.tailCost_atomic
#print axioms ThresholdHC.FiniteLawCertificates.tailMeasure_eq
#print axioms ThresholdHC.FiniteLawCertificates.tailWeights
#print axioms ThresholdHC.FiniteLawCertificates.tailWeights_nonneg
#print axioms ThresholdHC.FiniteLawCertificates.tailWorkExpr
#print axioms ThresholdHC.FiniteLawCertificates.tailWorkExpr_eval
#print axioms ThresholdHC.FiniteLawCertificates.tailWorkIntegral
#print axioms ThresholdHC.FiniteLawCertificates.tailWork_accepted_sound
#print axioms ThresholdHC.FiniteLawCertificates.unresolvedMeasure_eq
#print axioms ThresholdHC.FiniteLawCertificates.unresolvedWeights
