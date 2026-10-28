import ThresholdHC.OracleLower.Model

/-!
Full targets fixed before lower-bound and semantic-embedding proofs. The
experiment is canonical, not supplied through a realization premise. The
confidence coefficient is the paper's displayed 15/(256 sqrt 2).
-/

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace ThresholdHC.OracleLower
open ThresholdHC.Tier3 ThresholdHC.Tier5 ThresholdHC.Tier6 ThresholdHC.Confidence

def OracleRealizationStatement : Prop :=
  ∀ (R : Type) [MeasurableSpace R] (A : OracleEstimator R) (q : SignLaw),
    IsProbabilityMeasure (oracleLaw A q) ∧
    RealizesCreationPrefixes A.randomLaw (oracleLaw A q) Prod.fst Prod.snd A.policy
      (fun r i => A.gap r i) (fun r i => q.val (A.gap r i))

def SelectedSemanticsStatement : Prop :=
  ∀ (R : Type) [MeasurableSpace R] (A : SelectedEstimator R),
    (∀ r xs, A.request r xs = some none →
      (selectedOracle A).policy r xs = some (Encodable.encode xs) ∧
      (selectedOracle A).gap r (Encodable.encode xs) = A.newGap r xs ∧
      ∀ k, k < xs.length → (selectedOracle A).policy r (xs.take k) ≠ some (Encodable.encode xs)) ∧
    (∀ r xs j, A.request r xs = some (some j) →
      j < xs.length ∧ A.request r (xs.take j) = some none ∧
      (selectedOracle A).policy r xs = (selectedOracle A).policy r (xs.take j) ∧
      (selectedOracle A).gap r (Encodable.encode (xs.take j)) = A.newGap r (xs.take j))

def OracleRMSLowerStatement : Prop :=
  ∀ (R : Type) [MeasurableSpace R] (μ : Measure Gap) [IsProbabilityMeasure μ]
    (A : OracleEstimator R) (B : ℝ),
    1 ≤ B → OracleBudget A B →
    ENNReal.ofReal (modulus μ (1/Real.sqrt B)/64) ≤ oracleRisk μ A

def OracleConfidenceLowerStatement : Prop :=
  ∀ (R : Type) [MeasurableSpace R] (μ : Measure Gap) [IsProbabilityMeasure μ]
    (A : OracleEstimator R) (B δ r : ℝ),
    1 ≤ B → 0 < δ → δ ≤ 1/4 → 0 ≤ r →
    OracleBudget A B → OracleConfidence μ A r δ →
    (15/(256*Real.sqrt 2))*modulus μ (confidenceScale B δ) ≤ r

def RevealedLowerStatement : Prop :=
  ∀ (R : Type) [MeasurableSpace R] (μ : Measure Gap) [IsProbabilityMeasure μ]
    (A : RevealedEstimator R) (B : ℝ), 1 ≤ B → OracleBudget (revealedOracle μ A) B →
    ENNReal.ofReal (modulus μ (1/Real.sqrt B)/64) ≤ oracleRisk μ (revealedOracle μ A) ∧
    ∀ δ r : ℝ, 0 < δ → δ ≤ 1/4 → 0 ≤ r →
      OracleConfidence μ (revealedOracle μ A) r δ →
      (15/(256*Real.sqrt 2))*modulus μ (confidenceScale B δ) ≤ r

def SelectedLowerStatement : Prop :=
  ∀ (R : Type) [MeasurableSpace R] (μ : Measure Gap) [IsProbabilityMeasure μ]
    (A : SelectedEstimator R) (B : ℝ), 1 ≤ B → OracleBudget (selectedOracle A) B →
    ENNReal.ofReal (modulus μ (1/Real.sqrt B)/64) ≤ oracleRisk μ (selectedOracle A) ∧
    ∀ δ r : ℝ, 0 < δ → δ ≤ 1/4 → 0 ≤ r →
      OracleConfidence μ (selectedOracle A) r δ →
      (15/(256*Real.sqrt 2))*modulus μ (confidenceScale B δ) ≤ r

def OracleMinimaxLowerStatement : Prop :=
  ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] (B δ : ℝ),
    1 ≤ B → 0 < δ → δ ≤ 1/4 →
    ENNReal.ofReal (modulus μ (1/Real.sqrt B)/64) ≤ revealedMinimaxRisk μ B ∧
    ENNReal.ofReal (modulus μ (1/Real.sqrt B)/64) ≤ selectedMinimaxRisk μ B ∧
    ENNReal.ofReal ((15/(256*Real.sqrt 2))*modulus μ (confidenceScale B δ)) ≤
      revealedConfidenceRadius μ B δ ∧
    ENNReal.ofReal ((15/(256*Real.sqrt 2))*modulus μ (confidenceScale B δ)) ≤
      selectedConfidenceRadius μ B δ

def OracleNonvacuityStatement : Prop :=
  ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] (B δ : ℝ), 0 ≤ B → 0 ≤ δ →
    (∃ A : RevealedEstimator Unit, OracleBudget (revealedOracle μ A) B ∧
      oracleRisk μ (revealedOracle μ A) ≤ 1 ∧ OracleConfidence μ (revealedOracle μ A) 1 δ) ∧
    (∃ A : SelectedEstimator Unit, OracleBudget (selectedOracle A) B ∧
      oracleRisk μ (selectedOracle A) ≤ 1 ∧ OracleConfidence μ (selectedOracle A) 1 δ) ∧
    revealedMinimaxRisk μ B ≤ 1 ∧ selectedMinimaxRisk μ B ≤ 1 ∧
    revealedConfidenceRadius μ B δ ≤ 1 ∧ selectedConfidenceRadius μ B δ ≤ 1

end ThresholdHC.OracleLower
