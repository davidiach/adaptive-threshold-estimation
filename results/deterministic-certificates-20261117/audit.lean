import ThresholdHC.DeterministicCertificates.Entropy
open ThresholdHC.DeterministicCertificates
example {input output : Interval} {x : ℝ}
    (h : sqrtCheck input output = true) (hi : Contains input x) :
    (output.lower:ℝ) ≤ Real.sqrt x ∧ Real.sqrt x ≤ (output.upper:ℝ) := sqrtCheck_sound h hi

example {x tolerance : ℚ} {output : Interval}
    (h : sqrtPrecisionCheck x tolerance output = true) (hx : 0 ≤ x) :
    (output.upper-output.lower:ℝ) ≤ (tolerance:ℝ)*min 1 (Real.sqrt (x:ℝ)) :=
  sqrtPrecisionCheck_sound h hx

example {x : ℚ} (hx : 1 ≤ x) (n : ℕ) :
    ((unitLog x n).lower:ℝ) ≤ Real.log (x:ℝ) ∧
      Real.log (x:ℝ) ≤ ((unitLog x n).upper:ℝ) := unitLog_sound hx n

example {input output : Interval} {lower upper : LogWitness} {x : ℝ}
    (h : logCheck input output lower upper = true) (hi : Contains input x) :
    (output.lower:ℝ) ≤ Real.log x ∧ Real.log x ≤ (output.upper:ℝ) := logCheck_sound h hi

example (e : Expr) (c : Evidence) (h : check e c = true) :
    (c.bounds.lower:ℝ) ≤ e.eval ∧ e.eval ≤ (c.bounds.upper:ℝ) := check_sound e c h

example {e : Expr} {claimed : Interval} {c : Evidence}
    (h : accepted e claimed c = true) :
    (claimed.lower:ℝ) ≤ e.eval ∧ e.eval ≤ (claimed.upper:ℝ) := accepted_sound h

example {n : ℕ} (a : Fin n → ℚ) (ha : ∀ i, 0 ≤ a i) :
    (entropyExpr a).eval =
      ThresholdHC.EntropyTailQuantile.costEntropy (fun i => (a i:ℝ)) := entropyExpr_eval a ha

example {n : ℕ} (a : Fin n → ℚ) (ha : ∀ i, 0 ≤ a i)
    {claimed : Interval} {c : Evidence} (h : accepted (entropyExpr a) claimed c = true) :
    (claimed.lower:ℝ) ≤ ThresholdHC.EntropyTailQuantile.costEntropy (fun i => (a i:ℝ)) ∧
      ThresholdHC.EntropyTailQuantile.costEntropy (fun i => (a i:ℝ)) ≤ (claimed.upper:ℝ) :=
  entropy_accepted_sound a ha h
#print axioms ThresholdHC.DeterministicCertificates.Contains
#print axioms ThresholdHC.DeterministicCertificates.Evidence
#print axioms ThresholdHC.DeterministicCertificates.Evidence.bounds
#print axioms ThresholdHC.DeterministicCertificates.Expr
#print axioms ThresholdHC.DeterministicCertificates.Expr.eval
#print axioms ThresholdHC.DeterministicCertificates.Interval
#print axioms ThresholdHC.DeterministicCertificates.LogWitness
#print axioms ThresholdHC.DeterministicCertificates.accepted
#print axioms ThresholdHC.DeterministicCertificates.accepted_sound
#print axioms ThresholdHC.DeterministicCertificates.add
#print axioms ThresholdHC.DeterministicCertificates.add_sound
#print axioms ThresholdHC.DeterministicCertificates.check
#print axioms ThresholdHC.DeterministicCertificates.check_sound
#print axioms ThresholdHC.DeterministicCertificates.encloses
#print axioms ThresholdHC.DeterministicCertificates.encloses_sound
#print axioms ThresholdHC.DeterministicCertificates.entropyExpr
#print axioms ThresholdHC.DeterministicCertificates.entropyExpr_eval
#print axioms ThresholdHC.DeterministicCertificates.entropy_accepted_sound
#print axioms ThresholdHC.DeterministicCertificates.imax
#print axioms ThresholdHC.DeterministicCertificates.imin
#print axioms ThresholdHC.DeterministicCertificates.logBounds
#print axioms ThresholdHC.DeterministicCertificates.logBounds_sound
#print axioms ThresholdHC.DeterministicCertificates.logCheck
#print axioms ThresholdHC.DeterministicCertificates.logCheck_sound
#print axioms ThresholdHC.DeterministicCertificates.logRange
#print axioms ThresholdHC.DeterministicCertificates.max_sound
#print axioms ThresholdHC.DeterministicCertificates.min_sound
#print axioms ThresholdHC.DeterministicCertificates.point
#print axioms ThresholdHC.DeterministicCertificates.point_sound
#print axioms ThresholdHC.DeterministicCertificates.scale
#print axioms ThresholdHC.DeterministicCertificates.scale_sound
#print axioms ThresholdHC.DeterministicCertificates.sqrtCheck
#print axioms ThresholdHC.DeterministicCertificates.sqrtCheck_sound
#print axioms ThresholdHC.DeterministicCertificates.sqrtPrecisionCheck
#print axioms ThresholdHC.DeterministicCertificates.sqrtPrecisionCheck_sound
#print axioms ThresholdHC.DeterministicCertificates.sumExpr
#print axioms ThresholdHC.DeterministicCertificates.sumExpr_eval
#print axioms ThresholdHC.DeterministicCertificates.unitLog
#print axioms ThresholdHC.DeterministicCertificates.unitLog_sound
