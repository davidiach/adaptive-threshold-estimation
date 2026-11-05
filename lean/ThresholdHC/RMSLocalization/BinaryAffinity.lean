import ThresholdHC.CriticalEntropy.AffinityTesting

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace ThresholdHC.RMSLocalization
open ThresholdHC.CriticalEntropy

theorem bool_affinity_quarter_errors (P Q : Measure Bool)
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (hp : P.real {true} ≤ 1/4) (hq : Q.real {false} ≤ 1/4) :
    (hellingerAffinity P Q).toReal ≤ 7/8 := by
  have hs : ({false} : Set Bool)ᶜ = {true} := by ext b; cases b <;> simp
  have hP : P.real {false}+P.real {true} = 1 := by
    have h := measureReal_add_measureReal_compl (μ := P) (measurableSet_singleton false)
    rwa [hs,probReal_univ] at h
  have hQ : Q.real {false}+Q.real {true} = 1 := by
    have h := measureReal_add_measureReal_compl (μ := Q) (measurableSet_singleton false)
    rwa [hs,probReal_univ] at h
  let x : Fin 2 → ℝ := ![P.real {false},Q.real {true}]
  let y : Fin 2 → ℝ := ![Q.real {false},P.real {true}]
  have hx (i : Fin 2) : 0 ≤ x i := by fin_cases i <;> exact measureReal_nonneg
  have hy (i : Fin 2) : 0 ≤ y i := by fin_cases i <;> exact measureReal_nonneg
  have hc : Real.sqrt (P.real {false})*Real.sqrt (Q.real {false})+
      Real.sqrt (Q.real {true})*Real.sqrt (P.real {true}) ≤
      Real.sqrt (P.real {false}+Q.real {true})*Real.sqrt (Q.real {false}+P.real {true}) := by
    have h := Real.sum_sqrt_mul_sqrt_le Finset.univ (fun i => hx i) (fun i => hy i)
    simpa [Fin.sum_univ_two,x,y] using h
  have he : 0 ≤ (1/2-(P.real {true}+Q.real {false}))*
      (3/2-(P.real {true}+Q.real {false})) := mul_nonneg (by linarith) (by linarith)
  calc
    _ = Real.sqrt (P.real {false})*Real.sqrt (Q.real {false})+
        Real.sqrt (Q.real {true})*Real.sqrt (P.real {true}) := by
      rw [hellingerAffinity_finite_real,realFiniteAffinity,Fintype.sum_bool,
        Real.sqrt_mul (show 0 ≤ P.real {true} from measureReal_nonneg),
        Real.sqrt_mul (show 0 ≤ P.real {false} from measureReal_nonneg)]
      ring
    _ ≤ _ := hc
    _ = Real.sqrt ((P.real {false}+Q.real {true})*(Q.real {false}+P.real {true})) :=
      (Real.sqrt_mul (add_nonneg measureReal_nonneg measureReal_nonneg) _).symm
    _ ≤ 7/8 := by
      apply Real.sqrt_le_iff.mpr
      refine ⟨by norm_num,?_⟩
      rw [show P.real {false} = 1-P.real {true} by linarith,
        show Q.real {true} = 1-Q.real {false} by linarith]
      nlinarith only [he]

end ThresholdHC.RMSLocalization
