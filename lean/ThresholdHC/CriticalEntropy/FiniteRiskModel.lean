import ThresholdHC.CriticalEntropy.FiniteGeometryModel

noncomputable section
open Set
namespace ThresholdHC.CriticalEntropy

def finitePartition {I : Type} [Fintype I] (p u : I → ℝ) : ℝ :=
  ∑ i, p i*Real.exp (u i)

def finitePartitionLinear {I : Type} [Fintype I] (u : I → ℝ) : (I → ℝ) →ₗ[ℝ] ℝ where
  toFun := fun p => finitePartition p u
  map_add' := by intros; simp [finitePartition,add_mul,Finset.sum_add_distrib]
  map_smul' := by intros; simp [finitePartition,Finset.mul_sum,mul_assoc]

def finiteRepeatedObjective {I : Type} [Fintype I]
    (p q : I → ℝ) (d : ℝ) (n : ℕ) (u : I → ℝ) (a : ℝ) : ℝ :=
  d+a*((n : ℝ)*Real.log (finitePartition p (fun i => -u i/a))+
    (n : ℝ)*Real.log (finitePartition q (fun i => u i/a))+2*Real.log 2)

end ThresholdHC.CriticalEntropy
