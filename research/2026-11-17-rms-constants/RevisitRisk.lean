import RevisitExperiment
import RevisitCertificate

noncomputable section
namespace ThresholdHC.SharpRMS.Revisit
open LargeBudget IntPoly

private theorem scale_powers (a x y : ℝ) (n m : ℕ) :
    (a*x)^n*(a*y)^m = a^(n+m)*(x^n*y^m) := by rw [pow_add,mul_pow,mul_pow]; ring

private def denom (p : ℝ) : Option Bool → ℝ
  | none => 1
  | some true => headProb p
  | some false => 1-headProb p

private def units : Option Bool → ℝ
  | none => 10
  | some _ => 100

private theorem joint (j : ℕ) (p : ℝ) (hp : p∈Set.Icc 0 1) :
    let r := nextHead p (mode j)
    let c := units (mode j)*denom p (mode j)
    value (factors j).1 p=c*r ∧ value (factors j).2.1 p=c*(1-r) := by
  have b0 : headProb p≠0 := by unfold headProb; linarith [hp.1]
  have c0 : 1-headProb p≠0 := by unfold headProb; linarith [hp.2]
  cases h : mode j with
  | none =>
    change value (factors j).1 p=_ ∧ value (factors j).2.1 p=_
    simp only [factors,h]
    change value [3,4] p=_ ∧ value [7,-4] p=_
    constructor <;> norm_num [value,nextHead,denom,units,headProb] <;> ring
  | some b =>
    cases b <;> simp [factors,h,units,denom,nextHead,value]
    all_goals constructor
    all_goals field_simp [b0,c0]
    all_goals try unfold headProb
    all_goals ring

private theorem word (j k : ℕ) (hj : j≤20) (hk : k≤5) (p : ℝ) (hp : p∈Set.Icc 0 1) :
    let (a,b,h,t) := factors j
    let r := nextHead p (mode j)
    (10*headProb p)^h*(10*(1-headProb p))^t*(value a p)^k*(value b p)^(5-k) =
    10^25*(headProb p)^j*(1-headProb p)^(20-j)*r^k*(1-r)^(5-k) := by
  change (10*headProb p)^(factors j).2.2.1*(10*(1-headProb p))^(factors j).2.2.2*
    (value (factors j).1 p)^k*(value (factors j).2.1 p)^(5-k) = _
  obtain ⟨u,v⟩ := joint j p hp
  rw [u,v,scale_powers, mul_assoc (_*_) (_^k),scale_powers,show k+(5-k)=5 by omega,mul_pow]
  let b := headProb p
  let c := 1-headProb p
  have unit (j : ℕ) (hj : j≤20) :
      (10:ℝ)^((factors j).2.2.1+(factors j).2.2.2)*
        (b^(factors j).2.2.1*c^(factors j).2.2.2)*(units (mode j)^5*denom p (mode j)^5)
      = 10^25*b^j*c^(20-j) := by
    by_cases H : 5≤j ∧ j≤9
    · simp only [factors,mode,ite_eq_left H,units,denom]
      change (10:ℝ)^(j-5+(20-j))*(b^(j-5)*c^(20-j))*(100^5*b^5)=_
      rw [show j-5+(20-j)=15 by omega,show b^j=b^(j-5)*b^5 by rw [←pow_add]; congr 1; omega]
      ring
    by_cases T : 11≤j ∧ j≤15
    · simp only [factors,mode,ite_eq_right H,ite_eq_left T,units,denom]
      change (10:ℝ)^(j+(20-j-5))*(b^j*c^(20-j-5))*(100^5*c^5)=_
      rw [show j+(20-j-5)=15 by omega,show c^(20-j)=c^(20-j-5)*c^5 by rw [←pow_add]; congr 1; omega]
      ring
    · simp only [factors,mode,ite_eq_right H,ite_eq_right T,units,denom]
      rw [show j+(20-j)=20 by omega]
      change (10:ℝ)^20*(b^j*c^(20-j))*(10^5*1^5)=_
      ring
  linear_combination (nextHead p (mode j))^k*(1-nextHead p (mode j))^(5-k) * unit j hj

private theorem raw (p : ℝ) (hp : p∈Set.Icc 0 1) :
    value riskCoeffs p = (10:ℝ)^35*binomialAverage (headProb p)
      (finish (fun j k => (estimate j k-p)^2) p) 20 0 := by
  rw [riskCoeffs,value_sumTo,binomial_sum,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  have jle : j≤20 := by have := Finset.mem_range.mp hj; omega
  simp only [value_scale,value_mul,value_power,value_sumTo,Int.cast_natCast,zero_add,finish,binomial_sum]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  have kle : k≤5 := by have := Finset.mem_range.mp hk; omega
  have w := word j k jle kle p hp
  change (10*headProb p)^(factors j).2.2.1*(10*(1-headProb p))^(factors j).2.2.2*
    (value (factors j).1 p)^k*(value (factors j).2.1 p)^(5-k) = _ at w
  have e : value [↑(entry j k),-100000] p=100000*(estimate j k-p) := by simp [estimate,value]; ring
  have a : value [3,4] p=10*headProb p := by norm_num [headProb,value]; ring
  have b : value [7,-4] p=10*(1-headProb p) := by norm_num [headProb,value]; ring
  change ((20:ℕ).choose j:ℝ)*((value [3,4] p^(factors j).2.2.1*value [7,-4] p^(factors j).2.2.2)*
    (↑((5:ℕ).choose k)*(value (factors j).1 p^k*value (factors j).2.1 p^(5-k)*value [↑(entry j k),-100000] p^2)))=_
  rw [e,a,b]
  linear_combination ((20:ℕ).choose j:ℝ)*((5:ℕ).choose k:ℝ)*(100000*(estimate j k-p))^2*w

theorem adaptive_binomial_risk (p : ℝ) (hp : p∈Set.Icc 0 1) :
    binomialAverage (headProb p) (finish (fun j k => (estimate j k-p)^2) p) 20 0 ≤ bound^2 := by
  have h := certificate p hp
  rw [raw p hp] at h
  exact (mul_le_mul_iff_right₀ (by norm_num : (0:ℝ)<10^35)).mp h

end ThresholdHC.SharpRMS.Revisit
