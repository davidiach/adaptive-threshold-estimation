import ThresholdHC.CapIdentification.PrefixRepresentation
import ThresholdHC.CapIdentification.FullCapCertificate
import ThresholdHC.CapIdentification.MomentCoordinates

/-! A polynomial in the Bernoulli parameter is an actual full-depth count
output. Odd-moment recovery coefficients therefore become terminal arrays
of the original normalized stopping program. -/

noncomputable section
open MeasureTheory Polynomial Set
open scoped BigOperators

namespace ThresholdHC.CapIdentification
open ThresholdHC.Tier6 (Gap SignLaw)
open ThresholdHC.StoppingProgram

def topState (N : ℕ) (k : Fin (N+1)) : CountState N := ⟨⟨N,by omega⟩,k⟩

def liftTerminalOutput {N : ℕ} (y : Fin (N+1) → ℝ) (s : CountState N) : ℝ :=
  y ⟨s.2.val,by have hk := s.2.isLt; have hn := s.1.isLt; omega⟩

theorem sum_terminal {N : ℕ} (f : CountState N → ℝ) :
    (∑ s : CountState N, if s.1.val = N then f s else 0) = ∑ k : Fin (N+1), f (topState N k) := by
  classical
  rw [Fintype.sum_sigma]
  rw [Finset.sum_eq_single (⟨N,by omega⟩ : Fin (N+1))]
  · simp only [ite_true,topState]
  · intro n _ hn
    have he : n.val ≠ N := by intro h; apply hn; exact Fin.ext h
    simp only [he,ite_false,Finset.sum_const_zero]
  · intro h
    exact (h (Finset.mem_univ _)).elim

theorem countMean_terminal {N : ℕ} (μ : Measure Gap) (q : SignLaw) (y : Fin (N+1) → ℝ) :
    countMean μ q (terminalArray (liftTerminalOutput y)) =
      ∑ k : Fin (N+1), countCoefficient μ q (topState N k)*y k := by
  simp only [countMean,terminalArray,mul_ite,mul_zero]
  rw [sum_terminal]
  rfl

def nullSignLaw : SignLaw := ⟨fun _ => 0,measurable_const,fun _ => ⟨le_rfl,by norm_num⟩⟩

def nullPolynomialMean (μ : Measure Gap) [IsFiniteMeasure μ] : ℝ[X] →ₗ[ℝ] ℝ :=
  weightedPolynomialIntegral μ (fun _ => 1) (fun d => 1/2-(d:ℝ)) measurable_const (by fun_prop)
    (fun _ => by norm_num) (fun d => ⟨by linarith [d.property.2],by linarith [d.property.1]⟩)

def populationPolynomialMean (μ : Measure Gap) [IsFiniteMeasure μ] (q : SignLaw) : ℝ[X] →ₗ[ℝ] ℝ :=
  nullPolynomialMean μ+signContrast μ q nullSignLaw

theorem populationPolynomialMean_prefix (μ : Measure Gap) [IsFiniteMeasure μ]
    (q : SignLaw) (n k : ℕ) :
    populationPolynomialMean μ q (prefixPolynomial n k) =
      ∫ d, q.val d*prefixLikelihood true n k d+(1-q.val d)*prefixLikelihood false n k d ∂μ := by
  change nullPolynomialMean μ (prefixPolynomial n k)+signContrast μ q nullSignLaw (prefixPolynomial n k) = _
  rw [signContrast_apply]
  simp only [nullPolynomialMean,weightedPolynomialIntegral,LinearMap.coe_mk,AddHom.coe_mk,
    nullSignLaw,sub_zero,one_mul,prefixPolynomial_eval_minus,prefixPolynomial_eval_plus]
  have hi0 := integrable_prefixLikelihood μ false n k
  have hi1 := integrable_weighted_prefix μ q true n k
  have hi2 := integrable_weighted_prefix μ q false n k
  have he : (fun d => q.val d*prefixLikelihood true n k d+(1-q.val d)*prefixLikelihood false n k d) =
      (fun d => q.val d*prefixLikelihood true n k d+(prefixLikelihood false n k d-q.val d*prefixLikelihood false n k d)) := by
    funext d
    ring
  have hAdd := integral_add hi1 (hi0.sub hi2)
  simp only [Pi.sub_apply] at hAdd
  rw [he,hAdd,integral_sub hi0 hi2]
  ring

theorem countCoefficient_polynomial {N : ℕ} (μ : Measure Gap) [IsFiniteMeasure μ]
    (q : SignLaw) (s : CountState N) :
    countCoefficient μ q s = (s.1.val.choose s.2.val:ℝ)*
      populationPolynomialMean μ q (prefixPolynomial s.1.val s.2.val) := by
  rw [populationPolynomialMean_prefix]
  rfl

theorem terminal_polynomial_representation (μ : Measure Gap) [IsFiniteMeasure μ]
    (N : ℕ) (P : ℝ[X]) (hP : P.natDegree ≤ N) :
    ∃ y : CountState N → ℝ, ∀ q : SignLaw,
      countMean μ q (terminalArray y) = populationPolynomialMean μ q P := by
  obtain ⟨y,hy⟩ := exists_count_coefficients N P hP
  refine ⟨liftTerminalOutput y,?_⟩
  intro q
  rw [countMean_terminal,hy]
  simp only [map_sum,map_smul,smul_eq_mul,countCoefficient_polynomial,topState]
  apply Finset.sum_congr rfl
  intro k _
  ring

theorem populationPolynomialMean_odd (μ : Measure Gap) [IsFiniteMeasure μ] (q : SignLaw)
    (N : ℕ) (w : Fin ((N+1)/2) → ℝ) :
    populationPolynomialMean μ q (oddMomentRepresentative N w) =
      nullPolynomialMean μ (oddMomentRepresentative N w)+
        ∑ j, w j*momentCoordinates μ q ((N+1)/2) (some j) := by
  change nullPolynomialMean μ (oddMomentRepresentative N w)+
    signContrast μ q nullSignLaw (oddMomentRepresentative N w) = _
  congr 1
  simp only [oddMomentRepresentative,map_sum,map_smul,smul_eq_mul,signContrast_odd,
    nullSignLaw,sub_zero,momentCoordinates_some]
  apply Finset.sum_congr rfl
  intro j _
  ring

end ThresholdHC.CapIdentification
