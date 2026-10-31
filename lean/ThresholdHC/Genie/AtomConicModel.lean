import ThresholdHC.Genie.FinitePriors
import ThresholdHC.Genie.FiniteConicValue

/-! A finite SOCP model: atom endpoint/work perspectives, variance values,
latent epigraphs, triangular Bellman values, and a squared-scale epigraph.
Every constraint is linear or a rotated quadratic cone. -/

noncomputable section
open MeasureTheory
open scoped ENNReal BigOperators
namespace ThresholdHC.Genie
open ThresholdHC.Tier6 ThresholdHC.RareAboveTwo ThresholdHC.StoppingProgram
variable {I : Type*} [Fintype I]

structure AtomConicPoint (I : Type*) (N : ℕ) where
  scale : ℝ
  price : ℝ
  scaleSquared : ℝ
  low : I → ℝ
  high : I → ℝ
  variance : I → ℝ
  work : I → ℝ
  revealPlus : I → ℝ
  revealMinus : I → ℝ
  bellman : CountState N → ℝ

def AtomBox (w : I → ℝ) (ρ c : ℝ) (u : I → ℝ) : Prop :=
  (∀ i, 0 ≤ u i ∧ u i ≤ c) ∧ ∑ i, w i*u i ≤ c*ρ

def AtomConicFeasible {N : ℕ} (w : I → ℝ) (d : I → Gap) (ρ : ℝ) (v : AtomConicPoint I N) : Prop :=
  0 ≤ v.scale ∧ 0 ≤ v.price ∧ v.scale^2 ≤ v.scaleSquared ∧
  AtomBox w ρ v.scale v.low ∧ AtomBox w ρ v.scale v.high ∧
  AtomBox w ρ 1 v.variance ∧ AtomBox w ρ v.price v.work ∧
  (∀ i, 0 ≤ v.revealPlus i ∧ 0 ≤ v.revealMinus i ∧
    (v.high i-v.low i)^2 ≤ v.variance i*v.revealPlus i ∧
    (v.high i-v.low i)^2 ≤ (1-v.variance i)*v.revealMinus i) ∧
  (∀ n k, 1 ≤ n → n ≤ N → k ≤ n → 0 ≤ arrayAt v.bellman n k ∧
    (if n = N then finiteRevealBound w d v.revealPlus v.revealMinus n k/4 ≤ arrayAt v.bellman n k
     else (atomPrefixCoefficient w d v.scale v.high n k-atomPrefixCoefficient w d v.scale v.low n k)^2 ≤
       4*atomPrefixCoefficient w d 1 v.variance n k*arrayAt v.bellman n k)) ∧
  (∀ n k, 1 ≤ n → n < N → k ≤ n →
    arrayAt v.bellman (n+1) k+arrayAt v.bellman (n+1) (k+1)-atomPrefixCoefficient w d v.price v.work n k ≤
      arrayAt v.bellman n k) ∧
  arrayAt v.bellman 1 0+arrayAt v.bellman 1 1-v.price ≤ 0

def atomConicObjective {N : ℕ} (w : I → ℝ) (B : ℝ) (v : AtomConicPoint I N) : ℝ :=
  (∑ i, w i*(v.high i-v.low i))-v.scaleSquared-v.price*B

def atomConicValue (N : ℕ) (w : I → ℝ) (d : I → Gap) (ρ B : ℝ) : ℝ≥0∞ :=
  ⨆ (v : AtomConicPoint I N) (_ : AtomConicFeasible w d ρ v), ENNReal.ofReal (atomConicObjective w B v)

theorem atomBox_of_prior (μ : Measure Gap) [IsProbabilityMeasure μ]
    (w : I → ℝ) (d : I → Gap) (hw : ∀ i, 0 ≤ w i)
    (hμ : μ = ∑ i, ENNReal.ofReal (w i) • Measure.dirac (d i))
    (ρ c : ℝ) (hc : 0 ≤ c) (q : SignLaw) (hq : RarePrior μ ρ q) :
    AtomBox w ρ c (fun i => c*q.val (d i)) := by
  constructor
  · intro i
    exact ⟨mul_nonneg hc (q.property.2 (d i)).1,by nlinarith [(q.property.2 (d i)).2]⟩
  · rw [←finite_scaled_mean μ w d hw hμ q c _ (fun _ => rfl)]
    exact mul_le_mul_of_nonneg_left hq hc

def atomPointOfPriors {N : ℕ} (d : I → Gap) (Q : FourPriors) (α η : ℝ)
    (X : CountState N → ℝ) (rp rm : I → ℝ) : AtomConicPoint I N where
  scale := α
  price := η
  scaleSquared := α^2
  low := fun i => α*Q.low.val (d i)
  high := fun i => α*Q.high.val (d i)
  variance := fun i => Q.variance.val (d i)
  work := fun i => η*Q.work.val (d i)
  revealPlus := rp
  revealMinus := rm
  bellman := X

theorem atomConicFeasible_of_priors {N : ℕ} (μ : Measure Gap) [IsProbabilityMeasure μ]
    (w : I → ℝ) (d : I → Gap) (hw : ∀ i, 0 ≤ w i)
    (hμ : μ = ∑ i, ENNReal.ofReal (w i) • Measure.dirac (d i))
    (ρ : ℝ) (Q : FourPriors) (hQ : Admissible μ ρ Q)
    (α η : ℝ) (hα : 0 ≤ α) (hη : 0 ≤ η) (X : CountState N → ℝ) (rp rm : I → ℝ)
    (hcone : FiniteGenieCones μ w d Q α η X rp rm) :
    AtomConicFeasible w d ρ (atomPointOfPriors d Q α η X rp rm) := by
  have hco (q : SignLaw) (c : ℝ) (n k : ℕ) := finite_scaled_prefixCoefficient μ w d hw hμ q c
    (fun i => c*q.val (d i)) (fun _ => rfl) n k
  refine ⟨hα,hη,le_rfl,atomBox_of_prior μ w d hw hμ ρ α hα Q.low hQ.1,
    atomBox_of_prior μ w d hw hμ ρ α hα Q.high hQ.2.1,?_,
    atomBox_of_prior μ w d hw hμ ρ η hη Q.work hQ.2.2.2,?_,?_,?_,hcone.2.2.2⟩
  · simpa only [one_mul,atomPointOfPriors] using atomBox_of_prior μ w d hw hμ ρ 1 (by norm_num) Q.variance hQ.2.2.1
  · intro i
    simpa only [atomPointOfPriors,←mul_sub] using hcone.1 i
  · intro n k hn hnN hk
    have hs := hcone.2.1 n k hn hnN hk
    refine ⟨hs.1,?_⟩
    change (if n = N then finiteRevealBound w d rp rm n k/4 ≤ arrayAt X n k else _)
    by_cases he : n = N
    · simpa only [he,ite_true] using hs.2
    · simp only [he,ite_false,atomPointOfPriors] at *
      have hv : atomPrefixCoefficient w d 1 (fun i => Q.variance.val (d i)) n k = prefixCoefficient μ Q.variance n k := by
        simpa only [one_mul] using (hco Q.variance 1 n k).symm
      rw [←hco Q.high α n k,←hco Q.low α n k,hv,←mul_sub]
      exact hs.2
  · intro n k hn hnN hk
    change arrayAt X (n+1) k+arrayAt X (n+1) (k+1)-atomPrefixCoefficient w d η (fun i => η*Q.work.val (d i)) n k ≤ arrayAt X n k
    rw [←hco Q.work η n k]
    exact hcone.2.2.1 n k hn hnN hk

theorem atomConicObjective_of_priors {N : ℕ} (μ : Measure Gap) (w : I → ℝ) (d : I → Gap)
    (hw : ∀ i, 0 ≤ w i) (hμ : μ = ∑ i, ENNReal.ofReal (w i) • Measure.dirac (d i))
    (B : ℝ) (Q : FourPriors) (α η : ℝ) (X : CountState N → ℝ) (rp rm : I → ℝ) :
    atomConicObjective w B (atomPointOfPriors d Q α η X rp rm) =
      α*(signMean μ Q.high.val-signMean μ Q.low.val)-α^2-η*B := by
  have hh := finite_scaled_mean μ w d hw hμ Q.high α _ (fun _ => rfl)
  have hl := finite_scaled_mean μ w d hw hμ Q.low α _ (fun _ => rfl)
  unfold atomConicObjective atomPointOfPriors
  simp only
  simp_rw [mul_sub]
  rw [Finset.sum_sub_distrib,←hh,←hl]

def atomConicVariableCount (I : Type*) [Fintype I] (N : ℕ) : ℕ :=
  3+6*Fintype.card I+Fintype.card (CountState N)

theorem countState_card_le_square (N : ℕ) : Fintype.card (CountState N) ≤ (N+1)^2 := by
  simp only [CountState,Fintype.card_sigma,Fintype.card_fin]
  calc
    (∑ n : Fin (N+1), (n.val+1)) ≤ (∑ _n : Fin (N+1), (N+1)) :=
      Finset.sum_le_sum (fun n _ => by have hn := n.isLt; omega)
    _ = _ := by simp [pow_two]

theorem atomConicVariableCount_bound (I : Type*) [Fintype I] (N : ℕ) :
    atomConicVariableCount I N ≤ 3+6*Fintype.card I+(N+1)^2 :=
  Nat.add_le_add_left (countState_card_le_square N) _

end ThresholdHC.Genie
