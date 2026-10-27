import ThresholdHC.Tier3.RandomizedBase
import ThresholdHC.Tier3.IntegralLogSum

/-!
Information bounds for policies with an arbitrary common random seed.

At each fixed horizon, policy actions and test values factor through finite
codes. This gives measurability and integrability without any information-bound
assumption. Integral log-sum proves marginal contraction and data processing
for tests that may inspect both the seed and the transcript. Global test error
bounds are imposed only after averaging over the seed.
-/

noncomputable section
namespace ThresholdHC.Tier3
open MeasureTheory Real
open ThresholdHC.Proofs

local instance (m : ℕ) : MeasurableSpace (Option (Fin m)) := ⊤

theorem integrable_kl_term {U : Type} [MeasurableSpace U] {m n : ℕ}
    (μ : Measure U) [IsFiniteMeasure μ] (pol : U → List Bool → Option (Fin m))
    (hp : MeasurablePolicy pol) (d q r : Fin m → ℝ) (ω : Prefix n) :
    Integrable (fun u => transcriptLaw (pol u) d q ω *
      Real.log (transcriptLaw (pol u) d q ω / transcriptLaw (pol u) d r ω)) μ :=
  integrable_policy_function μ pol hp (fun c => codeLaw c d q ω *
    Real.log (codeLaw c d q ω / codeLaw c d r ω))

theorem randomized_marginal_kl_le {U : Type} [MeasurableSpace U] {m n : ℕ}
    (μ : Measure U) [IsProbabilityMeasure μ] (pol : U → List Bool → Option (Fin m))
    (hp : MeasurablePolicy pol) (d q r : Fin m → ℝ)
    (hd : ∀ i, 0 ≤ d i ∧ d i ≤ 1/2)
    (hq : ∀ i, 0 < q i ∧ q i < 1) (hr : ∀ i, 0 < r i ∧ r i < 1) :
    klFT (randomizedLaw (n:=n) μ pol d q) (randomizedLaw (n:=n) μ pol d r) ≤
      ∫ u, klFT (transcriptLaw (n:=n) (pol u) d q) (transcriptLaw (pol u) d r) ∂μ := by
  have hP u := (transcript_law_total m n (pol u) d q hd (fun i => ⟨(hq i).1.le,(hq i).2.le⟩)).1
  have hQ u := (transcript_law_total m n (pol u) d r hd (fun i => ⟨(hr i).1.le,(hr i).2.le⟩)).1
  unfold klFT randomizedLaw
  calc
    _ ≤ ∑ ω : Prefix n, ∫ u, transcriptLaw (pol u) d q ω *
        Real.log (transcriptLaw (pol u) d q ω / transcriptLaw (pol u) d r ω) ∂μ := by
      apply Finset.sum_le_sum
      intro ω _
      exact integral_log_sum μ _ _ (fun u => hP u ω) (fun u => hQ u ω)
        (integrable_transcriptLaw μ pol hp d q ω) (integrable_transcriptLaw μ pol hp d r ω)
        (fun u => (transcriptLaw_support (pol u) d q r hd hq hr ω).mpr)
        (integrable_kl_term μ pol hp d q r ω)
    _ = _ := (integral_finsetSum _ (fun ω _ => integrable_kl_term μ pol hp d q r ω)).symm

theorem randomized_marginal_kl_bound : RandomizedMarginalKLStatement := by
  intro U _ μ _ m n pol d η h hp hh hd hη hdη
  have hd0 i : 0 ≤ d i ∧ d i ≤ 1/2 := ⟨(hd i).1.le,(hd i).2⟩
  have hq i : 0 < (1/2:ℝ)+η i ∧ (1/2:ℝ)+η i < 1 := by constructor <;> linarith [(hη i).1,(hη i).2]
  have hr i : 0 < (1/2:ℝ)-η i ∧ (1/2:ℝ)-η i < 1 := by constructor <;> linarith [(hη i).1,(hη i).2]
  exact (randomized_marginal_kl_le (n:=n) μ pol hp d _ _ hd0 hq hr).trans
    (randomized_information_bound U μ m n pol d η h hp hh hd hη hdη)

def testCode {U : Type} {n : ℕ} (A : U → Finset (Prefix n)) (u : U) : Prefix n → Bool :=
  fun ω => if ω ∈ A u then true else false

theorem measurable_testCode {U : Type} [MeasurableSpace U] {n : ℕ}
    (A : U → Finset (Prefix n)) (hA : MeasurableTest A) : Measurable (testCode A) := by
  apply Measurable.of_eval
  intro ω
  exact Measurable.ite (hA ω) measurable_const measurable_const

def codeAcceptance {m n : ℕ} (c : PolicyCode m n) (a : Prefix n → Bool)
    (d q : Fin m → ℝ) : ℝ :=
  ∑ ω, if a ω then codeLaw c d q ω else 0

theorem acceptance_eq_code {U : Type} {m n : ℕ}
    (pol : U → List Bool → Option (Fin m)) (A : U → Finset (Prefix n))
    (d q : Fin m → ℝ) (u : U) :
    (∑ ω ∈ A u, transcriptLaw (pol u) d q ω) =
      codeAcceptance (policyCode pol u) (testCode A u) d q := by
  simp [codeAcceptance, testCode, ← transcriptLaw_eq_codeLaw]

theorem integrable_test_function {U : Type} [MeasurableSpace U] {m n : ℕ}
    (μ : Measure U) [IsFiniteMeasure μ] (pol : U → List Bool → Option (Fin m))
    (hp : MeasurablePolicy pol) (A : U → Finset (Prefix n)) (hA : MeasurableTest A)
    (F : PolicyCode m n × (Prefix n → Bool) → ℝ) :
    Integrable (fun u => F (policyCode pol u, testCode A u)) μ :=
  integrable_finite_comp μ _ ((measurable_policyCode pol hp).prodMk (measurable_testCode A hA)) F

theorem integrable_acceptance {U : Type} [MeasurableSpace U] {m n : ℕ}
    (μ : Measure U) [IsFiniteMeasure μ] (pol : U → List Bool → Option (Fin m))
    (hp : MeasurablePolicy pol) (A : U → Finset (Prefix n)) (hA : MeasurableTest A)
    (d q : Fin m → ℝ) : Integrable (fun u => ∑ ω ∈ A u, transcriptLaw (pol u) d q ω) μ := by
  simp_rw [acceptance_eq_code pol A d q]
  exact integrable_test_function μ pol hp A hA (fun z => codeAcceptance z.1 z.2 d q)

theorem integrable_acceptance_function {U : Type} [MeasurableSpace U] {m n : ℕ}
    (μ : Measure U) [IsFiniteMeasure μ] (pol : U → List Bool → Option (Fin m))
    (hp : MeasurablePolicy pol) (A : U → Finset (Prefix n)) (hA : MeasurableTest A)
    (d q r : Fin m → ℝ) (F : ℝ → ℝ → ℝ) :
    Integrable (fun u => F (∑ ω ∈ A u, transcriptLaw (pol u) d q ω)
      (∑ ω ∈ A u, transcriptLaw (pol u) d r ω)) μ := by
  simp_rw [acceptance_eq_code pol A d q, acceptance_eq_code pol A d r]
  exact integrable_test_function μ pol hp A hA
    (fun z => F (codeAcceptance z.1 z.2 d q) (codeAcceptance z.1 z.2 d r))

theorem sum_support {B : Type} [Fintype B] (P Q : B → ℝ) (A : Finset B)
    (hQ : ∀ x, 0 ≤ Q x) (hPQ : ∀ x, Q x = 0 → P x = 0)
    (hzero : ∑ x ∈ A, Q x = 0) : ∑ x ∈ A, P x = 0 := by
  have hz := (Finset.sum_eq_zero_iff_of_nonneg (fun x _ => hQ x)).mp hzero
  exact Finset.sum_eq_zero (fun x hx => hPQ x (hz x hx))

theorem randomized_test_data_processing {U : Type} [MeasurableSpace U] {m n : ℕ}
    (μ : Measure U) [IsProbabilityMeasure μ] (pol : U → List Bool → Option (Fin m))
    (hp : MeasurablePolicy pol) (A : U → Finset (Prefix n)) (hA : MeasurableTest A)
    (d q r : Fin m → ℝ) (hd : ∀ i, 0 ≤ d i ∧ d i ≤ 1/2)
    (hq : ∀ i, 0 < q i ∧ q i < 1) (hr : ∀ i, 0 < r i ∧ r i < 1) :
    klB (randomizedAcceptance μ pol d q A) (randomizedAcceptance μ pol d r A) ≤
      ∫ u, klFT (transcriptLaw (n:=n) (pol u) d q) (transcriptLaw (pol u) d r) ∂μ := by
  classical
  let P := fun u => ∑ ω ∈ A u, transcriptLaw (pol u) d q ω
  let Q := fun u => ∑ ω ∈ A u, transcriptLaw (pol u) d r ω
  have htP u := transcript_law_total m n (pol u) d q hd (fun i => ⟨(hq i).1.le,(hq i).2.le⟩)
  have htQ u := transcript_law_total m n (pol u) d r hd (fun i => ⟨(hr i).1.le,(hr i).2.le⟩)
  have hsupp (u : U) (ω : Prefix n) := (transcriptLaw_support (pol u) d q r hd hq hr ω).mpr
  have hP u : 0 ≤ P u := Finset.sum_nonneg (fun ω _ => (htP u).1 ω)
  have hQ u : 0 ≤ Q u := Finset.sum_nonneg (fun ω _ => (htQ u).1 ω)
  have hP1 u : P u ≤ 1 := (Finset.sum_le_univ_sum_of_nonneg (htP u).1).trans_eq (htP u).2
  have hQ1 u : Q u ≤ 1 := (Finset.sum_le_univ_sum_of_nonneg (htQ u).1).trans_eq (htQ u).2
  have hPQ u : Q u = 0 → P u = 0 := sum_support _ _ (A u) (htQ u).1 (hsupp u)
  have hcP u : 1-P u = ∑ ω ∈ (A u)ᶜ, transcriptLaw (pol u) d q ω := by
    have hs := Finset.sum_add_sum_compl (A u) (transcriptLaw (n:=n) (pol u) d q)
    rw [(htP u).2] at hs
    dsimp [P]
    linarith
  have hcQ u : 1-Q u = ∑ ω ∈ (A u)ᶜ, transcriptLaw (pol u) d r ω := by
    have hs := Finset.sum_add_sum_compl (A u) (transcriptLaw (n:=n) (pol u) d r)
    rw [(htQ u).2] at hs
    dsimp [Q]
    linarith
  have hcPQ u : 1-Q u = 0 → 1-P u = 0 := by
    rw [hcP u, hcQ u]
    exact sum_support _ _ (A u)ᶜ (htQ u).1 (hsupp u)
  have hPi : Integrable P μ := integrable_acceptance μ pol hp A hA d q
  have hQi : Integrable Q μ := integrable_acceptance μ pol hp A hA d r
  have hK1 : Integrable (fun u => P u * Real.log (P u / Q u)) μ :=
    integrable_acceptance_function μ pol hp A hA d q r (fun x y => x * Real.log (x/y))
  have hK0 : Integrable (fun u => (1-P u) * Real.log ((1-P u)/(1-Q u))) μ :=
    integrable_acceptance_function μ pol hp A hA d q r (fun x y => (1-x) * Real.log ((1-x)/(1-y)))
  have hfirst := integral_log_sum μ P Q hP hQ hPi hQi hPQ hK1
  have hsecond := integral_log_sum μ (fun u => 1-P u) (fun u => 1-Q u)
    (fun u => sub_nonneg.mpr (hP1 u)) (fun u => sub_nonneg.mpr (hQ1 u))
    ((integrable_const 1).sub hPi) ((integrable_const 1).sub hQi) hcPQ hK0
  have hcompP : (∫ u, 1-P u ∂μ) = 1-∫ u, P u ∂μ := by rw [integral_sub (integrable_const 1) hPi]; simp
  have hcompQ : (∫ u, 1-Q u ∂μ) = 1-∫ u, Q u ∂μ := by rw [integral_sub (integrable_const 1) hQi]; simp
  rw [hcompP, hcompQ] at hsecond
  have hbinary : klB (∫ u, P u ∂μ) (∫ u, Q u ∂μ) ≤ ∫ u, klB (P u) (Q u) ∂μ := by
    unfold klB
    rw [integral_add hK1 hK0]
    exact add_le_add hfirst hsecond
  have hdata u : klB (P u) (Q u) ≤ klFT (transcriptLaw (n:=n) (pol u) d q)
      (transcriptLaw (pol u) d r) :=
    kl_data_processing_finite (Prefix n) _ _ (A u) (htP u).1 (htQ u).1 (hsupp u) (htP u).2 (htQ u).2
  exact hbinary.trans (integral_mono
    (integrable_acceptance_function μ pol hp A hA d q r klB)
    (integrable_conditional_kl (n:=n) μ pol hp d q r) hdata)

theorem randomized_testing_bound : RandomizedTestingStatement := by
  intro U _ μ _ m n pol d η h δ A hp hA hh hd hη hdη hδ hδhalf hPA hQA
  have hd0 i : 0 ≤ d i ∧ d i ≤ 1/2 := ⟨(hd i).1.le,(hd i).2⟩
  have hq i : 0 < (1/2:ℝ)+η i ∧ (1/2:ℝ)+η i < 1 := by constructor <;> linarith [(hη i).1,(hη i).2]
  have hr i : 0 < (1/2:ℝ)-η i ∧ (1/2:ℝ)-η i < 1 := by constructor <;> linarith [(hη i).1,(hη i).2]
  have hP u := transcript_law_total m n (pol u) d (fun i => 1/2+η i) hd0 (fun i => ⟨(hq i).1.le,(hq i).2.le⟩)
  have hQ u := transcript_law_total m n (pol u) d (fun i => 1/2-η i) hd0 (fun i => ⟨(hr i).1.le,(hr i).2.le⟩)
  have hP0 u : 0 ≤ ∑ ω ∈ A u, transcriptLaw (pol u) d (fun i => 1/2+η i) ω :=
    Finset.sum_nonneg (fun ω _ => (hP u).1 ω)
  have hQ0 u : 0 ≤ ∑ ω ∈ A u, transcriptLaw (pol u) d (fun i => 1/2-η i) ω :=
    Finset.sum_nonneg (fun ω _ => (hQ u).1 ω)
  have hPle u : (∑ ω ∈ A u, transcriptLaw (pol u) d (fun i => 1/2+η i) ω) ≤ 1 :=
    (Finset.sum_le_univ_sum_of_nonneg (hP u).1).trans_eq (hP u).2
  have hPAnn : 0 ≤ randomizedAcceptance μ pol d (fun i => 1/2+η i) A := integral_nonneg hP0
  have hPAle : randomizedAcceptance μ pol d (fun i => 1/2+η i) A ≤ 1 := by
    have hb := integral_mono (integrable_acceptance μ pol hp A hA d _) (integrable_const 1) hPle
    simpa [randomizedAcceptance] using hb
  have hQApos : 0 < randomizedAcceptance μ pol d (fun i => 1/2-η i) A := by
    by_contra hn
    have hzero : randomizedAcceptance μ pol d (fun i => 1/2-η i) A = 0 :=
      le_antisymm (not_lt.mp hn) (integral_nonneg hQ0)
    have hz := integral_support μ _ _ hP0 hQ0
      (integrable_acceptance μ pol hp A hA d _) (integrable_acceptance μ pol hp A hA d _)
      (fun u => sum_support _ _ (A u) (hQ u).1
        (fun ω => (transcriptLaw_support (pol u) d _ _ hd0 hq hr ω).mpr)) hzero
    change randomizedAcceptance μ pol d (fun i => 1/2+η i) A = 0 at hz
    linarith
  have htest := Tier2Information.kl_test_separation δ _ _ hδ hδhalf hPAnn hPAle hQApos hQA hPA
  exact htest.trans ((randomized_test_data_processing μ pol hp A hA d _ _ hd0 hq hr).trans
    (randomized_information_bound U μ m n pol d η h hp hh hd hη hdη))

end ThresholdHC.Tier3
