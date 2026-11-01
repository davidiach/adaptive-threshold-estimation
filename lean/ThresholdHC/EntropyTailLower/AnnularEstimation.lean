import ThresholdHC.EntropyTailLower.AnnularWork
import ThresholdHC.EntropyTailLower.WeightedEstimation

/-! Annular hardness for an actual single-coin estimator, with arbitrary
finite gap law and band masses. The separation and moment premises remain
explicit: constructing such an estimator from a population procedure is a
separate, still missing step of the full lower bound. -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace ThresholdHC.EntropyTailLower
open ThresholdHC.CriticalEntropy

theorem annular_estimation_entropy {R : Type} [MeasurableSpace R]
    (ν : Measure R) [IsProbabilityMeasure ν] (A : StoppedProcedure R ℝ)
    (μ : Measure EntropyGap) [IsFiniteMeasure μ]
    {K : ℕ} (I : Fin K → Set EntropyGap) (b : Fin K → ℝ)
    (hb : ∀ i, 0 < b i) (hI : ∀ i, MeasurableSet (I i))
    (hdisjoint : Pairwise (fun i j => Disjoint (I i) (I j)))
    (hmass : ∀ i, 0 < μ.real (I i))
    (hband : ∀ i d, d ∈ I i → b i/2 < (d:ℝ) ∧ (d:ℝ) ≤ b i)
    (hsep : ∀ i j, j.val = i.val+1 → 4*b j ≤ b i)
    (G : Set EntropyGap) (hG : MeasurableSet G)
    (hbad : ∀ i, μ.real Gᶜ ≤ μ.real (I i)/2)
    (n : ℕ) (hn : 0 < n) (M threshold margin : ℝ) (hmargin : 0 < margin)
    (hnM : 10*M ≤ (n:ℝ)*margin^2)
    (hw : Integrable (fun d : EntropyGap =>
      (expectedStoppedProcedureWork ν (signParameter d false) A).toReal) μ)
    (hfinite : ∀ d ∈ G, ∀ s, expectedStoppedProcedureWork ν (signParameter d s) A ≠ ∞)
    (hmem : ∀ d ∈ G, ∀ s, MemLp id 2
      ((ν.prod (Tier2.tapeMeasure (signParameter d s))).map A.output))
    (hM : ∀ d ∈ G, ∀ s, (∫ x : ℝ, x^2
      ∂(ν.prod (Tier2.tapeMeasure (signParameter d s))).map A.output) ≤ M)
    (hminus : ∀ d ∈ G, (∫ x : ℝ, x
      ∂(ν.prod (Tier2.tapeMeasure (signParameter d false))).map A.output) ≤ threshold-margin)
    (hplus : ∀ d ∈ G, threshold+margin ≤ (∫ x : ℝ, x
      ∂(ν.prod (Tier2.tapeMeasure (signParameter d true))).map A.output)) :
    ThresholdHC.EntropyTailQuantile.costEntropy (fun i => μ.real (I i)/(b i)^2) ≤
      16384*(n:ℝ)*(∫ d : EntropyGap,
        (expectedStoppedProcedureWork ν (signParameter d false) A).toReal ∂μ) := by
  classical
  let w := fun d : EntropyGap => (expectedStoppedProcedureWork ν (signParameter d false) A).toReal
  have hw0 : ∀ d, 0 ≤ w d := fun _ => ENNReal.toReal_nonneg
  have hp (i : Fin K) := exists_point_below_annular_average G (I i) hG (hI i)
    (hmass i) (hbad i) w hw hw0
  choose d hd hlow using hp
  have hgap : ∀ i j, j.val = i.val+1 → 2*(d j:ℝ) ≤ (d i:ℝ) := by
    intro i j hij
    have hi := hband i (d i) (hd i).2
    have hj := hband j (d j) (hd j).2
    linarith [hsep i j hij]
  have hs := weighted_estimation_entropy ν A K d hgap n hn M threshold margin hmargin hnM
    (fun i => hfinite _ (hd i).1) (fun i => hmem _ (hd i).1)
    (fun i => hM _ (hd i).1) (fun i => hminus _ (hd i).1) (fun i => hplus _ (hd i).1)
    (fun i => μ.real (I i)/(b i)^2) (fun i => by positivity)
  have hsum := annular_work_sum μ I b hb hI hdisjoint hmass d
    (fun i => (hband i (d i) (hd i).2).2) w hw hw0 hlow
  have hscaled := mul_le_mul_of_nonneg_left hsum (by positivity : 0 ≤ 4096*(n:ℝ))
  exact hs.trans (by nlinarith)

end ThresholdHC.EntropyTailLower
